import KroneckerManuscriptShadowNodes

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace KroneckerCompatibility
open KroneckerStack KroneckerSourceHorizontalShadow KroneckerSourceCompatibility

theorem root_iff_source_first {E F : ℕ → Edge} {a l : ℕ} (hl : 0 < l)
    (h : ∀ k, k < l → F k = E (a+k)) :
    RootComponent F l ↔ PositiveH E a ∧ FirstClosure E a (a+l-1) := by
  have hw (k : ℕ) (hk : k ≤ l) : debt F k = debt E (a+k)-debt E a :=
    walk_subpath h Edge.debtChange k hk
  have hzero : F 0 = E a := by simpa using h 0 hl
  have hend : a+l-1+1=a+l := by omega
  constructor
  · intro hr
    have hv := (root_iff_first_vertical_return F l).mp hr
    refine ⟨by simpa only [PositiveH,hzero] using hr.2.1,by omega,?_,?_,?_⟩
    · simpa only [Vertical,h (l-1) (by omega),show a+(l-1)=a+l-1 by omega] using hv.2.2.1
    · rw [hEquality_iff_debt E a (a+l-1) (by omega),hend]
      have hz := hw l le_rfl
      have hrz := hr.2.2.1
      omega
    · intro e hae hel heV heq
      have heq' := (hEquality_iff_debt E a e (by omega)).mp heq
      have hk : 0 < e-a+1 := by omega
      have hkl : e-a+1 < l := by omega
      have hpos := hr.2.2.2 (e-a+1) hk hkl
      have hd := hw (e-a+1) hkl.le
      rw [show a+(e-a+1)=e+1 by omega] at hd
      omega
  · rintro ⟨hu,hc⟩
    obtain ⟨he,hpre⟩ := first_return_debt hu hc
    rw [hend] at he
    apply (root_iff_first_return F l).mpr
    refine ⟨hl,by simpa only [PositiveH,hzero] using hu,?_,?_⟩
    · rw [hw l le_rfl,he,sub_self]
    · intro k hk hkl
      have hn := hpre (a+k) (by omega) (by omega)
      rw [hw k hkl.le]
      exact sub_ne_zero.mpr hn

end KroneckerCompatibility

namespace KroneckerPaperPaths

theorem cyclicSubpath_mem_iff (P : TNEPath) (u v : Edge P) (w : GeomEdge P) :
    w ∈ (CyclicSubpath.mk u v).edges ↔
      cyclicLength u ((edgeEquiv P).symm w) ≤ cyclicLength u v := by
  change w ∈ List.ofFn (fun k => edgeEquiv P (cyclicIndex u v k)) ↔ _
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨k,hk⟩
    have hi := congrArg (fun z => ((edgeEquiv P).symm z).val) hk
    simp only [Equiv.symm_apply_apply] at hi
    rw [cyclicIndex_val] at hi
    have hkn : k.val < P.steps.length := lt_of_lt_of_le k.isLt (cyclicLength_le u v)
    have hlpos := cyclicLength_pos u ((edgeEquiv P).symm w)
    have hlle := cyclicLength_le u ((edgeEquiv P).symm w)
    have hlast := congrArg Fin.val (cyclicIndex_last u ((edgeEquiv P).symm w))
    rw [cyclicIndex_val] at hlast
    dsimp only at hlast
    have he : k.val = cyclicLength u ((edgeEquiv P).symm w)-1 := by
      split_ifs at hi hlast <;> omega
    have hklt := k.isLt
    omega
  · intro h
    let k : Fin (cyclicLength u v) :=
      ⟨cyclicLength u ((edgeEquiv P).symm w)-1,by
        have := cyclicLength_pos u ((edgeEquiv P).symm w)
        omega⟩
    refine ⟨k,?_⟩
    have he : cyclicIndex u v k = cyclicIndex u ((edgeEquiv P).symm w)
        ⟨cyclicLength u ((edgeEquiv P).symm w)-1,by
          have := cyclicLength_pos u ((edgeEquiv P).symm w); omega⟩ := by
      apply Fin.ext
      simp only [cyclicIndex_val]
      rfl
    rw [he,cyclicIndex_last,Equiv.apply_symm_apply]

end KroneckerPaperPaths

namespace KroneckerPaperPathGradings
open KroneckerPaperPaths KroneckerCompatibility KroneckerSourceHorizontalShadow
open KroneckerSourceCompatibility

theorem firstShadow_source_first {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) :
    FirstShadow g u v ↔ PositiveH (geometricTrace g) u.val ∧
      FirstClosure (geometricTrace g) u.val (lift P.steps.length u.val v.val) := by
  have hc : ∀ k, k < cyclicLength u v →
      geometricTrace (cyclicGrading g u v) k = geometricTrace g (u.val+k) := by
    intro k hk
    exact cyclicTrace_correspondence g u v ⟨k,by simpa using hk⟩
  rw [firstShadow_iff_root,root_iff_source_first (cyclicLength_pos u v) hc]
  have he : u.val+cyclicLength u v-1 = lift P.steps.length u.val v.val := by
    have := cyclicLength_lift u v
    omega
  rw [he]

theorem horizontalShadow_source {m : ℕ} {P : TNEPath} (g : Grading m P) (u : Edge P)
    (hu : PositiveH (geometricTrace g) u.val) (w : GeomEdge P)
    (hw : P.steps.get ((edgeEquiv P).symm w) = false) :
    w ∈ horizontalShadow g u ↔
      Shadow (geometricTrace g) u.val
        (lift P.steps.length u.val ((edgeEquiv P).symm w).val) := by
  let t := lift P.steps.length u.val ((edgeEquiv P).symm w).val
  have ht : u.val ≤ t ∧ t < u.val+P.steps.length := by
    have hu' := u.isLt
    have hw' := ((edgeEquiv P).symm w).isLt
    unfold t lift
    split_ifs <;> omega
  by_cases h : ∃ v, FirstShadow g u v
  · simp only [horizontalShadow,h,↓reduceIte,Set.mem_ofPred_eq,hw,true_and]
    constructor
    · rintro ⟨v,hv,hwv⟩
      have hc := ((firstShadow_source_first g u v).mp hv).2
      have hlen := (cyclicSubpath_mem_iff P u v w).mp hwv
      have hle : t ≤ lift P.steps.length u.val v.val := by
        have h1 := cyclicLength_lift u ((edgeEquiv P).symm w)
        have h2 := cyclicLength_lift u v
        dsimp [t]
        omega
      intro e hue het heV
      exact hc.2.2.2 e hue (het.trans_le hle) heV
    · intro hs
      obtain ⟨v,hv⟩ := h
      have hc := ((firstShadow_source_first g u v).mp hv).2
      have hle : t ≤ lift P.steps.length u.val v.val := by
        by_contra hn
        exact beyond_first_not_shadow hc (by omega) hs
      refine ⟨v,hv,(cyclicSubpath_mem_iff P u v w).mpr ?_⟩
      have h1 := cyclicLength_lift u ((edgeEquiv P).symm w)
      have h2 := cyclicLength_lift u v
      dsimp [t] at hle
      omega
  · simp only [horizontalShadow,h,↓reduceIte,Set.mem_ofPred_eq,hw,true_iff]
    intro e hue het heV heq
    let H : ∃ e, u.val ≤ e ∧ e < u.val+P.steps.length ∧
        KroneckerCompatibility.Vertical (geometricTrace g) e ∧
        HEquality (geometricTrace g) u.val e :=
      ⟨e,hue,het.trans ht.2,heV,heq⟩
    let f := Nat.find H
    have hf := Nat.find_spec H
    have hc : FirstClosure (geometricTrace g) u.val f := by
      refine ⟨hf.1,hf.2.2.1,hf.2.2.2,?_⟩
      intro z huz hzf hzV hzq
      exact Nat.find_min H hzf ⟨huz,hzf.trans hf.2.1,hzV,hzq⟩
    let v : Edge P := ⟨if f < P.steps.length then f else f-P.steps.length,by
      have hu' := u.isLt
      have hf' : f < u.val+P.steps.length := hf.2.1
      split_ifs <;> omega⟩
    have he : lift P.steps.length u.val v.val=f := by
      have hu' := u.isLt
      have hf0 : u.val ≤ f := hf.1
      have hf1 : f < u.val+P.steps.length := hf.2.1
      simp only [v,lift]
      split_ifs <;> omega
    exact h ⟨v,(firstShadow_source_first g u v).mpr ⟨hu,he.symm ▸ hc⟩⟩


theorem positiveH_edge {m : ℕ} {P : TNEPath} (g : Grading m P) (k : Edge P) :
    PositiveH (geometricTrace g) k.val ↔ P.steps.get k = true ∧
      0 < (g (edgeEquiv P k)).val := by
  unfold PositiveH
  rw [geometricTrace_edge]
  cases P.steps.get k <;> simp

theorem positiveV_edge {m : ℕ} {P : TNEPath} (g : Grading m P) (k : Edge P) :
    PositiveV (geometricTrace g) k.val ↔ P.steps.get k = false ∧
      0 < (g (edgeEquiv P k)).val := by
  unfold PositiveV
  rw [geometricTrace_edge]
  cases P.steps.get k <;> simp

theorem tight_iff_source_support {m : ℕ} {P : TNEPath} (g : Grading m P) :
    Tight g ↔ Compatible g ∧ Support (geometricTrace g) P.steps.length := by
  constructor
  · rintro ⟨hc,ht⟩
    refine ⟨hc,?_⟩
    intro k hk hkp
    let v : Edge P := ⟨k,hk⟩
    have hv := (positiveV_edge g v).mp hkp
    let w : Vertical P := ⟨edgeEquiv P v,by simpa only [Equiv.symm_apply_apply] using hv.1⟩
    obtain ⟨x,hx,hs⟩ := ht w hv.2
    let u : Edge P := (edgeEquiv P).symm x.val
    have hup : PositiveH (geometricTrace g) u.val :=
      (positiveH_edge g u).mpr ⟨x.property,by simpa only [u,Equiv.apply_symm_apply] using hx⟩
    refine ⟨u.val,u.isLt,hup,?_⟩
    have hz := (horizontalShadow_source g u hup w.val w.property).mp hs
    simpa only [w,v,Equiv.symm_apply_apply] using hz
  · rintro ⟨hc,ht⟩
    refine ⟨hc,?_⟩
    intro w hg
    let v : Edge P := (edgeEquiv P).symm w.val
    have hvp : PositiveV (geometricTrace g) v.val :=
      (positiveV_edge g v).mpr ⟨w.property,by simpa only [v,Equiv.apply_symm_apply] using hg⟩
    obtain ⟨k,hk,hkp,hs⟩ := ht v.val v.isLt hvp
    let u : Edge P := ⟨k,hk⟩
    have hu := (positiveH_edge g u).mp hkp
    let z : Horizontal P := ⟨edgeEquiv P u,by simpa only [Equiv.symm_apply_apply] using hu.1⟩
    refine ⟨z,hu.2,?_⟩
    change w.val ∈ horizontalShadow g ((edgeEquiv P).symm (edgeEquiv P u))
    rw [Equiv.symm_apply_apply]
    exact (horizontalShadow_source g u hkp w.val w.property).mpr hs

def TightAtTotals {m : ℕ} {P : TNEPath} (a b : ℤ) (g : Grading m P) : Prop :=
  Tight g ∧ KroneckerSourceIntervalCounts.hWeight (geometricTrace g) 0 P.steps.length = b ∧
    KroneckerSourceIntervalCounts.vWeight (geometricTrace g) 0 P.steps.length = a

theorem tightAtTotals_iff_source {m : ℕ} {P : TNEPath} (a b : ℤ) (g : Grading m P) :
    TightAtTotals a b g ↔ KroneckerSourceGradingDictionary.SourceTight
      (KroneckerWordCounts.pathShape P.steps) a b (gradingEquiv m P g) := by
  simp only [TightAtTotals,tight_iff_source_support,compatible_iff_source,
    KroneckerSourceGradingDictionary.SourceTight,geometricTrace]
  tauto

end KroneckerPaperPathGradings
#print axioms KroneckerPaperPathGradings.horizontalShadow_source

#print axioms KroneckerPaperPathGradings.tightAtTotals_iff_source
