import KroneckerExchangeRepairCorrespondence

/-! Pointwise agreement with the manuscript's Recol operator and recovery code. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerExchangeColorCorrespondence
open KroneckerColoring KroneckerColoredEdges KroneckerColoredRepair
open KroneckerRightColoredChange KroneckerColoredExchangeRelation
open KroneckerExchangeTransport KroneckerCanonicalExchange

def swapSeq {α : Type} (i : ℕ) (xs : List α) : List α :=
  xs.take i ++ ((xs.drop i).take 2).reverse ++ xs.drop (i+2)

theorem swapSeq_pair {α : Type} (pre es : List α) (x y : α) :
    swapSeq pre.length (pre ++ x::y::es) = pre ++ y::x::es := by
  simp [swapSeq,List.drop_append,
    List.drop_eq_nil_of_le (by omega : pre.length ≤ pre.length+2),List.append_assoc]

@[simp] theorem swapSeq_length {α : Type} (xs : List α) (i : ℕ) :
    (swapSeq i xs).length = xs.length := by
  simp only [swapSeq,List.length_append,List.length_take,List.length_drop,List.length_reverse]
  omega

theorem swapPos_succ (i k : ℕ) : swapPos (i+1) (k+1) = swapPos i k+1 := by
  by_cases h : k = i
  · subst k; simp [swapPos]
  · by_cases h' : k = i+1
    · subst k; simp [swapPos]
    · simp [swapPos,h,h']

theorem swapSeq_get {α : Type} (xs : List α) (i k : ℕ) (hi : i+1 < xs.length) :
    (swapSeq i xs)[k]? = xs[swapPos i k]? := by
  induction xs generalizing i k with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero =>
          cases xs with
          | nil => simp at hi
          | cons b xs =>
              cases k with
              | zero => simp [swapSeq,swapPos]
              | succ k =>
                  cases k with
                  | zero => simp [swapSeq,swapPos]
                  | succ k => simp [swapSeq,swapPos]
      | succ i =>
          have he : swapSeq (i+1) (a::xs) = a::swapSeq i xs := by
            simp [swapSeq,List.take_succ_cons,List.drop_succ_cons]
          cases k with
          | zero => simp [he,swapPos]
          | succ k =>
              rw [he,List.getElem?_cons_succ,swapPos_succ,List.getElem?_cons_succ]
              exact ih i k (by simpa using hi)

def Rel {m : ℕ} (p q : CEdge m) : Prop := p.1 = q.1 ∧ RespectsRecol p.2 q.2

theorem rel_refl {m : ℕ} (es : List (CEdge m)) : List.Forall₂ Rel es es := by
  induction es with
  | nil => exact .nil
  | cons p es ih => exact .cons ⟨rfl,respects_self p.2⟩ ih

theorem repair_rel {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (hr : ColoredRepairAt j xs ys p q) : List.Forall₂ Rel xs ys := by
  induction hr with
  | here es p q hk hc => exact .cons ⟨rfl,hc⟩ (rel_refl es)
  | there e hr ih => exact .cons ⟨rfl,respects_self e.2⟩ ih

theorem exchange_rel {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) : List.Forall₂ Rel (swapSeq i xs) ys := by
  cases he with
  | right pre hc =>
      rw [swapSeq_pair]
      apply List.rel_append (rel_refl pre)
      cases hc with
      | zero q es hx hq hcol =>
          exact .cons ⟨rfl,hcol⟩ (.cons ⟨rfl,respects_self _⟩ (rel_refl _))
      | positive hx hy hi hr =>
          exact .cons ⟨rfl,respects_self _⟩ (.cons ⟨rfl,respects_self _⟩ (repair_rel hr))
  | left pre es hc =>
      rw [swapSeq_pair]
      apply List.rel_append (rel_refl pre)
      cases hc with
      | zero hx => exact .cons ⟨rfl,respects_self _⟩ (.cons ⟨rfl,respects_self _⟩ (rel_refl _))
      | positive hx => exact .cons ⟨rfl,respects_self _⟩ (.cons ⟨rfl,respects_zero _⟩ (rel_refl _))

theorem exchange_pair_bound {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) : i+1 < xs.length := by
  cases he <;> simp

theorem exchange_rel_at {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) (k : ℕ) (hk : k < ys.length) :
    ∃ a b, xs[swapPos i k]? = some a ∧ ys[k]? = some b ∧ Rel a b := by
  have hr := exchange_rel he
  have hl := hr.length_eq
  have hx : k < (swapSeq i xs).length := by omega
  refine ⟨(swapSeq i xs)[k],ys[k],?_,List.getElem?_eq_getElem hk,?_⟩
  · rw [←swapSeq_get xs i k (exchange_pair_bound he)]
    exact List.getElem?_eq_getElem hx
  · exact hr.get hx hk

theorem repair_original_palette {m j : ℕ} {xs ys : List (CEdge m)} {p q : Palette m}
    (hr : ColoredRepairAt j xs ys p q) : xs[j]? = some (false,p) := by
  induction hr with
  | here => rfl
  | there e hr ih => simpa using ih

theorem exchange_code_at {m i d : ℕ} {right : Bool} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange right i xs ys p d) :
    xs[swapPos i (repairPosition right i (coloredWord xs))]? = some (false,p) := by
  cases he with
  | right pre hc =>
      cases hc with
      | zero q es hx hq hcol =>
          simp [repairPosition,coloredWord,uncolor,paint,hx,KroneckerStack.Edge.grade,swapPos]
      | @positive y q es ds n j hx hy hi hr =>
          rename_i x y es ds
          have hp := repairPosition_right (coloredWord pre) (coloredWord es) (grade x) (grade y)
          simp only [hx,Nat.add_sub_cancel,Nat.add_eq_zero_iff,one_ne_zero,and_false,
            ite_false,hi,Option.getD_some] at hp
          have hp' : repairPosition true pre.length
              (coloredWord (pre++(true,x)::(false,y)::es)) = pre.length+2+j := by
            simpa [coloredWord,uncolor,paint,hx] using hp
          rw [hp']
          simp only [swapPos,ite_eq_right (by omega : pre.length+2+j ≠ pre.length),
            ite_eq_right (by omega : pre.length+2+j ≠ pre.length+1)]
          rw [List.getElem?_append_right (by omega),
            show pre.length+2+j-pre.length = j+1+1 by omega]
          simpa using repair_original_palette hr
  | left pre es hc => simp [repairPosition,swapPos]


open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerAdjacentExchangeLemma
open KroneckerManuscriptExchangeDefinitions KroneckerExchangeRepairCorrespondence
open KroneckerWrappedExchangeWitness KroneckerWrappedExchangeMap KroneckerEdgeShell

theorem geometric_relation (ξ : AdjShellExch) (a : ColoredSet ξ.X) :
    Exchange ξ.right ξ.r (edges (shell ξ.spec a.2.val)) (edges (ξ.exchange a).2.val)
      (chosen ξ.spec (operational ξ.X a)).code (chosen ξ.spec (operational ξ.X a)).delta := by
  have hc := exchange_context (chosen ξ.spec (operational ξ.X a)).exchange
    (edgePrefix 3 ξ.spec.u ξ.spec.hu) (edgeSuffix 3 ξ.spec.v ξ.spec.hv ξ.spec.hm)
  have hp : (edgePrefix 3 ξ.spec.u ξ.spec.hu).length+(ξ.spec.P.length+1) = ξ.r := by
    simp [edgePrefix,AdjShellExch.spec,KroneckerAdjacentExchangeLemma.spec,AdjShellExch.r]
    omega
  rw [hp] at hc
  simp only [List.append_assoc] at hc
  have ho := exchangeMap_edges ξ.spec (operational (source ξ.spec ξ.origin) a)
  rw [←exchange_core ξ.spec ξ.origin a] at ho
  change edges (ξ.exchange a).2.val = edgeShell ξ.spec.u ξ.spec.v ξ.spec.hu ξ.spec.hv ξ.spec.hm
    (chosen ξ.spec (operational ξ.X a)).middle at ho
  rw [ho,shell_edges]
  exact hc

def palette {P : TNEPath} (a : ColoredGrading 3 P) (k : Edge P) : Palette 3 :=
  KroneckerPaperPathGradings.paletteEncoding (coloredGradingEquiv 3 P a) k

theorem edges_get {P : TNEPath} (a : ColoredGrading 3 P) (k : Edge P) :
    (edges a)[k.val]? = some (P.steps[k.val],palette a k) := by
  simp [edges,KroneckerPaperPathGradings.coloredEdges,
    KroneckerColoredEdgeDictionary.ofColoring,palette,k.isLt]

theorem palette_grade {P : TNEPath} (a : ColoredGrading 3 P) (k : Edge P) :
    grade (palette a k) = a.1 (edgeEquiv P k) := rfl

theorem palette_color {P : TNEPath} (a : ColoredGrading 3 P) (k : Edge P) :
    (palette a k).2.val+1 = (a.2 (edgeEquiv P k)).val := by
  have h := congrArg (fun t : GradeColor => t.2.val) (geometric_pair a k)
  exact h

theorem geometric_recol_at (ξ : AdjShellExch) (a : ColoredSet ξ.X) (k : Edge ξ.Y') :
    RespectsRecol (palette (shell ξ.spec a.2.val) ((shellPair ξ).indices.symm k))
      (palette (ξ.exchange a).2.val k) := by
  have hk : k.val < (edges (ξ.exchange a).2.val).length := by
    simp only [edges,KroneckerPaperPathGradings.coloredEdges,
      KroneckerColoredEdgeDictionary.ofColoring,List.length_zip,List.length_ofFn,Nat.min_self]
    exact k.isLt
  obtain ⟨x,y,hx,hy,hr⟩ := exchange_rel_at (geometric_relation ξ a) k.val hk
  have hs := edges_get (shell ξ.spec a.2.val) ((shellPair ξ).indices.symm k)
  have ht := edges_get (ξ.exchange a).2.val k
  have hi : ((shellPair ξ).indices.symm k).val = swapPos ξ.r k.val := by
    change swapPos (shellPair ξ).pre.length k.val = _
    rw [shell_pair_position]
  rw [←hi] at hx
  rw [hs] at hx
  rw [ht] at hy
  cases hx
  cases hy
  exact hr.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem color_rule (ξ : AdjShellExch) (a : ColoredSet ξ.X) (k : Edge ξ.Y') :
    ((ξ.exchange a).2.val.2 (edgeEquiv ξ.Y' k)).val =
      if (ξ.exchange a).2.val.1 (edgeEquiv ξ.Y' k) =
          (shell ξ.spec a.2.val).1 (edgeEquiv ξ.Y ((shellPair ξ).indices.symm k)) then
        ((shell ξ.spec a.2.val).2 (edgeEquiv ξ.Y ((shellPair ξ).indices.symm k))).val
      else 1 := by
  have hr := geometric_recol_at ξ a k
  by_cases h : (ξ.exchange a).2.val.1 (edgeEquiv ξ.Y' k) =
      (shell ξ.spec a.2.val).1 (edgeEquiv ξ.Y ((shellPair ξ).indices.symm k))
  · rw [ite_eq_left h]
    have hg : grade (palette (ξ.exchange a).2.val k) =
        grade (palette (shell ξ.spec a.2.val) ((shellPair ξ).indices.symm k)) := by
      simp only [palette_grade]
      exact h
    have hc := congrArg (fun p : Palette 3 => p.2.val+1) (hr.1 hg)
    simp only [palette_color] at hc
    exact hc
  · rw [ite_eq_right h,←palette_color]
    have hg : grade (palette (ξ.exchange a).2.val k) ≠
        grade (palette (shell ξ.spec a.2.val) ((shellPair ξ).indices.symm k)) := by
      simp only [palette_grade]
      exact h
    rw [hr.2 hg]

def copy (ξ : AdjShellExch) : (Set.univ : Set (GeomEdge ξ.Y)) ↪ GeomEdge ξ.Y' :=
  KroneckerManuscriptRecolorMaps.edgeCopy (shellPair ξ).indices.toEmbedding

theorem copy_eq_tau (ξ : AdjShellExch) (e : (Set.univ : Set (GeomEdge ξ.Y))) :
    copy ξ e = tau ξ e.val := rfl

/-- A pointwise color rule determines Recol along a bijection. -/
theorem recol_from_rule {U V : TNEPath} (e : Edge U ≃ Edge V)
    (src : ColoredGrading 3 U) (out : ColoredGrading 3 V)
    (hr : ∀ k : Edge V, (out.2 (edgeEquiv V k)).val =
      if out.1 (edgeEquiv V k) = src.1 (edgeEquiv U (e.symm k)) then
        (src.2 (edgeEquiv U (e.symm k))).val else 1) :
    out.2 = Recol U V (KroneckerManuscriptRecolorMaps.edgeCopy e.toEmbedding)
      out.1 (color_grade_le out.2) src.1 src.2 := by
  funext v
  apply Subtype.ext
  obtain ⟨k,rfl⟩ := (edgeEquiv V).surjective v
  let x : (Set.univ : Set (GeomEdge U)) := ⟨edgeEquiv U (e.symm k),Set.mem_univ _⟩
  let cp := KroneckerManuscriptRecolorMaps.edgeCopy e.toEmbedding
  have hx : cp x = edgeEquiv V k := by
    simp [cp,KroneckerManuscriptRecolorMaps.edgeCopy,x]
  rw [hr k]
  by_cases h : out.1 (edgeEquiv V k) = src.1 (edgeEquiv U (e.symm k))
  · rw [ite_eq_left h]
    have hc := Recol_preserved cp out.1 (color_grade_le out.2) src.1 src.2 x (by rw [hx]; exact h)
    rw [hx] at hc
    exact hc.symm
  · rw [ite_eq_right h]
    have hc := Recol_changed cp out.1 (color_grade_le out.2) src.1 src.2 x (by rw [hx]; exact h)
    rw [hx] at hc
    exact hc.symm

/-- The color projection of the actual exchange is precisely Recol along τ. -/
theorem exchange_colors_eq_Recol (ξ : AdjShellExch) (a : ColoredSet ξ.X) :
    (ξ.exchange a).2.val.2 = Recol ξ.Y ξ.Y' (copy ξ) (ξ.exchange a).2.val.1
      (color_grade_le (ξ.exchange a).2.val.2)
      (shell ξ.spec a.2.val).1 (shell ξ.spec a.2.val).2 :=
  recol_from_rule (shellPair ξ).indices (shell ξ.spec a.2.val) (ξ.exchange a).2.val
    (color_rule ξ a)

/-- Both projections of the actual colored map agree with the manuscript. -/
theorem exchange_exact (ξ : AdjShellExch) (a : ColoredSet ξ.X) :
    (ξ.exchange a).2.val.1 = RepGr ξ a.2.val.1 ∧
    (ξ.exchange a).2.val.2 = Recol ξ.Y ξ.Y' (copy ξ) (ξ.exchange a).2.val.1
      (color_grade_le (ξ.exchange a).2.val.2)
      (shell ξ.spec a.2.val).1 (shell ξ.spec a.2.val).2 :=
  ⟨exchange_eq_RepGr ξ a,exchange_colors_eq_Recol ξ a⟩

end KroneckerExchangeColorCorrespondence

#print axioms KroneckerExchangeColorCorrespondence.copy_eq_tau
#print axioms KroneckerExchangeColorCorrespondence.exchange_colors_eq_Recol
#print axioms KroneckerExchangeColorCorrespondence.exchange_exact
