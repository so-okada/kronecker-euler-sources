import KroneckerAmbientCyclicWitnesses
import KroneckerNodeRestrictionGeometry

/-! Definition 2.19 and Lemma 2.24 after separating ambient cyclic edge sets from
NEReal. These bridges use the existing verified shadow theorems. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerPaperPathGradings
open KroneckerPaperPaths KroneckerCompatibility

/-- First vertical equality in cyclic order, using ambient edge sets. -/
def AmbientFirstShadow {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) : Prop :=
  P.steps.get u = true ∧ 0 < (g (edgeEquiv P u)).val ∧ P.steps.get v = false ∧
  ((cyclicN P u v).card : ℤ) = ∑ w ∈ cyclicE P u v, ((g w).val : ℤ) ∧
  ∀ k : Fin (cyclicLength u v), k.val+1 < cyclicLength u v →
    P.steps.get (cyclicIndex u v k) = false →
    ((cyclicN P u (cyclicIndex u v k)).card : ℤ) ≠
      ∑ w ∈ cyclicE P u (cyclicIndex u v k), ((g w).val : ℤ)

theorem ambientFirstShadow_iff {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) : AmbientFirstShadow g u v ↔ FirstShadow g u v := by
  rw [firstShadow_iff_first_vertical_equality]
  have hzero := cyclicTrace_at g u v 0 (cyclicLength_pos u v)
  simp only [Nat.add_zero] at hzero
  have hpos : PositiveH (geometricTrace (NERealGrading g u v)) 0 ↔
      P.steps.get u = true ∧ 0 < (g (edgeEquiv P u)).val := by
    simp only [PositiveH, hzero]
    exact positiveH_geometric g u
  let last : Fin (cyclicLength u v) := ⟨cyclicLength u v-1,by have := cyclicLength_pos u v; omega⟩
  have hlast : KroneckerCompatibility.Vertical (geometricTrace (NERealGrading g u v))
      (cyclicLength u v-1) ↔ P.steps.get v = false := by
    simpa only [last, cyclicIndex_last] using vertical_cyclic_index g u v last
  change AmbientFirstShadow g u v ↔ _ ∧ _ ∧ _ ∧ _
  rw [hpos,hlast,cyclic_east_grade,cyclic_north_count]
  constructor
  · rintro ⟨hu,hg,hv,he,hfirst⟩
    refine ⟨⟨hu,hg⟩,hv,he.symm,?_⟩
    intro n hn hnl hV hEq
    let K : Fin (cyclicLength u v) := ⟨n-1,by omega⟩
    have hKn : K.val+1 = n := by dsimp [K]; omega
    have hd := (vertical_cyclic_index g u v K).mp hV
    apply hfirst K (by omega) hd
    have he' := hEq
    rw [← hKn, cyclic_prefix_sum, cyclic_prefix_sum, cyclic_east_grade, cyclic_north_count] at he'
    exact he'.symm
  · rintro ⟨⟨hu,hg⟩,hv,he,hfirst⟩
    refine ⟨hu,hg,hv,he.symm,?_⟩
    intro K hK hV hEq
    apply hfirst (K.val+1) (by omega) hK
      (by simpa using (vertical_cyclic_index g u v K).mpr hV)
    rw [cyclic_prefix_sum, cyclic_prefix_sum, cyclic_east_grade, cyclic_north_count]
    exact hEq.symm

private theorem same_start_sum {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v w : Edge P) (n : ℕ) (hnv : n ≤ cyclicLength u v) (hnw : n ≤ cyclicLength u w)
    (f : KroneckerStack.Edge → ℤ) :
    intervalSum f (geometricTrace (NERealGrading g u v)) 0 n =
      intervalSum f (geometricTrace (NERealGrading g u w)) 0 n := by
  unfold intervalSum
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [Nat.zero_add, cyclicTrace_at g u v k (by omega), cyclicTrace_at g u w k (by omega)]

/-- The first closing edge is unique in the ambient path. -/
theorem firstShadow_endpoint_unique {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v w : Edge P) (hv : FirstShadow g u v) (hw : FirstShadow g u w) : v = w := by
  have hlen : cyclicLength u v = cyclicLength u w := by
    rcases lt_trichotomy (cyclicLength u v) (cyclicLength u w) with h | h | h
    · exfalso
      apply hw.2.2 (cyclicLength u v) (cyclicLength_pos u v) h
      rw [← same_start_sum g u v w _ le_rfl h.le hGrade,
        ← same_start_sum g u v w _ le_rfl h.le vCount]
      exact hv.2.1
    · exact h
    · exfalso
      apply hv.2.2 (cyclicLength u w) (cyclicLength_pos u w) h
      rw [← same_start_sum g u w v _ le_rfl h.le hGrade,
        ← same_start_sum g u w v _ le_rfl h.le vCount]
      exact hw.2.1
  apply Fin.ext
  have hu' := u.isLt
  have hv' := v.isLt
  have hw' := w.isLt
  unfold cyclicLength at hlen
  split_ifs at hlen <;> omega

/-- A closing horizontal shadow is precisely the ambient vertical edge set. -/
theorem horizontalShadow_eq_cyclicN {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hv : FirstShadow g u v) :
    horizontalShadow g u = (cyclicN P u v : Set (GeomEdge P)) := by
  classical
  ext w
  simp only [horizontalShadow, show (∃ v, FirstShadow g u v) from ⟨v,hv⟩, ite_true,
    Set.mem_ofPred_eq, cyclicN, CyclicSubpath.N, Finset.mem_coe, Finset.mem_filter,
    CyclicSubpath.NE, List.mem_toFinset]
  constructor
  · rintro ⟨hdir,t,ht,hm⟩
    have he := firstShadow_endpoint_unique g u t v ht hv
    subst t
    exact ⟨hm,hdir⟩
  · rintro ⟨hm,hdir⟩
    exact ⟨hdir,v,hv,hm⟩

/-- Lemma 2.24(3)(b), using the transported grading on NEReal. -/
theorem NEReal_shadow_connected {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hs : AmbientFirstShadow g u v) (hc : AmbientCompatible g) :
    ConnectedGrading (NERealGrading g u v) := by
  have h := firstShadow_compatible_restriction g u v
    ((ambientFirstShadow_iff g u v).mp hs) ((ambientCompatible_iff g).mp hc)
  simpa only [ConnectedGrading, NERealGrading, cyclicRealization_length] using h

/-- The surplus of the connected component is computed on its realization. -/
theorem NEReal_shadow_surp_nonnegative {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hs : AmbientFirstShadow g u v) (hc : AmbientCompatible g) :
    0 ≤ Surp (NEReal P u v) (NERealGrading g u v) :=
  connectedGrading_surp_nonnegative (NEReal_shadow_connected g u v hs hc)

/-- The component formula used in Proposition 2.26, with ambient names and the
transported grading on the separate NE realization. -/
theorem NEReal_surp_formula {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) :
    Surp (NEReal P u v) (NERealGrading g u v) =
      ((cyclicE P u v).card : ℤ)-1-∑ w ∈ cyclicN P u v, ((g w).val : ℤ) := by
  unfold Surp surplus
  rw [boundaryBalance_formula]
  change intervalSum hCount (geometricTrace (NERealGrading g u v)) 0
      (NEReal P u v).steps.length -
    intervalSum vGrade (geometricTrace (NERealGrading g u v)) 0
      (NEReal P u v).steps.length - 1 = _
  rw [cyclicRealization_length,cyclic_east_count,cyclic_north_grade]
  omega

/-- Lemma 2.24(2): witnesses on NEReal are equivalent to its node balance
condition for its valid h-precursor. -/
theorem NEReal_shadow_balance_iff {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hs : AmbientFirstShadow g u v)
    (p : Fin (cyclicLength u v) → Fin (cyclicLength u v))
    (hp : KroneckerPredecessor.ValidThrough
      (KroneckerPaperTraceBridge.sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v))
      p (cyclicLength u v)) :
    AmbientCompatible (NERealGrading g u v) ↔ KroneckerPredecessor.OwnedBalance
      (KroneckerPaperTraceBridge.sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v)) p := by
  rw [ambientCompatible_iff]
  exact firstShadow_ownedBalance g u v ((ambientFirstShadow_iff g u v).mp hs) p hp

/-- Lemma 2.24(3)(a), after transporting the grading to NEReal. -/
theorem NEReal_shadow_zero_extension {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hs : AmbientFirstShadow g u v)
    (hz : ∀ k, cyclicLength u v ≤ k → k < P.steps.length →
      (geometricTrace g (u.val+k)).grade = 0) :
    AmbientCompatible g ↔ ConnectedGrading (NERealGrading g u v) := by
  rw [ambientCompatible_iff]
  simpa only [ConnectedGrading, NERealGrading, cyclicRealization_length] using
    firstShadow_zero_extension g u v ((ambientFirstShadow_iff g u v).mp hs) hz

end KroneckerPaperPathGradings
