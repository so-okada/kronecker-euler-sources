import KroneckerCyclicEdgeSets

/-! Compatibility and shadows expressed using the ambient cyclic edge sets. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerPaperPaths

theorem cyclicLength_prefix {P : TNEPath} (u v : Edge P)
    (k : Fin (cyclicLength u v)) :
    cyclicLength u (cyclicIndex u v k) = k.val+1 := by
  have hu := u.isLt
  have hk := k.isLt
  have hl := cyclicLength_le u v
  change (if u.val ≤ (cyclicIndex u v k).val then
    (cyclicIndex u v k).val-u.val+1 else
    P.steps.length-u.val+(cyclicIndex u v k).val+1) = k.val+1
  rw [cyclicIndex_val]
  split_ifs <;> omega

theorem cyclicLength_suffix {P : TNEPath} (u v : Edge P)
    (k : Fin (cyclicLength u v)) :
    cyclicLength (cyclicIndex u v k) v = cyclicLength u v-k.val := by
  have hu := u.isLt
  have hv := v.isLt
  have hk := k.isLt
  simp only [cyclicLength] at hk ⊢
  simp only [cyclicIndex_val]
  split_ifs at * <;> omega

end KroneckerPaperPaths
namespace KroneckerPaperPathGradings
open KroneckerPaperPaths KroneckerCompatibility

theorem cyclicTrace_at {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (k : ℕ) (hk : k < cyclicLength u v) :
    geometricTrace (NERealGrading g u v) k = geometricTrace g (u.val+k) :=
  cyclicTrace_correspondence g u v
    (⟨k, by rw [cyclicRealization_length]; exact hk⟩ : Edge (cyclicRealization u v))

theorem cyclicTrace_index {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (k : Fin (cyclicLength u v)) :
    geometricTrace (NERealGrading g u v) k.val = geometricTrace g (cyclicIndex u v k).val := by
  rw [cyclicTrace_at g u v k.val k.isLt, cyclicIndex_mod, geometricTrace_mod]

theorem cyclic_prefix_sum {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (k : Fin (cyclicLength u v)) (f : KroneckerStack.Edge → ℤ) :
    intervalSum f (geometricTrace (NERealGrading g u v)) 0 (k.val+1) =
      intervalSum f (geometricTrace (NERealGrading g u (cyclicIndex u v k))) 0
        (cyclicLength u (cyclicIndex u v k)) := by
  rw [cyclicLength_prefix]
  unfold intervalSum
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [Nat.zero_add, cyclicTrace_at g u v i (by have := k.isLt; omega),
    cyclicTrace_at g u (cyclicIndex u v k) i (by rw [cyclicLength_prefix]; exact hi')]

theorem cyclic_suffix_sum {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (k : Fin (cyclicLength u v)) (f : KroneckerStack.Edge → ℤ) :
    intervalSum f (geometricTrace (NERealGrading g u v)) k.val (cyclicLength u v-k.val) =
      intervalSum f (geometricTrace (NERealGrading g (cyclicIndex u v k) v)) 0
        (cyclicLength (cyclicIndex u v k) v) := by
  rw [cyclicLength_suffix]
  unfold intervalSum
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [Nat.zero_add, cyclicTrace_at g u v (k.val+i) (by have := k.isLt; omega),
    cyclicTrace_at g (cyclicIndex u v k) v i (by rw [cyclicLength_suffix]; exact hi')]
  congr 1
  rw [← geometricTrace_mod g (u.val+(k.val+i)),
    ← geometricTrace_mod g ((cyclicIndex u v k).val+i), cyclicIndex_mod]
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- The horizontal equality in Definition 2.19(1)(a), with ambient edges. -/
def AmbientHWitness {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v t : Edge P) : Prop :=
  edgeEquiv P t ∈ cyclicNE P u v ∧ P.steps.get t = false ∧ t ≠ v ∧
    ((cyclicN P u t).card : ℤ) = ∑ w ∈ cyclicE P u t, ((g w).val : ℤ)

/-- The vertical equality in Definition 2.19(1)(b), with ambient edges. -/
def AmbientVWitness {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v t : Edge P) : Prop :=
  edgeEquiv P t ∈ cyclicNE P u v ∧ P.steps.get t = true ∧ t ≠ u ∧
    ((cyclicE P t v).card : ℤ) = ∑ w ∈ cyclicN P t v, ((g w).val : ℤ)

/-- Literal witness formulation of compatibility, for any tNE path. -/
def AmbientCompatible {m : ℕ} {P : TNEPath} (g : Grading m P) : Prop :=
  ∀ u v : Edge P, P.steps.get u = true → P.steps.get v = false →
    0 < (g (edgeEquiv P u)).val → 0 < (g (edgeEquiv P v)).val →
      ∃ t : Edge P, AmbientHWitness g u v t ∨ AmbientVWitness g u v t

theorem positiveH_geometric {m : ℕ} {P : TNEPath} (g : Grading m P) (u : Edge P) :
    PositiveH (geometricTrace g) u.val ↔
      P.steps.get u = true ∧ 0 < (g (edgeEquiv P u)).val := by
  rw [PositiveH, geometricTrace_edge]
  cases P.steps.get u <;> simp

theorem positiveV_geometric {m : ℕ} {P : TNEPath} (g : Grading m P) (v : Edge P) :
    PositiveV (geometricTrace g) v.val ↔
      P.steps.get v = false ∧ 0 < (g (edgeEquiv P v)).val := by
  rw [PositiveV, geometricTrace_edge]
  cases P.steps.get v <;> simp

theorem vertical_cyclic_index {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (k : Fin (cyclicLength u v)) :
    KroneckerCompatibility.Vertical (geometricTrace (NERealGrading g u v)) k.val ↔
      P.steps.get (cyclicIndex u v k) = false := by
  rw [KroneckerCompatibility.Vertical, cyclicTrace_index, geometricTrace_edge]
  cases P.steps.get (cyclicIndex u v k) <;> simp

theorem horizontal_cyclic_index {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (k : Fin (cyclicLength u v)) :
    KroneckerCompatibility.Horizontal (geometricTrace (NERealGrading g u v)) k.val ↔
      P.steps.get (cyclicIndex u v k) = true := by
  rw [KroneckerCompatibility.Horizontal, cyclicTrace_index, geometricTrace_edge]
  cases P.steps.get (cyclicIndex u v k) <;> simp

theorem hwitness_ambient_iff {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hu : P.steps.get u = true) :
    HWitness (geometricTrace (NERealGrading g u v)) 0 (cyclicLength u v-1) ↔
      ∃ t, AmbientHWitness g u v t := by
  rw [hwitness_counts]
  simp only [Nat.sub_zero]
  constructor
  · rintro ⟨k,hk,hkl,hV,he⟩
    let K : Fin (cyclicLength u v) := ⟨k,by omega⟩
    refine ⟨cyclicIndex u v K, ?_, ?_, ?_, ?_⟩
    · exact (mem_cyclicNE u v _).mpr ⟨K,rfl⟩
    · exact (vertical_cyclic_index g u v K).mp hV
    · intro hv
      have := cyclicIndex_first_encounter u v K hv
      dsimp [K] at this
      omega
    · change intervalSum hGrade _ 0 (K.val+1) = intervalSum vCount _ 0 (K.val+1) at he
      rw [cyclic_prefix_sum, cyclic_prefix_sum, cyclic_east_grade, cyclic_north_count] at he
      exact he.symm
  · rintro ⟨t,hm,ht,hne,he⟩
    obtain ⟨K,hK⟩ := (mem_cyclicNE u v _).mp hm
    have heq : cyclicIndex u v K = t := (edgeEquiv P).injective hK
    subst t
    have hk : 0 < K.val := by
      by_contra hh
      have hzero : K = ⟨0,cyclicLength_pos u v⟩ := Fin.ext (by dsimp; omega)
      rw [hzero, cyclicIndex_first, hu] at ht
      contradiction
    have hkl : K.val < cyclicLength u v-1 := by
      have hb := K.isLt
      by_contra hh
      have hlast : K = ⟨cyclicLength u v-1,by have := cyclicLength_pos u v; omega⟩ :=
        Fin.ext (by dsimp; omega)
      exact hne (by rw [hlast, cyclicIndex_last])
    refine ⟨K.val,hk,hkl,(vertical_cyclic_index g u v K).mpr ht,?_⟩
    rw [cyclic_prefix_sum, cyclic_prefix_sum, cyclic_east_grade, cyclic_north_count]
    exact he.symm

theorem vwitness_ambient_iff {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hv : P.steps.get v = false) :
    VWitness (geometricTrace (NERealGrading g u v)) 0 (cyclicLength u v-1) ↔
      ∃ t, AmbientVWitness g u v t := by
  rw [vwitness_counts]
  have hl : cyclicLength u v-1+1 = cyclicLength u v := by
    have := cyclicLength_pos u v; omega
  rw [hl]
  constructor
  · rintro ⟨k,hk,hkl,hH,he⟩
    let K : Fin (cyclicLength u v) := ⟨k,by omega⟩
    refine ⟨cyclicIndex u v K, ?_, ?_, ?_, ?_⟩
    · exact (mem_cyclicNE u v _).mpr ⟨K,rfl⟩
    · exact (horizontal_cyclic_index g u v K).mp hH
    · intro hu
      have hzero := cyclicIndex_injective u v (hu.trans (cyclicIndex_first u v).symm)
      have hz := congrArg Fin.val hzero
      dsimp [K] at hz
      omega
    · change intervalSum hCount _ K.val (cyclicLength u v-K.val) =
        intervalSum vGrade _ K.val (cyclicLength u v-K.val) at he
      rw [cyclic_suffix_sum, cyclic_suffix_sum, cyclic_east_count, cyclic_north_grade] at he
      exact he
  · rintro ⟨t,hm,ht,hne,he⟩
    obtain ⟨K,hK⟩ := (mem_cyclicNE u v _).mp hm
    have heq : cyclicIndex u v K = t := (edgeEquiv P).injective hK
    subst t
    have hk : 0 < K.val := by
      by_contra hh
      have hzero : K = ⟨0,cyclicLength_pos u v⟩ := Fin.ext (by dsimp; omega)
      exact hne (by rw [hzero, cyclicIndex_first])
    have hkl : K.val < cyclicLength u v-1 := by
      have hb := K.isLt
      by_contra hh
      have hlast : K = ⟨cyclicLength u v-1,by have := cyclicLength_pos u v; omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hlast, cyclicIndex_last, hv] at ht
      contradiction
    refine ⟨K.val,hk,hkl,(horizontal_cyclic_index g u v K).mpr ht,?_⟩
    rw [cyclic_suffix_sum, cyclic_suffix_sum, cyclic_east_count, cyclic_north_grade]
    exact he

/-- The direct edge-set definition and the verified trace definition are
logically equivalent, with both endpoint exclusions retained. -/
theorem ambientCompatible_iff {m : ℕ} {P : TNEPath} (g : Grading m P) :
    AmbientCompatible g ↔ Compatible g := by
  constructor
  · intro h u v hU hV
    obtain ⟨hu,hgu⟩ := (positiveH_geometric g u).mp hU
    obtain ⟨hv,hgv⟩ := (positiveV_geometric g v).mp hV
    obtain ⟨t,ht | ht⟩ := h u v hu hv hgu hgv
    · exact Or.inl ((hwitness_ambient_iff g u v hu).mpr ⟨t,ht⟩)
    · exact Or.inr ((vwitness_ambient_iff g u v hv).mpr ⟨t,ht⟩)
  · intro h u v hu hv hgu hgv
    rcases h u v ((positiveH_geometric g u).mpr ⟨hu,hgu⟩)
      ((positiveV_geometric g v).mpr ⟨hv,hgv⟩) with hH | hV
    · obtain ⟨t,ht⟩ := (hwitness_ambient_iff g u v hu).mp hH
      exact ⟨t,Or.inl ht⟩
    · obtain ⟨t,ht⟩ := (vwitness_ambient_iff g u v hv).mp hV
      exact ⟨t,Or.inr ht⟩

end KroneckerPaperPathGradings
