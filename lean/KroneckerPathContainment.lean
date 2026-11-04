import KroneckerPaperPaths
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint

/-! Definitions 2.2(4–5): consecutive subpaths with their actual lattice positions.
The unique empty path is a subpath of every path; disjointness concerns edges. -/
set_option autoImplicit false
namespace KroneckerPaperPaths

/-- The manuscript's ordinary subpath relation. -/
def IsSubpath (A B : TNEPath) : Prop :=
  ∃ i j : ℕ, i ≤ j ∧ j ≤ B.steps.length ∧ A = subpath B i j

/-- Paths are disjoint when they have no common geometric edge. -/
def EdgeDisjoint (A B : TNEPath) : Prop :=
  Disjoint (Set.range (edge A)) (Set.range (edge B))

@[simp] theorem subpath_all (P : TNEPath) : subpath P 0 P.steps.length = P := by
  apply TNEPath.ext
  · simp [subpath]
  · by_cases h : P.steps = []
    · simp [subpath, h, P.empty_origin h, ofSteps]
    · simp [subpath, vertex, ofSteps, h]

theorem IsSubpath.refl (P : TNEPath) : IsSubpath P P :=
  ⟨0, P.steps.length, Nat.zero_le _, le_rfl, (subpath_all P).symm⟩

@[simp] theorem empty_isSubpath (P : TNEPath) : IsSubpath empty P :=
  ⟨0, 0, le_rfl, Nat.zero_le _, (subpath_self P 0).symm⟩

theorem subpath_isSubpath (P : TNEPath) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ P.steps.length) : IsSubpath (subpath P i j) P :=
  ⟨i,j,hij,hj,rfl⟩

theorem subpath_length (P : TNEPath) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.steps.length) :
    (subpath P i j).steps.length = j-i := by
  simp only [subpath_steps, List.length_take, List.length_drop]
  omega

/-- Subpath composition preserves position, including the empty case. -/
theorem subpath_subpath (P : TNEPath) {i j a b : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.steps.length)
    (hab : a ≤ b) (hb : b ≤ j-i) :
    subpath (subpath P i j) a b = subpath P (i+a) (i+b) := by
  by_cases he : a = b
  · subst b
    simp
  have hab' : a < b := by omega
  have hiab : i+a < i+b := by omega
  have hib : i+b ≤ P.steps.length := by omega
  have hlen := subpath_length P hij hj
  apply TNEPath.ext
  · simp only [subpath_steps, List.drop_take, List.drop_drop, List.take_take]
    congr 1
    omega
  · rw [subpath_origin _ _ _ hab' (by omega), subpath_origin _ _ _ hiab hib]
    exact subpath_vertex P i j a (by omega) hj (by omega)

theorem IsSubpath.trans {A B C : TNEPath} (hAB : IsSubpath A B)
    (hBC : IsSubpath B C) : IsSubpath A C := by
  obtain ⟨a,b,hab,hb,rfl⟩ := hAB
  obtain ⟨i,j,hij,hj,rfl⟩ := hBC
  rw [subpath_length C hij hj] at hb
  exact ⟨i+a,i+b,by omega,by omega,subpath_subpath C hij hj hab hb⟩

theorem IsSubpath.edge_subset {A B : TNEPath} (h : IsSubpath A B) :
    Set.range (edge A) ⊆ Set.range (edge B) := by
  obtain ⟨i,j,_,hj,rfl⟩ := h
  rintro _ ⟨k,rfl⟩
  exact ⟨subpathEdge B i j hj k, (subpath_edge B i j hj k).symm⟩

theorem edgeDisjoint_iff (A B : TNEPath) : EdgeDisjoint A B ↔
    ∀ (a : Edge A) (b : Edge B), edge A a ≠ edge B b := by
  rw [EdgeDisjoint, Set.disjoint_left]
  constructor
  · intro h a b he
    exact h ⟨a,rfl⟩ ⟨b,he.symm⟩
  · rintro h _ ⟨a,rfl⟩ ⟨b,hb⟩
    exact h a b hb.symm

end KroneckerPaperPaths
