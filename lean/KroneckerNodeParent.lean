import KroneckerHPrecursor
import KroneckerPathContainment

/-! Geometric containment and the parent in Definition 2.16; uniqueness in Lemma 2.17. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerPaperPathGradings
open KroneckerPaperPaths

@[simp] theorem edge_equiv_inverse (P : TNEPath) (w : GeomEdge P) :
    edge P ((edgeEquiv P).symm w) = w.val :=
  congrArg Subtype.val ((edgeEquiv P).apply_symm_apply w)

variable {m : ℕ} {P : TNEPath} {g : Grading m P}
variable {p : Vertical P → Horizontal P}

theorem Node.start_lt_end (hp : IsHPrecursor g p) (X : Node g p) :
    edgeIndex X.first.val < edgeIndex X.last.val := by
  have h := ((isHPrecursor_iff g p).mp hp X.last).1
  simpa only [X.isNode.1] using h

theorem Node.isSubpath (hp : IsHPrecursor g p) (X : Node g p) :
    IsSubpath (nodePath X.first X.last) P :=
  subpath_isSubpath P _ _ (by have := X.start_lt_end hp; omega)
    ((edgeEquiv P).symm X.last.val).isLt

theorem Node.first_mem (hp : IsHPrecursor g p) (X : Node g p) :
    X.first.val.val ∈ nodeEdges X := by
  have h := (nodePath_mem_edge_iff X.first X.last ((edgeEquiv P).symm X.first.val)).mpr
    ⟨le_rfl, (X.start_lt_end hp).le⟩
  simpa only [edge_equiv_inverse, nodeEdges] using h

theorem Node.last_mem (hp : IsHPrecursor g p) (X : Node g p) :
    X.last.val.val ∈ nodeEdges X := by
  have h := (nodePath_mem_edge_iff X.first X.last ((edgeEquiv P).symm X.last.val)).mpr
    ⟨(X.start_lt_end hp).le, le_rfl⟩
  simpa only [edge_equiv_inverse, nodeEdges] using h

theorem nodeEdges_subset_iff (hp : IsHPrecursor g p) (X Y : Node g p) :
    nodeEdges X ⊆ nodeEdges Y ↔
      edgeIndex Y.first.val ≤ edgeIndex X.first.val ∧
      edgeIndex X.last.val ≤ edgeIndex Y.last.val := by
  constructor
  · intro h
    have hf := h (X.first_mem hp)
    have hl := h (X.last_mem hp)
    have hff := (nodePath_mem_edge_iff Y.first Y.last
      ((edgeEquiv P).symm X.first.val)).mp (by simpa only [edge_equiv_inverse, nodeEdges] using hf)
    have hll := (nodePath_mem_edge_iff Y.first Y.last
      ((edgeEquiv P).symm X.last.val)).mp (by simpa only [edge_equiv_inverse, nodeEdges] using hl)
    exact ⟨hff.1,hll.2⟩
  · rintro ⟨hleft,hright⟩ e he
    have hP := X.isSubpath hp |>.edge_subset he
    obtain ⟨k,rfl⟩ := hP
    have hx := (nodePath_mem_edge_iff X.first X.last k).mp he
    exact (nodePath_mem_edge_iff Y.first Y.last k).mpr ⟨by omega,by omega⟩

/-- For nodes, the existing geometric-edge relation is exactly ordinary subpath
containment, with the same endpoints and origin. -/
theorem node_isSubpath_iff (hp : IsHPrecursor g p) (X Y : Node g p) :
    IsSubpath (nodePath X.first X.last) (nodePath Y.first Y.last) ↔
      nodeEdges X ⊆ nodeEdges Y := by
  constructor
  · exact IsSubpath.edge_subset
  · intro h
    obtain ⟨hl,hr⟩ := (nodeEdges_subset_iff hp X Y).mp h
    have hxy := X.start_lt_end hp
    have hyy := Y.start_lt_end hp
    let i := edgeIndex Y.first.val
    let j := edgeIndex Y.last.val+1
    let a := edgeIndex X.first.val-i
    let b := edgeIndex X.last.val+1-i
    have hij : i ≤ j := by dsimp [i,j]; omega
    have hj : j ≤ P.steps.length := ((edgeEquiv P).symm Y.last.val).isLt
    have hab : a ≤ b := by dsimp [a,b]; omega
    have hb : b ≤ j-i := by dsimp [b,j]; omega
    refine ⟨a,b,hab,?_,?_⟩
    · change b ≤ (subpath P i j).steps.length
      rw [subpath_length P hij hj]
      exact hb
    · change subpath P _ _ = subpath (subpath P i j) a b
      rw [subpath_subpath P hij hj hab hb]
      have hi : i+a = edgeIndex X.first.val := by dsimp [a,i]; omega
      have hj' : i+b = edgeIndex X.last.val+1 := by dsimp [b,i]; omega
      rw [hi,hj']

theorem nodeEdges_injective (hp : IsHPrecursor g p) :
    Function.Injective (nodeEdges (g := g) (p := p)) := by
  intro X Y he
  have hXY := (nodeEdges_subset_iff hp X Y).mp he.subset
  have hYX := (nodeEdges_subset_iff hp Y X).mp he.symm.subset
  have hf : X.first = Y.first := by
    apply Subtype.ext
    apply (edgeEquiv P).symm.injective
    apply Fin.ext
    exact Nat.le_antisymm hYX.1 hXY.1
  have hl : X.last = Y.last := by
    apply Subtype.ext
    apply (edgeEquiv P).symm.injective
    apply Fin.ext
    exact Nat.le_antisymm hXY.2 hYX.2
  cases X; cases Y; cases hf; cases hl; rfl

theorem nodeEdges_laminar (hp : IsHPrecursor g p) (X Y : Node g p) :
    Disjoint (nodeEdges X) (nodeEdges Y) ∨
      nodeEdges X ⊆ nodeEdges Y ∨ nodeEdges Y ⊆ nodeEdges X := by
  have hp' := (isPredecessor_iff g p).mp ((isHPrecursor_iff g p).mp hp)
  have hX := (isNode_iff g p X.first X.last).mp X.isNode
  have hY := (isNode_iff g p Y.first Y.last).mp Y.isNode
  have h := hX.disjoint_or_nested hY hp'
  change edgeIndex X.last.val < edgeIndex Y.first.val ∨
    edgeIndex Y.last.val < edgeIndex X.first.val ∨
    (edgeIndex X.first.val ≤ edgeIndex Y.first.val ∧ edgeIndex Y.last.val ≤ edgeIndex X.last.val) ∨
    (edgeIndex Y.first.val ≤ edgeIndex X.first.val ∧ edgeIndex X.last.val ≤ edgeIndex Y.last.val) at h
  rcases h with h | h | h | h
  · left
    rw [Set.disjoint_left]
    intro e hx hy
    obtain ⟨k,rfl⟩ := (X.isSubpath hp).edge_subset hx
    have hx' := (nodePath_mem_edge_iff X.first X.last k).mp hx
    have hy' := (nodePath_mem_edge_iff Y.first Y.last k).mp hy
    omega
  · left
    rw [Set.disjoint_left]
    intro e hx hy
    obtain ⟨k,rfl⟩ := (X.isSubpath hp).edge_subset hx
    have hx' := (nodePath_mem_edge_iff X.first X.last k).mp hx
    have hy' := (nodePath_mem_edge_iff Y.first Y.last k).mp hy
    omega
  · exact Or.inr (Or.inr ((nodeEdges_subset_iff hp Y X).mpr h))
  · exact Or.inr (Or.inl ((nodeEdges_subset_iff hp X Y).mpr h))

/-- A node has at most one parent. No maximality or existence assumption is
added; this follows from laminarity and the definition of Parent. -/
theorem parent_unique (hp : IsHPrecursor g p) {X Y Z : Node g p}
    (hX : Parent X Z) (hY : Parent Y Z) : X = Y := by
  by_contra hne
  have hsets : nodeEdges X ≠ nodeEdges Y := fun h => hne (nodeEdges_injective hp h)
  rcases nodeEdges_laminar hp X Y with hd | hXY | hYX
  · exact Set.disjoint_left.mp hd (hX.1.1 (Z.first_mem hp)) (hY.1.1 (Z.first_mem hp))
  · have hstrict : Ancestor Y X := lt_of_le_of_ne hXY hsets
    exact hY.2 ⟨X,hstrict,hX.1⟩
  · have hstrict : Ancestor X Y := lt_of_le_of_ne hYX hsets.symm
    exact hX.2 ⟨Y,hstrict,hY.1⟩

end KroneckerPaperPathGradings
