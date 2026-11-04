import KroneckerTypedQuiverMaps

/-! A typed multiquiver is a reduced forest when every reduced closed walk is
empty. Every reduced walk in such a quiver has distinct vertices and length
strictly below the finite vertex count. The definition retains parallel-arrow
labels and loops instead of silently replacing them by a simple graph. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTypedReducedForest
open KroneckerAbelianCover LabeledWalk KroneckerTypedQuiverMaps
attribute [local instance] Classical.decEq Classical.propDecidable

def ReducedForest (Q : TypedQuiver) : Prop :=
  ∀ u (p : LabeledWalk Q.source Q.target u u), Reduced p → labels p = []

theorem forest_of_finite_girth (Q : TypedQuiver) [Fintype Q.A] (g : ℕ)
    (hg : ReducedGirthBound Q.source Q.target g) (hc : Fintype.card Q.A + 1 < g) : ReducedForest Q := by
  intro u p hp
  exact finite_support_no_reduced_closed hg Finset.univ (by simpa using hc) p hp
    (Finset.subset_univ _)

theorem reduced_vertices_nodup (Q : TypedQuiver) (hQ : ReducedForest Q) {u v : Q.V}
    (p : LabeledWalk Q.source Q.target u v) (hp : Reduced p) : (vertices p).Nodup := by
  by_contra hn
  obtain ⟨w,q,hq,hpos,_⟩ := repeated_vertex_closed_subwalk p hp hn
  have hz := hQ w q hq
  rw [hz] at hpos
  exact Nat.lt_irrefl 0 hpos

theorem vertices_length (Q : TypedQuiver) {u v : Q.V} (p : LabeledWalk Q.source Q.target u v) :
    (vertices p).length = (labels p).length + 1 := by
  induction p <;> simp_all [vertices,labels,Nat.add_comm]

theorem reduced_length_lt_card (Q : TypedQuiver) [Fintype Q.V] (hQ : ReducedForest Q) {u v : Q.V}
    (p : LabeledWalk Q.source Q.target u v) (hp : Reduced p) : (labels p).length < Fintype.card Q.V := by
  have h := (reduced_vertices_nodup Q hQ p hp).length_le_card
  rw [vertices_length] at h
  omega


end KroneckerTypedReducedForest
