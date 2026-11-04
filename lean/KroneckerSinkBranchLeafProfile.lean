import KroneckerBranchIsomorphismInvariance

set_option autoImplicit false
namespace KroneckerSinkBranchLeafProfile
open KroneckerFiniteColoredTables KroneckerTableLeafMarks KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I]

/-- A sink branch is counted after its parent edge is attached: its isolated root is a leaf
of the parent color, while a root with children is no longer a leaf. -/
def SinkLeaf (T : ColoredTable I J) (r : J) (d e : Fin 3) (j : J) : Prop :=
  (j≠r ∧ LeafMark T e j) ∨ (j=r ∧ (∀ i,¬Incidence T i r) ∧ e=d)

theorem sink_leaf_root (T : ColoredTable I J) (r : J) (d e : Fin 3) :
    SinkLeaf T r d e r ↔ (∀ i,¬Incidence T i r) ∧ e=d := by simp [SinkLeaf]

theorem sink_leaf_transport {I' J' : Type} [Fintype I']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (f : ColoredIso (coloring T) (coloring U)) (r j : J) (d e : Fin 3) :
    SinkLeaf U (f.sink r) d e (f.sink j) ↔ SinkLeaf T r d e j := by
  have hi : (∀ i,¬Incidence U i (f.sink r)) ↔ ∀ i,¬Incidence T i r := by
    constructor
    · intro h i hx
      exact h (f.source i) ((f.incidence i r).mpr hx)
    · intro h i hx
      obtain ⟨i,rfl⟩ := f.source.surjective i
      exact h i ((f.incidence i r).mp hx)
  simp only [SinkLeaf,f.sink.injective.eq_iff,f.sink.injective.ne_iff,leaf_mark_transport,hi]

noncomputable def sinkLeafTransport {I' J' : Type} [Fintype I']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (f : ColoredIso (coloring T) (coloring U)) (r : J) (d e : Fin 3) :
    {j // SinkLeaf T r d e j} ≃ {j // SinkLeaf U (f.sink r) d e j} :=
  Equiv.subtypeEquiv f.sink (fun j => (sink_leaf_transport f r j d e).symm)

theorem sink_leaf_count_invariant {I' J' : Type} [Fintype I'] [Fintype J] [Fintype J']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (f : ColoredIso (coloring T) (coloring U)) (r : J) (d e : Fin 3) :
    Fintype.card {j // SinkLeaf T r d e j}=Fintype.card {j // SinkLeaf U (f.sink r) d e j} := by
  classical
  exact Fintype.card_congr (sinkLeafTransport f r d e)

end KroneckerSinkBranchLeafProfile
