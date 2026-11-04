import KroneckerSaturatedTableAction

set_option autoImplicit false
namespace KroneckerTableLeafMarks
open KroneckerFiniteColoredTables KroneckerTableIsomorphisms KroneckerColoredIncidenceIso
open KroneckerRetainedVacantSlots KroneckerColoredLeafTransport
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I]

def LeafMark (T : ColoredTable I J) (d : Fin 3) (j : J) : Prop :=
  Fintype.card {i // Incidence T i j}=1 ∧ ∃ i,T.code i j=some d

noncomputable def leafMarkEquiv (T : ColoredTable I J) (d : Fin 3) :
    {j // LeafMark T d j} ≃
      {j : {j // Fintype.card {i // Incidence T i j}=1} // leafColor (coloring T) j=d} where
  toFun j := ⟨⟨j.1,j.2.1⟩,by
    obtain ⟨i,hi⟩ := j.2.2
    obtain ⟨h,hd⟩ := (code_eq_some_iff T i j.1 d).mp hi
    haveI : Subsingleton {i // Incidence T i j.1} :=
      Fintype.card_le_one_iff_subsingleton.mp j.2.1.le
    have hn : leafNeighbor (⟨j.1,j.2.1⟩ : {j // Fintype.card {i // Incidence T i j}=1})=⟨i,h⟩ :=
      Subsingleton.elim _ _
    simpa only [leafColor,hn] using hd⟩
  invFun j := ⟨j.1.1,j.1.2,⟨(leafNeighbor j.1).1,
    (code_eq_some_iff T _ _ d).mpr ⟨(leafNeighbor j.1).2,j.2⟩⟩⟩
  left_inv j := rfl
  right_inv j := rfl

theorem leaf_mark_transport {I' J' : Type} [Fintype I']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (e : ColoredIso (coloring T) (coloring U)) (d : Fin 3) (j : J) :
    LeafMark U d (e.sink j) ↔ LeafMark T d j := by
  unfold LeafMark
  rw [e.sink_degree]
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨i',hi⟩
    obtain ⟨i,rfl⟩ := e.source.surjective i'
    exact ⟨i,(iso_preserves_code T U e i j).symm.trans hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨e.source i,(iso_preserves_code T U e i j).trans hi⟩

noncomputable def leafMarkTransport {I' J' : Type} [Fintype I']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (e : ColoredIso (coloring T) (coloring U)) (d : Fin 3) :
    {j // LeafMark T d j} ≃ {j // LeafMark U d j} :=
  Equiv.subtypeEquiv e.sink (fun j => (leaf_mark_transport e d j).symm)

theorem leaf_mark_count_invariant {I' J' : Type} [Fintype I'] [Fintype J] [Fintype J']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (e : ColoredIso (coloring T) (coloring U)) (d : Fin 3) :
    Fintype.card {j // LeafMark T d j}=Fintype.card {j // LeafMark U d j} :=
  Fintype.card_congr (leafMarkTransport e d)

end KroneckerTableLeafMarks
