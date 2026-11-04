import KroneckerTableIsomorphisms
import KroneckerUnrootedColoredRigidity

set_option autoImplicit false
namespace KroneckerColoredTableTranspose
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence KroneckerColoredIncidenceIso
open KroneckerTableIsomorphisms

variable {I J : Type}

def transposeTable (T : ColoredTable I J) : ColoredTable J I where
  code j i := T.code i j
  atSource := fun j i k d hi hk => T.atSink i k j d hi hk
  atSink := fun j k i d hj hk => T.atSource i j k d hj hk


def transposeGraphIso (T : ColoredTable I J) :
    incidenceGraph (Incidence (transposeTable T)) ≃g incidenceGraph (Incidence T) where
  toEquiv := Equiv.sumComm J I
  map_rel_iff' := by intro u v; cases u <;> cases v <;> rfl

theorem transpose_tree_iff (T : ColoredTable I J) :
    (incidenceGraph (Incidence (transposeTable T))).IsTree ↔
      (incidenceGraph (Incidence T)).IsTree := (transposeGraphIso T).isTree_iff

noncomputable def transposeColoredIso {I' J' : Type}
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (e : ColoredIso (coloring T) (coloring U)) :
    ColoredIso (coloring (transposeTable T)) (coloring (transposeTable U)) :=
  isoOfCode _ _ e.sink e.source (fun j i => iso_preserves_code T U e i j)


end KroneckerColoredTableTranspose
