import KroneckerOutgoingSinkBranches

set_option autoImplicit false
namespace KroneckerColoredCutTransport
open SimpleGraph KroneckerTreeCutComponents KroneckerColoredIncidenceIso
open KroneckerFiniteColoredTables KroneckerTableIsomorphisms
open KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches

def deleteEdgeIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (u v : V) : G.deleteEdges {s(u,v)} ≃g H.deleteEdges {s(e u,e v)} where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    change (H.deleteEdges {s(e u,e v)}).Adj (e x) (e y) ↔ (G.deleteEdges {s(u,v)}).Adj x y
    simp only [deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff,e.map_rel_iff,e.injective.eq_iff]

theorem cut_side_iso_iff {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (u v x : V) : cutSide H (e u) (e v) (e x) ↔ cutSide G u v x :=
  Iso.reachable_iff (φ:=deleteEdgeIso e u v)

variable {I J I' J' : Type} {T : ColoredTable I J} {U : ColoredTable I' J'}

/-- Actual colored isomorphisms transport every cut component with its original incidences. -/
noncomputable def coloredCutIso (e : ColoredIso (coloring T) (coloring U)) (u v : I ⊕ J) :
    ColoredIso (coloring (cutTable T u v)) (coloring (cutTable U (e.graphIso u) (e.graphIso v))) := by
  let s : {i // cutSource T u v i} ≃ {i // cutSource U (e.graphIso u) (e.graphIso v) i} :=
    Equiv.subtypeEquiv e.source (fun i => (cut_side_iso_iff e.graphIso u v (.inl i)).symm)
  let t : {j // cutSink T u v j} ≃ {j // cutSink U (e.graphIso u) (e.graphIso v) j} :=
    Equiv.subtypeEquiv e.sink (fun j => (cut_side_iso_iff e.graphIso u v (.inr j)).symm)
  apply isoOfCode _ _ s t
  intro i j
  exact iso_preserves_code T U e i.1 j.1



end KroneckerColoredCutTransport
