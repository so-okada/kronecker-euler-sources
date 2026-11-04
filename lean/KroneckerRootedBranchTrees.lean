import KroneckerTreeCutComponents

section

set_option autoImplicit false
namespace KroneckerRootedEdgePartition
open SimpleGraph KroneckerTreeCutComponents

variable {V : Type*} {G : SimpleGraph V}

/-- The root cannot occur anywhere along a walk inside an outgoing tree branch. -/
theorem branch_walk_avoids_root (hT : G.IsTree) {r v x : V} (hv : G.Adj r v)
    (p : (G.deleteEdges {s(r,v)}).Walk v x) : r ∉ p.support := by
  classical
  intro hr
  exact tree_cut_excludes_source hT hv (p.takeUntil r hr).reachable

/-- Two outgoing components at a root are disjoint unless their first neighbors agree. -/
theorem branch_neighbor_unique (hT : G.IsTree) {r v w x : V}
    (hv : G.Adj r v) (hw : G.Adj r w)
    (hxv : cutSide G r v x) (hxw : cutSide G r w x) : v=w := by
  classical
  obtain ⟨p,hp⟩ := hxv.exists_isPath
  obtain ⟨q,hq⟩ := hxw.exists_isPath
  have hle₁ : G.deleteEdges {s(r,v)} ≤ G := deleteEdges_le _
  have hle₂ : G.deleteEdges {s(r,w)} ≤ G := deleteEdges_le _
  have ha : r ∉ (p.mapLe hle₁).support := by
    simpa using branch_walk_avoids_root hT hv p
  have hb : r ∉ (q.mapLe hle₂).support := by
    simpa using branch_walk_avoids_root hT hw q
  have he := (hT.isAcyclic.subsingleton_path r x).elim
    (⟨Walk.cons hv (p.mapLe hle₁),(hp.mapLe hle₁).cons ha⟩ : G.Path r x)
    ⟨Walk.cons hw (q.mapLe hle₂),(hq.mapLe hle₂).cons hb⟩
  have he' := congrArg (fun z : G.Path r x => z.1.getVert 1) he
  simpa using he'

/-- Every nonroot vertex belongs to exactly one actual edge-deletion component. -/
theorem unique_outgoing_branch (hT : G.IsTree) (r : V) {x : V} (hx : x≠r) :
    ∃! v : G.neighborSet r,cutSide G r v.1 x := by
  classical
  obtain ⟨p,hp⟩ := hT.connected.exists_isPath r x
  cases p with
  | nil => exact False.elim (hx rfl)
  | @cons _ v _ hv q =>
    have hq := (Walk.cons_isPath_iff hv q).mp hp
    have hc : cutSide G r v x := by
      apply reachable_deleteEdges_iff_exists_walk.mpr
      exact ⟨q,fun he => hq.2 (q.fst_mem_support_of_mem_edges he)⟩
    exact ⟨⟨v,hv⟩,hc,fun w hw => Subtype.ext (branch_neighbor_unique hT w.2 hv hw hc)⟩

end KroneckerRootedEdgePartition
end

section

set_option autoImplicit false
namespace KroneckerRootedBranchTrees
open SimpleGraph KroneckerTreeCutComponents KroneckerRootedEdgePartition

variable {V : Type*} {G : SimpleGraph V}

/-- An edge-deletion component carries exactly the induced graph on its vertices. -/
def branchComponentIso (hT : G.IsTree) {r v : V} (hv : G.Adj r v) :
    ((G.deleteEdges {s(r,v)}).connectedComponentMk v).toSimpleGraph ≃g
      G.induce {x | cutSide G r v x} where
  toFun x := ⟨x.1,(ConnectedComponent.exact x.2).symm⟩
  invFun x := ⟨x.1,ConnectedComponent.sound x.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro x y
    change G.Adj x.1 y.1 ↔ (G.deleteEdges {s(r,v)}).Adj x.1 y.1
    have hx : x.1≠r := by
      intro h
      have hr : cutSide G r v x.1 := (ConnectedComponent.exact x.2).symm
      exact tree_cut_excludes_source hT hv (by simpa only [h] using hr)
    have hy : y.1≠r := by
      intro h
      have hr : cutSide G r v y.1 := (ConnectedComponent.exact y.2).symm
      exact tree_cut_excludes_source hT hv (by simpa only [h] using hr)
    simp only [deleteEdges_adj,Set.mem_singleton_iff,Sym2.eq_iff]
    simp [hx,hy]

theorem outgoing_branch_is_tree (hT : G.IsTree) {r v : V} (hv : G.Adj r v) :
    (G.induce {x | cutSide G r v x}).IsTree := by
  exact ⟨(branchComponentIso hT hv).connected_iff.mp
    ((G.deleteEdges {s(r,v)}).connectedComponentMk v).connected_toSimpleGraph,
    hT.isAcyclic.induce _⟩

/-- Every neighbor of a branch vertex remains in that branch unless it is the deleted root. -/
theorem branch_closed_away_from_root {r v x y : V} (hx : cutSide G r v x)
    (hxy : G.Adj x y) (hy : y≠r) : cutSide G r v y := by
  by_contra hout
  have he := crossing_is_removed_edge r v hxy.symm hout hx
  rcases (Sym2.eq_iff.mp he) with h | h
  · exact hy h.1
  · apply hout
    rw [h.1]
    exact cut_side_contains_target G r v

end KroneckerRootedBranchTrees
end

