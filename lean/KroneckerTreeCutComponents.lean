import KroneckerPositiveFlowBoundary

set_option autoImplicit false
namespace KroneckerTreeCutComponents
open SimpleGraph KroneckerBipartiteIncidence
attribute [local instance] Classical.propDecidable

def cutSide {V : Type*} (G : SimpleGraph V) (u v w : V) : Prop :=
  (G.deleteEdges {s(u,v)}).Reachable v w

theorem cut_side_contains_target {V : Type*} (G : SimpleGraph V) (u v : V) :
    cutSide G u v v := Reachable.refl _

theorem tree_cut_excludes_source {V : Type*} {G : SimpleGraph V}
    (hT : G.IsTree) {u v : V} (h : G.Adj u v) : ¬cutSide G u v u := by
  have hb := (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) h
  have hn := isBridge_iff.mp hb
  intro hr
  exact hn hr.symm

theorem crossing_is_removed_edge {V : Type*} {G : SimpleGraph V}
    (u v : V) {w z : V} (hadj : G.Adj w z)
    (hout : ¬cutSide G u v w) (hin : cutSide G u v z) : s(w,z)=s(u,v) := by
  by_contra hne
  have he : (G.deleteEdges {s(u,v)}).Adj w z :=
    deleteEdges_adj.mpr ⟨hadj,by simpa using hne⟩
  exact hout (hin.trans he.symm.reachable)

noncomputable def cutConnectors {I J : Type*} [Fintype I]
    (R : I → J → Prop) (i : I) (j : J) : Finset I :=
  Finset.univ.filter (fun k => cutSide (incidenceGraph R) (.inl i) (.inr j) (.inl k))

noncomputable def cutBlocks {I J : Type*} [Fintype J]
    (R : I → J → Prop) (i : I) (j : J) : Finset J :=
  Finset.univ.filter (fun k => cutSide (incidenceGraph R) (.inl i) (.inr j) (.inr k))

theorem cut_connector_excluded {I J : Type*} [Fintype I]
    {R : I → J → Prop} (hT : (incidenceGraph R).IsTree) {i : I} {j : J} (h : R i j) :
    i∉cutConnectors R i j := by
  simpa [cutConnectors] using tree_cut_excludes_source hT (u:=.inl i) (v:=.inr j) h

theorem cut_block_included {I J : Type*} [Fintype J]
    (R : I → J → Prop) (i : I) (j : J) : j∈cutBlocks R i j := by
  simpa [cutBlocks] using cut_side_contains_target (incidenceGraph R) (.inl i) (.inr j)

theorem cut_boundary_unique {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (i₀ : I) (j₀ : J) {i : I} {j : J}
    (hi : i∉cutConnectors R i₀ j₀) (hj : j∈cutBlocks R i₀ j₀) (hij : R i j) :
    i=i₀ ∧ j=j₀ := by
  have hi' : ¬cutSide (incidenceGraph R) (.inl i₀) (.inr j₀) (.inl i) := by
    simpa [cutConnectors] using hi
  have hj' : cutSide (incidenceGraph R) (.inl i₀) (.inr j₀) (.inr j) := by
    simpa [cutBlocks] using hj
  have he := crossing_is_removed_edge (G:=incidenceGraph R) (.inl i₀) (.inr j₀)
    (w:=.inl i) (z:=.inr j) hij hi' hj'
  simpa [Sym2.eq_iff] using he

theorem cut_is_connector_closed {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (hT : (incidenceGraph R).IsTree)
    {i₀ : I} {j₀ : J} (h₀ : R i₀ j₀) {i : I} {j : J}
    (hi : i∈cutConnectors R i₀ j₀) (hij : R i j) : j∈cutBlocks R i₀ j₀ := by
  by_contra hj
  have hi' : cutSide (incidenceGraph R) (.inl i₀) (.inr j₀) (.inl i) := by
    simpa [cutConnectors] using hi
  have hj' : ¬cutSide (incidenceGraph R) (.inl i₀) (.inr j₀) (.inr j) := by
    simpa [cutBlocks] using hj
  have he := crossing_is_removed_edge (.inl i₀) (.inr j₀) (G:=incidenceGraph R)
    (w:=.inr j) (z:=.inl i) hij hj' hi'
  have heq : j=j₀ ∧ i=i₀ := by simpa [Sym2.eq_iff] using he
  exact cut_connector_excluded hT h₀ (heq.2 ▸ hi)

end KroneckerTreeCutComponents
