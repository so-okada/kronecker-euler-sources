import KroneckerGluedSupportGraph

section

set_option autoImplicit false
namespace KroneckerGluedSupportConnected
open SimpleGraph KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedSupportGraph KroneckerBipartiteIncidence

def rootVertex {I J : Type} (B : J → LinearCoverBlock)
    (r : ∀ j,(B j).Source ⊕ (B j).Sink) :
    (I ⊕ J) → ((I ⊕ (Σ j,(B j).Source)) ⊕ (Σ j,(B j).Sink))
  | .inl i => .inl (.inl i)
  | .inr j => blockVertex B j (r j)

def parentVertex {I J : Type} (B : J → LinearCoverBlock) :
    ((I ⊕ (Σ j,(B j).Source)) ⊕ (Σ j,(B j).Sink)) → I ⊕ J
  | .inl (.inl i) => .inl i
  | .inl (.inr p) => .inr p.1
  | .inr p => .inr p.1

theorem root_incidence_reachable {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hB : ∀ j,(supportGraph (B j)).Connected) (r : ∀ j,(B j).Source ⊕ (B j).Sink)
    {i : I} {j : J} (hij : R i j) :
    (gluedGraph B R attach).Reachable (rootVertex B r (.inl i)) (rootVertex B r (.inr j)) := by
  have he : (gluedGraph B R attach).Adj (.inl (.inl i)) (.inr ⟨j,attach i j hij⟩) :=
    GlueEdge.attachment i j hij
  exact he.reachable.trans ((hB j (.inr (attach i j hij)) (r j)).map (blockHom B R attach j))

theorem root_adjacency_reachable {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hB : ∀ j,(supportGraph (B j)).Connected) (r : ∀ j,(B j).Source ⊕ (B j).Sink)
    {u v : I ⊕ J} (h : (incidenceGraph R).Adj u v) :
    (gluedGraph B R attach).Reachable (rootVertex B r u) (rootVertex B r v) := by
  cases u with
  | inl i => cases v with
    | inl k => exact False.elim h
    | inr j => exact root_incidence_reachable B R attach hB r h
  | inr j => cases v with
    | inr k => exact False.elim h
    | inl i => exact (root_incidence_reachable B R attach hB r h).symm

theorem root_walk_reachable {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hB : ∀ j,(supportGraph (B j)).Connected) (r : ∀ j,(B j).Source ⊕ (B j).Sink)
    {u v : I ⊕ J} (p : (incidenceGraph R).Walk u v) :
    (gluedGraph B R attach).Reachable (rootVertex B r u) (rootVertex B r v) := by
  induction p with
  | nil => exact Reachable.refl _
  | cons h p ih => exact (root_adjacency_reachable B R attach hB r h).trans ih

theorem vertex_to_root {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hB : ∀ j,(supportGraph (B j)).Connected) (r : ∀ j,(B j).Source ⊕ (B j).Sink)
    (v : (I ⊕ (Σ j,(B j).Source)) ⊕ (Σ j,(B j).Sink)) :
    (gluedGraph B R attach).Reachable v (rootVertex B r (parentVertex B v)) := by
  cases v with
  | inl s => cases s with
    | inl i => exact Reachable.refl _
    | inr p => exact (hB p.1 (.inl p.2) (r p.1)).map (blockHom B R attach p.1)
  | inr p => exact (hB p.1 (.inr p.2) (r p.1)).map (blockHom B R attach p.1)

/-- Replacing every block node by a connected block and attaching at the chosen
sinks preserves connectedness, even when several attachments use the same sink. -/
theorem glued_graph_connected {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hB : ∀ j,(supportGraph (B j)).Connected) (hR : (incidenceGraph R).Connected) :
    (gluedGraph B R attach).Connected := by
  let r : ∀ j,(B j).Source ⊕ (B j).Sink := fun j => Classical.choice (hB j).nonempty
  refine { preconnected := ?_, nonempty := ⟨rootVertex B r (Classical.choice hR.nonempty)⟩ }
  intro u v
  obtain ⟨p⟩ := hR (parentVertex B u) (parentVertex B v)
  exact (vertex_to_root B R attach hB r u).trans
    ((root_walk_reachable B R attach hB r p).trans (vertex_to_root B R attach hB r v).symm)

end KroneckerGluedSupportConnected
end

section

set_option autoImplicit false
namespace KroneckerGluedSupportTree
open SimpleGraph KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedSupportGraph KroneckerGluedSupportConnected KroneckerBipartiteIncidence
open KroneckerIncidenceDivergence KroneckerTreeFlowUniqueness KroneckerGluedLinearRepresentation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem connector_neighbor_count {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (i : I) : Fintype.card {t // GlueEdge B R attach (.inl i) t}=Fintype.card {j // R i j} := by
  classical
  simp only [Fintype.card_subtype,Finset.card_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  simp only [glue_edge_connector_iff]
  by_cases h : R i j
  · simp [h]
  · simp [h]

theorem internal_neighbor_count {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (j : J) (s : (B j).Source) :
    Fintype.card {t // GlueEdge B R attach (.inr ⟨j,s⟩) t}=
      Fintype.card {t // linearSupport (B j) s t} := by
  classical
  simp only [Fintype.card_subtype,Finset.card_filter]
  rw [Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [glue_edge_internal_iff]
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro t _
    simp [glue_edge_internal_other B R attach (Ne.symm hk)]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem glued_incidence_edge_count {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink) :
    Fintype.card (Edge (GlueEdge B R attach))=
      Fintype.card (Edge R)+∑ j,Fintype.card (Edge (linearSupport (B j))) := by
  rw [incidence_edge_count,Fintype.sum_sum_type]
  simp only [connector_neighbor_count,Fintype.sum_sigma,internal_neighbor_count,
    incidence_edge_count]

theorem incidence_edgeFinset_count {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) : (incidenceGraph R).edgeFinset.card=Fintype.card (Edge R) := by
  classical
  have h := (incidenceGraph R).sum_degrees_eq_twice_card_edges
  rw [incidence_degree_sum,←incidence_edge_count] at h
  omega

theorem glued_vertex_count {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) :
    Fintype.card ((I ⊕ (Σ j,(B j).Source)) ⊕ (Σ j,(B j).Sink))=
      Fintype.card I+∑ j,Fintype.card ((B j).Source ⊕ (B j).Sink) := by
  simp [Fintype.card_sum,Fintype.card_sigma,Finset.sum_add_distrib,add_assoc]

/-- The edge count is proved for the actual assembled support, so repeated
attachment sinks do not introduce an unproved tree-substitution premise. -/
theorem glued_graph_tree {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hB : ∀ j,(supportGraph (B j)).IsTree) (hR : (incidenceGraph R).IsTree) :
    (gluedGraph B R attach).IsTree := by
  classical
  have hc := glued_graph_connected B R attach (fun j => (hB j).connected) hR.connected
  have hb : ∀ j,Fintype.card (Edge (linearSupport (B j)))+1=
      Fintype.card ((B j).Source ⊕ (B j).Sink) := fun j => tree_edge_count _ (hB j)
  have hsum := congrArg (fun f : J → ℕ => ∑ j,f j) (funext hb)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hsum
  have he := tree_edge_count R hR
  have hg := glued_incidence_edge_count B R attach
  have hv := glued_vertex_count (I:=I) B
  have hcard : (gluedGraph B R attach).edgeFinset.card+1=
      Fintype.card ((I ⊕ (Σ j,(B j).Source)) ⊕ (Σ j,(B j).Sink)) := by
    rw [gluedGraph,incidence_edgeFinset_count]
    simp only [Fintype.card_sum] at he
    omega
  apply isTree_iff_connected_and_card.mpr
  refine ⟨hc,?_⟩
  simpa only [Nat.card_eq_fintype_card,←edgeFinset_card] using hcard

theorem glued_nonzero_support_tree {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hB : ∀ j,(supportGraph (B j)).IsTree) (hR : (incidenceGraph R).IsTree) :
    (supportGraph (gluedBlock B R attach)).IsTree := by
  rw [glued_support_graph]
  exact glued_graph_tree B R attach hB hR

end KroneckerGluedSupportTree
end

