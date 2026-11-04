import KroneckerManuscriptBranchCounting
import KroneckerFiniteChainInputs
import KroneckerChainRepresentativeStability

/-! The named chain's leaf and degree-two lists in the manuscript graph model. -/
noncomputable section
set_option autoImplicit false
open Classical

namespace KroneckerManuscriptQuiverDefinitions.Graph

/-- For a simple graph, its incident edges are in bijection with its neighbors. -/
def simpleIncidentEquivNeighbor {V : Type} (G : SimpleGraph V) (v : V) :
    {e : (ofSimpleGraph G).Edge // ∃ u, u ≠ v ∧ (ofSimpleGraph G).boundary e = s(v,u)} ≃
      {u : V // G.Adj v u} where
  toFun e := by
    let u := Classical.choose e.property
    have h := Classical.choose_spec e.property
    have he : e.val.val = s(v,u) := h.2
    refine ⟨u, G.mem_edgeSet.mp ?_⟩
    rw [← he]
    exact e.val.property
  invFun u := ⟨⟨s(v,u.val), G.mem_edgeSet.mpr u.property⟩,
    u.val, (G.ne_of_adj u.property).symm, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec e.property).2.symm
  right_inv u := by
    apply Subtype.ext
    have he := (Classical.choose_spec
      (show ∃ w, w ≠ v ∧ (ofSimpleGraph G).boundary
        ⟨s(v,u.val), G.mem_edgeSet.mpr u.property⟩ = s(v,w) from
          ⟨u.val, (G.ne_of_adj u.property).symm, rfl⟩)).2
    change s(v,u.val) = s(v,Classical.choose _) at he
    rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨_, h⟩
    · exact h.symm
    · exact False.elim ((G.ne_of_adj u.property) h.symm)

theorem simple_degree_cardinal {V : Type} (G : SimpleGraph V) (v : V) :
    (ofSimpleGraph G).degree v = Cardinal.mk {u : V // G.Adj v u} := by
  let : IsEmpty {e : (ofSimpleGraph G).Edge // (ofSimpleGraph G).boundary e = s(v,v)} :=
    ⟨fun e => by
      have h : s(v,v) ∈ G.edgeSet := by rw [← e.property]; exact e.val.property
      exact G.loopless.irrefl v (G.mem_edgeSet.mp h)⟩
  unfold degree
  have hinc : Cardinal.mk {e : (ofSimpleGraph G).Edge //
      ∃ u, u ≠ v ∧ (ofSimpleGraph G).boundary e = s(v,u)} =
      Cardinal.mk {u : V // G.Adj v u} := Cardinal.mk_congr (simpleIncidentEquivNeighbor G v)
  have hloop : Cardinal.mk {e : (ofSimpleGraph G).Edge //
      (ofSimpleGraph G).boundary e = s(v,v)} = 0 := Cardinal.mk_eq_zero _
  calc
    _ = Cardinal.mk {e : (ofSimpleGraph G).Edge //
          ∃ u, u ≠ v ∧ (ofSimpleGraph G).boundary e = s(v,u)} +
        2 * Cardinal.mk {e : (ofSimpleGraph G).Edge //
          (ofSimpleGraph G).boundary e = s(v,v)} := rfl
    _ = Cardinal.mk {u : V // G.Adj v u} + 2 * 0 := congrArg₂ (fun x y : Cardinal => x + 2*y) hinc hloop
    _ = _ := by simp

theorem simple_degree_fintype {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (ofSimpleGraph G).degree v = (G.degree v : Cardinal) := by
  rw [simple_degree_cardinal, Cardinal.mk_fintype]
  exact congrArg (fun n : ℕ => (n : Cardinal)) (G.card_neighborSet_eq_degree v)

end KroneckerManuscriptQuiverDefinitions.Graph

namespace KroneckerChainLeafCorrespondence
open KroneckerManuscriptQuiverDefinitions KroneckerChainIncidence
open KroneckerChainBlockNeighbors KroneckerChainLeafClassification

/-- The degree-one sinks are exactly the two axial endpoints and the middle
sinks, including all three sinks when the chain has one source. -/
theorem named_sink_leaf_iff (n : ℕ) (j : Block n) :
    (LabeledChain.LSTrivCh n).Leaf (Sum.inr j) ↔
      j = leftBlock n ∨ j = rightBlock n ∨ ∃ i, j = middleBlock i := by
  classical
  have hd : (LabeledChain.LSTrivCh n).degree (Sum.inr j) =
      (Fintype.card {i // incidence i j} : Cardinal) := by
    change (Graph.ofSimpleGraph (KroneckerBipartiteIncidence.incidenceGraph (@incidence n))).degree
      (Sum.inr j) = _
    rw [Graph.simple_degree_fintype]
    rw [KroneckerBipartiteIncidence.right_degree]
  change (LabeledChain.LSTrivCh n).degree (Sum.inr j) = 1 ↔ _
  rw [hd]
  have hc : ((Fintype.card {i // incidence i j} : ℕ) : Cardinal) = 1 ↔
      ∃ i, LeafAt i j := by
    simp only [Nat.cast_eq_one]
    rw [Fintype.card_eq_one_iff]
    constructor
    · rintro ⟨⟨i,hi⟩, h⟩
      exact ⟨i,hi,fun k hk => congrArg Subtype.val (h ⟨k,hk⟩)⟩
    · rintro ⟨i,hi,hu⟩
      refine ⟨⟨i,hi⟩, ?_⟩
      intro k
      exact Subtype.ext (hu k.val k.property)
  rw [hc]
  simp only [leaf_at_iff]
  constructor
  · rintro ⟨i, h | ⟨_,h⟩ | ⟨_,h⟩⟩
    · exact Or.inr (Or.inr ⟨i,h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rintro (h | h | ⟨i,h⟩)
    · exact ⟨0, Or.inr (Or.inl ⟨rfl,h⟩)⟩
    · exact ⟨Fin.last n, Or.inr (Or.inr ⟨rfl,h⟩)⟩
    · exact ⟨i,Or.inl h⟩

/-- The internal axial sinks have degree two. -/
theorem named_internal_degree (n : ℕ) (t : Fin n) :
    (LabeledChain.LSTrivCh n).degree (Sum.inr (internalBlock t)) = 2 := by
  classical
  change (Graph.ofSimpleGraph (KroneckerBipartiteIncidence.incidenceGraph (@incidence n))).degree
    (Sum.inr (internalBlock t)) = 2
  rw [Graph.simple_degree_fintype]
  rw [KroneckerBipartiteIncidence.right_degree, internal_degree]
  norm_num

theorem named_sink_degree_two_iff (n : ℕ) (j : Block n) :
    (LabeledChain.LSTrivCh n).degree (Sum.inr j) = 2 ↔
      ∃ t : Fin n, j = internalBlock t := by
  constructor
  · intro hd
    rcases block_cases j with hl | hr | ⟨i,hm⟩ | ⟨t,hi⟩
    · have hf := (named_sink_leaf_iff n j).mpr (Or.inl hl)
      change (LabeledChain.LSTrivCh n).degree (Sum.inr j) = 1 at hf
      rw [hf] at hd
      norm_num at hd
    · have hf := (named_sink_leaf_iff n j).mpr (Or.inr (Or.inl hr))
      change (LabeledChain.LSTrivCh n).degree (Sum.inr j) = 1 at hf
      rw [hf] at hd
      norm_num at hd
    · have hf := (named_sink_leaf_iff n j).mpr (Or.inr (Or.inr ⟨i,hm⟩))
      change (LabeledChain.LSTrivCh n).degree (Sum.inr j) = 1 at hf
      rw [hf] at hd
      norm_num at hd
    · exact ⟨t,hi⟩
  · rintro ⟨t,rfl⟩
    exact named_internal_degree n t

/-- Each source has degree three in the actual graph. -/
theorem named_source_degree (n : ℕ) (i : Connector n) :
    (LabeledChain.LSTrivCh n).degree (Sum.inl i) = 3 := by
  classical
  change (Graph.ofSimpleGraph (KroneckerBipartiteIncidence.incidenceGraph (@incidence n))).degree
    (Sum.inl i) = 3
  rw [Graph.simple_degree_fintype]
  rw [KroneckerBipartiteIncidence.left_degree, connector_degree]
  norm_num

theorem named_chain_tree (n : ℕ) : (LabeledChain.LSTrivCh n).IsTree := by
  let R := KroneckerBipartiteIncidence.incidenceGraph (@incidence n)
  change (Graph.ofSimpleGraph R).IsTree
  refine ⟨Graph.ofSimpleGraph_simple R, ?_⟩
  rw [Graph.simpleGraph_ofSimpleGraph]
  exact KroneckerChainSkeletonTree.chain_tree n

/-- For c=1, every one of the three sinks is a leaf. -/
theorem one_source_all_sinks_are_leaves (j : Block 0) :
    (LabeledChain.LSTrivCh 0).Leaf (Sum.inr j) := by
  apply (named_sink_leaf_iff 0 j).mpr
  rcases block_cases j with hl | hr | ⟨i,hm⟩ | ⟨t,hi⟩
  · exact Or.inl hl
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr ⟨i,hm⟩)
  · exact Fin.elim0 t

end KroneckerChainLeafCorrespondence

set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.Graph.simple_degree_cardinal
set_option pp.fullNames true in
#print axioms KroneckerChainLeafCorrespondence.named_sink_leaf_iff
set_option pp.fullNames true in
#print axioms KroneckerChainLeafCorrespondence.named_internal_degree
set_option pp.fullNames true in
#print axioms KroneckerChainLeafCorrespondence.named_source_degree
set_option pp.fullNames true in
#print axioms KroneckerChainLeafCorrespondence.named_sink_degree_two_iff
set_option pp.fullNames true in
#print axioms KroneckerChainLeafCorrespondence.named_chain_tree
set_option pp.fullNames true in
#print axioms KroneckerChainLeafCorrespondence.one_source_all_sinks_are_leaves
