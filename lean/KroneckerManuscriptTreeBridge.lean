import KroneckerManuscriptRevision
import KroneckerIntermediateLemmas

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace KroneckerManuscriptQuiverDefinitions.Graph.SourceTrivalentTree
open KroneckerReflectionKernel KroneckerReflectedSubrepresentations
attribute [local instance] Classical.propDecidable

def reflectedQuiver (T : Graph.SourceTrivalentTree) : Quiver where
  Vert := T.Sink ⊕ T.Source
  Edge := {p : T.Sink × T.Source // T.incidence p.2 p.1}
  delta e := (Sum.inl e.val.1, Sum.inr e.val.2)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Zero extension of the manuscript's reflected representation to leaf sinks of T. -/
def zeroSum (T : Graph.SourceTrivalentTree) : Representation T.reflectedQuiver where
  Space v := Sum.elim (fun j => Kernel {i // T.incidence i j}) (fun _ => ℂ) v
  spaceAddCommGroup v := by cases v <;> dsimp only [Sum.elim] <;> infer_instance
  spaceModule v := by cases v <;> dsimp only [Sum.elim] <;> infer_instance
  spaceFiniteDimensional v := by cases v <;> dsimp only [Sum.elim] <;> infer_instance
  arrow e := projection (ι := {i // T.incidence i e.val.1}) ⟨e.val.2,e.property⟩

def toReflectedSubrep (T : Graph.SourceTrivalentTree) (W : T.zeroSum.SubRep) :
    ReflectedSubrep T.incidence where
  source j := W.space (Sum.inl j)
  sink i := W.space (Sum.inr i)
  invariant j i h x hx := W.invariant ⟨(j,i),h⟩ x hx

theorem source_degree_card (T : Graph.SourceTrivalentTree) (i : T.Source) :
    Fintype.card {j // T.incidence i j} = 3 := by
  simpa only [Nat.card_eq_fintype_card] using T.source_degree i

/-- Lemma 7.22: all vertexwise subspaces are quantified, not only coordinate subspaces. -/
theorem source_dimension_bound (T : Graph.SourceTrivalentTree) (W : T.zeroSum.SubRep)
    (hn : 0 < (∑ j, Module.finrank ℂ (W.space (Sum.inl j))) +
      (∑ i, Module.finrank ℂ (W.space (Sum.inr i)))) :
    1 ≤ ∑ i, Module.finrank ℂ (W.space (Sum.inr i)) ∧
      (∑ j, Module.finrank ℂ (W.space (Sum.inl j))) + 1 ≤
        ∑ i, Module.finrank ℂ (W.space (Sum.inr i)) :=
  KroneckerIntermediateLemmas.zero_sum_source_bound T.tree T.source_degree_card
    (T.toReflectedSubrep W) hn

theorem coordinate_vanishes (T : Graph.SourceTrivalentTree) (W : T.zeroSum.SubRep)
    (j : T.Sink) (x : (T.toReflectedSubrep W).source j) (i : {i // T.incidence i j})
    (hi : i ∉ selectedCoordinates T.incidence (selected (T.toReflectedSubrep W)) j) :
    (x.val : {i // T.incidence i j} → ℂ) i = 0 :=
  subrep_coordinate_support (T.toReflectedSubrep W) j x i hi

theorem local_dimension_bound (T : Graph.SourceTrivalentTree) (W : T.zeroSum.SubRep) (j : T.Sink) :
    Module.finrank ℂ (W.space (Sum.inl j)) ≤
      KroneckerReflectionCapacity.selectedDegree T.incidence (selected (T.toReflectedSubrep W)) j - 1 :=
  subrep_source_capacity (T.toReflectedSubrep W) j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem leaf_source_zero_dimension (T : Graph.SourceTrivalentTree) (W : T.zeroSum.SubRep)
    (j : T.Sink) (hj : Fintype.card {i // T.incidence i j} = 1) :
    Module.finrank ℂ (W.space (Sum.inl j)) = 0 := by
  have h := (W.space (Sum.inl j)).finrank_le
  have hk := KroneckerSupportedReflectionKernel.kernel_dimension_all {i // T.incidence i j}
  change Module.finrank ℂ (W.space (Sum.inl j)) ≤ Module.finrank ℂ (Kernel {i // T.incidence i j}) at h
  rw [hk, hj] at h
  omega
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem omitted_source_zero_dimension (T : Graph.SourceTrivalentTree) (W : T.zeroSum.SubRep)
    (j : T.Sink) (hj : Fintype.card {i // T.incidence i j} < 2) :
    Module.finrank ℂ (W.space (Sum.inl j)) = 0 := by
  have h := (W.space (Sum.inl j)).finrank_le
  change Module.finrank ℂ (W.space (Sum.inl j)) ≤ Module.finrank ℂ (Kernel {i // T.incidence i j}) at h
  rw [KroneckerSupportedReflectionKernel.kernel_dimension_all] at h
  omega

theorem selected_count (T : Graph.SourceTrivalentTree) (W : T.zeroSum.SubRep) :
    (∑ i, Module.finrank ℂ (W.space (Sum.inr i))) = (selected (T.toReflectedSubrep W)).card :=
  selected_sink_dimension (T.toReflectedSubrep W)

theorem induced_forest (T : Graph.SourceTrivalentTree) (s : Finset T.Source) :
    (KroneckerBipartiteIncidence.incidenceGraph
      (KroneckerSelectedIncidenceForest.selectedRelation T.incidence s)).IsAcyclic :=
  KroneckerSelectedIncidenceForest.selected_acyclic T.incidence s T.tree.isAcyclic

theorem source_vertex_degree (T : Graph.SourceTrivalentTree) (i : T.Source) :
    (KroneckerBipartiteIncidence.incidenceGraph T.incidence).degree (Sum.inl i) = 3 := by
  rw [KroneckerBipartiteIncidence.left_degree]
  exact T.source_degree_card i

theorem total_source_dimension (T : Graph.SourceTrivalentTree) [Nonempty T.Source] [Nonempty T.Sink] :
    (∑ j, Module.finrank ℂ (Kernel {i // T.incidence i j})) + 1 = Fintype.card T.Source :=
  KroneckerSaturatedTreeDimensions.reflected_source_dimension T.incidence T.tree T.source_degree_card

end KroneckerManuscriptQuiverDefinitions.Graph.SourceTrivalentTree
