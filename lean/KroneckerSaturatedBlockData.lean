import KroneckerTreeGluingCriterion
import KroneckerCoverTitsForm
import KroneckerGluedProperColoring

set_option autoImplicit false
namespace KroneckerSaturatedBlockData
open SimpleGraph KroneckerBipartiteIncidence KroneckerSaturatedTreeDimensions
open KroneckerProperColoredReflection KroneckerReflectedLinearBlock KroneckerLinearCoverBlocks
open KroneckerRetainedReflectionKernels KroneckerRetainedSubrepresentations
open KroneckerRetainedBlockSupport KroneckerGluedSubrepEquivalence KroneckerCoverTitsForm
attribute [local instance] Classical.propDecidable

structure SaturatedBlockData where
  sources : ℕ
  sinks : ℕ
  sources_ge_two : 2≤sources
  incidence : Fin sources → Fin sinks → Prop
  tree : (incidenceGraph incidence).IsTree
  saturated : ∀ i,Fintype.card {j // incidence i j}=3
  coloring : ProperColoring incidence

noncomputable def block (T : SaturatedBlockData) : LinearCoverBlock := reflectedBlock T.incidence

theorem original_sink_count (T : SaturatedBlockData) : T.sinks=2*T.sources+1 := by
  simpa using saturated_tree_sink_count T.incidence T.tree T.saturated

theorem reflected_block_dimensions (T : SaturatedBlockData) :
    sourceDimension (block T)=T.sources-1 ∧ Fintype.card (block T).Sink=T.sources := by
  have hn := T.sources_ge_two
  have hm := original_sink_count T
  let : Nonempty (Fin T.sources) := ⟨⟨0,by omega⟩⟩
  let : Nonempty (Fin T.sinks) := ⟨⟨0,by omega⟩⟩
  constructor
  · simpa [block] using reflected_total_source T.incidence T.tree T.saturated
  · exact Fintype.card_fin T.sources

theorem reflected_block_dimension_gap (T : SaturatedBlockData) :
    Fintype.card (block T).Sink=sourceDimension (block T)+1 := by
  obtain ⟨ha,hb⟩ := reflected_block_dimensions T
  have hn := T.sources_ge_two
  omega

theorem reflected_block_defect (T : SaturatedBlockData) : PositiveDefect (block T) :=
  reflected_positive_defect T.tree T.saturated



noncomputable def supportedBlock (T : SaturatedBlockData) : LinearCoverBlock := retainedBlock T.incidence

noncomputable def supportedColoring (T : SaturatedBlockData) :
    ProperColoring (linearSupport (supportedBlock T)) := retainedColoring T.coloring

theorem supported_block_dimensions (T : SaturatedBlockData) :
    sourceDimension (supportedBlock T)=T.sources-1 ∧ Fintype.card (supportedBlock T).Sink=T.sources := by
  constructor
  · rw [supportedBlock,retained_total_dimension]
    exact (reflected_block_dimensions T).1
  · exact Fintype.card_fin T.sources

theorem supported_block_defect (T : SaturatedBlockData) : PositiveDefect (supportedBlock T) :=
  (retained_defect_iff T.incidence).mpr (reflected_block_defect T)


theorem supported_block_tree (T : SaturatedBlockData) : (supportGraph (supportedBlock T)).IsTree := by
  have hn := T.sources_ge_two
  have hm := original_sink_count T
  let : Nonempty (Fin T.sources) := ⟨⟨0,by omega⟩⟩
  let : Nonempty (Fin T.sinks) := ⟨⟨0,by omega⟩⟩
  exact retained_nonzero_support_tree T.incidence T.tree

theorem supported_block_tits (T : SaturatedBlockData) : titsForm (supportedBlock T)=1 := by
  have hn := T.sources_ge_two
  have hm := original_sink_count T
  let : Nonempty (Fin T.sources) := ⟨⟨0,by omega⟩⟩
  let : Nonempty (Fin T.sinks) := ⟨⟨0,by omega⟩⟩
  exact retained_tits_form T.incidence T.tree T.saturated


/-- The fully retained construction supplies the tree, Tits form and exact
stability criterion for an actual global representation. -/
theorem supported_tree_gluing {I J : Type} [Fintype I] [Fintype J]
    (T : J → SaturatedBlockData) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (supportedBlock (T j)).Sink)
    (hT : (incidenceGraph R).IsTree) (h3 : ∀ i,Fintype.card {j // R i j}=3) :
    (supportGraph (KroneckerGluedLinearRepresentation.gluedBlock
      (fun j => supportedBlock (T j)) R attach)).IsTree ∧
    titsForm (KroneckerGluedLinearRepresentation.gluedBlock
      (fun j => supportedBlock (T j)) R attach)=1 ∧
    ∃! f : KroneckerIncidenceDivergence.Edge R → ℝ,
      KroneckerSkeletonFlowExistence.FlowEquations
        (KroneckerGluingKingWeight.slopeParameter (I:=I) (fun j => supportedBlock (T j)))
        (fun j => sourceDimension (supportedBlock (T j))) f ∧
      (BlockKingStable (KroneckerGluedLinearRepresentation.gluedBlock
        (fun j => supportedBlock (T j)) R attach) ↔ ∀ e,0<f e) := by
  refine ⟨KroneckerGluedSupportTree.glued_nonzero_support_tree _ _ _
    (fun j => supported_block_tree (T j)) hT,
    glued_tits_form_one _ _ _ hT h3 (fun j => supported_block_tits (T j)),?_⟩
  have hdim : ∀ j,Fintype.card (supportedBlock (T j)).Sink=sourceDimension (supportedBlock (T j))+1 := by
    intro j
    obtain ⟨ha,hb⟩ := supported_block_dimensions (T j)
    have hn := (T j).sources_ge_two
    omega
  have h := KroneckerTreeGluingCriterion.unique_flow_and_gluing_criterion
    (fun j => supportedBlock (T j)) R attach hT h3 (fun j => supported_block_defect (T j)) hdim
  simpa only [global_stability_iff] using h

end KroneckerSaturatedBlockData
