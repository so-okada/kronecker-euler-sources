import KroneckerGluingKingWeight

set_option autoImplicit false
namespace KroneckerTreeGluingCriterion
open SimpleGraph KroneckerLinearCoverBlocks KroneckerBipartiteIncidence
open KroneckerGluingKingWeight KroneckerPositiveGluedStability KroneckerGluedCutStability
open KroneckerIncidenceDivergence KroneckerFlowEdgeExtension KroneckerSkeletonFlowExistence
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem tree_flow_stability_criterion {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hT : (incidenceGraph R).IsTree) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (hdef : ∀ j,PositiveDefect (B j))
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1)
    (f : Edge R → ℝ)
    (hf : FlowEquations (slopeParameter (I:=I) B) (fun j => sourceDimension (B j)) f) :
    KingStable B R attach ↔ ∀ e,0<f e := by
  have htotal := glued_total_dimension B R hT h3 hdim
  have hoff := extend_off_edge f
  have hneigh : ∀ i,∃ j,R i j := by
    intro i
    have hn : Nonempty {j // R i j} := Fintype.card_pos_iff.mp (by rw [h3]; omega)
    obtain ⟨j,hj⟩ := hn
    exact ⟨j,hj⟩
  rw [king_stable_iff_normalized B R attach htotal]
  constructor
  · intro hs e
    have hp := stability_implies_positive_flows B R attach hT hdim (extendFlow f) hoff
      (slopeParameter (I:=I) B) hf.1 hf.2 hs e.1.1 e.1.2 e.2
    simpa [extendFlow,e.2] using hp
  · intro hpos
    have hp : ∀ i j,R i j → 0<extendFlow f i j := by
      intro i j hij
      simpa [extendFlow,hij] using hpos ⟨(i,j),hij⟩
    have hn : ∀ i j,0≤extendFlow f i j := by
      intro i j
      by_cases hij : R i j
      · exact (hp i j hij).le
      · simp [extendFlow,hij]
    exact positive_flows_imply_stability B R attach hT.connected hneigh hdef hdim
      (extendFlow f) hn hp hoff (slopeParameter (I:=I) B)
      (by unfold slopeParameter; positivity) hf.1 hf.2

/-- Existence, uniqueness and the exact King-stability criterion are internal
theorems for the constructed block-and-connector linear system. -/
theorem unique_flow_and_gluing_criterion {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hT : (incidenceGraph R).IsTree) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (hdef : ∀ j,PositiveDefect (B j))
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1) :
    ∃! f : Edge R → ℝ,
      FlowEquations (slopeParameter (I:=I) B) (fun j => sourceDimension (B j)) f ∧
      (KingStable B R attach ↔ ∀ e,0<f e) := by
  obtain ⟨f,hf,hu⟩ := unique_skeleton_flow R hT h3 (slopeParameter (I:=I) B)
    (fun j => sourceDimension (B j)) (slope_parameter_balance B)
  exact ⟨f,⟨hf,tree_flow_stability_criterion B R attach hT h3 hdef hdim f hf⟩,
    fun g hg => hu g hg.1⟩

end KroneckerTreeGluingCriterion
