import KroneckerRepairGeometry
import KroneckerManuscriptTarget
import KroneckerReadableMain

/-! Kernel checks for the deterministic-exchange correspondence and its
seven-interface boundary. The finite example separates validity from canonicity. -/
set_option autoImplicit false
namespace KroneckerExactExchangeAudit
open KroneckerStack KroneckerDebtUnits KroneckerVerticalRepair
open KroneckerCanonicalExchange

/-- Successful execution alone does not force the largest admissible repair grade. -/
theorem nonunique_valid_repair :
    Connected 3 [.H 2,.H 1,.V 0,.H 0,.V 1,.V 0] 1 ∧
    RepairAt 1 [.H 0,.V 1,.V 0] [.H 0,.V 1,.V 0] 1 1 ∧
    RepairAt 1 [.H 0,.V 1,.V 0] [.H 0,.V 0,.V 0] 1 0 ∧
    Connected 3 [.H 2,.V 0,.H 1,.H 0,.V 1,.V 0] 1 ∧
    Connected 3 [.H 2,.V 0,.H 1,.H 0,.V 0,.V 0] 2 ∧
    repairDelta true 1 [.H 2,.H 1,.V 0,.H 0,.V 1,.V 0] = 0 := by
  refine ⟨by unfold Connected; decide,.there (.H 0) (.here [.V 0] 1 1 (by decide)),
    .there (.H 0) (.here [.V 0] 1 0 (by decide)),
    by unfold Connected; decide,by unfold Connected; decide,by decide⟩

end KroneckerExactExchangeAudit

#print axioms KroneckerCanonicalExchange.coloredRepair_append
#print axioms KroneckerCanonicalExchange.exact_delta
#print axioms KroneckerCanonicalExchange.exchange_context
#print axioms KroneckerCanonicalExchange.exchange_word
#print axioms KroneckerCanonicalExchange.exchange_word_exact
#print axioms KroneckerCanonicalExchange.left_delta
#print axioms KroneckerCanonicalExchange.lower
#print axioms KroneckerCanonicalExchange.markedIndex_append_of_some
#print axioms KroneckerCanonicalExchange.marked_baseline_repair_exact
#print axioms KroneckerCanonicalExchange.modify_append
#print axioms KroneckerCanonicalExchange.positiveDelta
#print axioms KroneckerCanonicalExchange.positiveDelta_append
#print axioms KroneckerCanonicalExchange.positive_reduction_formula
#print axioms KroneckerCanonicalExchange.positive_right_exact
#print axioms KroneckerCanonicalExchange.repairDelta
#print axioms KroneckerCanonicalExchange.repairDelta_context
#print axioms KroneckerCanonicalExchange.repairDelta_left
#print axioms KroneckerCanonicalExchange.repairDelta_right
#print axioms KroneckerCanonicalExchange.repairPosition
#print axioms KroneckerCanonicalExchange.repairPosition_right
#print axioms KroneckerCanonicalExchange.repairWord
#print axioms KroneckerCanonicalExchange.repair_modify
#print axioms KroneckerCanonicalExchange.right_colored_exact
#print axioms KroneckerCanonicalExchange.right_node_exact
#print axioms KroneckerCanonicalExchange.swapEdges
#print axioms KroneckerCanonicalExchange.swapEdges_pair
#print axioms KroneckerCanonicalExchange.unit_execute_credit
#print axioms KroneckerCanonicalExchange.wrapped_right_exact
#print axioms KroneckerExactExchangeAudit.nonunique_valid_repair
#print axioms KroneckerExchangeColorCorrespondence.Rel
#print axioms KroneckerExchangeColorCorrespondence.color_rule
#print axioms KroneckerExchangeColorCorrespondence.copy
#print axioms KroneckerExchangeColorCorrespondence.copy_eq_tau
#print axioms KroneckerExchangeColorCorrespondence.edges_get
#print axioms KroneckerExchangeColorCorrespondence.exchange_code_at
#print axioms KroneckerExchangeColorCorrespondence.exchange_colors_eq_Recol
#print axioms KroneckerExchangeColorCorrespondence.exchange_exact
#print axioms KroneckerExchangeColorCorrespondence.exchange_pair_bound
#print axioms KroneckerExchangeColorCorrespondence.exchange_rel
#print axioms KroneckerExchangeColorCorrespondence.exchange_rel_at
#print axioms KroneckerExchangeColorCorrespondence.geometric_recol_at
#print axioms KroneckerExchangeColorCorrespondence.geometric_relation
#print axioms KroneckerExchangeColorCorrespondence.palette
#print axioms KroneckerExchangeColorCorrespondence.palette_color
#print axioms KroneckerExchangeColorCorrespondence.palette_grade
#print axioms KroneckerExchangeColorCorrespondence.recol_from_rule
#print axioms KroneckerExchangeColorCorrespondence.rel_refl
#print axioms KroneckerExchangeColorCorrespondence.repair_original_palette
#print axioms KroneckerExchangeColorCorrespondence.repair_rel
#print axioms KroneckerExchangeColorCorrespondence.swapPos_succ
#print axioms KroneckerExchangeColorCorrespondence.swapSeq
#print axioms KroneckerExchangeColorCorrespondence.swapSeq_get
#print axioms KroneckerExchangeColorCorrespondence.swapSeq_pair
#print axioms KroneckerExchangeRepairCorrespondence.RepGr
#print axioms KroneckerExchangeRepairCorrespondence.RepGr_word
#print axioms KroneckerExchangeRepairCorrespondence.exchange_eq_RepGr
#print axioms KroneckerExchangeRepairCorrespondence.geometric_exchange_word
#print axioms KroneckerExchangeRepairCorrespondence.geometric_reduction_eq
#print axioms KroneckerExchangeRepairCorrespondence.position
#print axioms KroneckerExchangeRepairCorrespondence.reduction
#print axioms KroneckerExchangeRepairCorrespondence.sourceGrading
#print axioms KroneckerExchangeRepairCorrespondence.uncolor_edges
#print axioms KroneckerExchangeTransport.Pair
#print axioms KroneckerExchangeTransport.Pair.directions
#print axioms KroneckerExchangeTransport.Pair.indices
#print axioms KroneckerExchangeTransport.Pair.length_eq
#print axioms KroneckerExchangeTransport.Pair.ordinal
#print axioms KroneckerExchangeTransport.Pair.swapWord
#print axioms KroneckerExchangeTransport.Pair.swapWord_eq_swapEdges
#print axioms KroneckerExchangeTransport.Pair.swapWord_pair
#print axioms KroneckerExchangeTransport.Pair.tau
#print axioms KroneckerExchangeTransport.Pair.transported
#print axioms KroneckerExchangeTransport.Pair.transported_word
#print axioms KroneckerExchangeTransport.Pair.transported_word_exact
#print axioms KroneckerExchangeTransport.shellPair
#print axioms KroneckerExchangeTransport.shell_pair_position
#print axioms KroneckerExchangeTransport.swapPos
#print axioms KroneckerExchangeTransport.swapPos_lt
#print axioms KroneckerExchangeTransport.tau
#print axioms KroneckerExchangeTransport.transportedShell
#print axioms KroneckerExchangeTransport.transported_shell_word
#print axioms KroneckerLiteralRepair.left
#print axioms KroneckerLiteralRepair.literalDelta
#print axioms KroneckerLiteralRepair.positive_formula
#print axioms KroneckerLiteralRepair.reduction_eq
#print axioms KroneckerLiteralRepair.right_positive
#print axioms KroneckerLiteralRepair.right_zero
#print axioms KroneckerReadableMain.semantic_main
#print axioms KroneckerRepairGeometry.J
#print axioms KroneckerRepairGeometry.RepGr_connected_bound
#print axioms KroneckerRepairGeometry.candidateOrdinals
#print axioms KroneckerRepairGeometry.colored_input
#print axioms KroneckerRepairGeometry.geometric_index_least
#print axioms KroneckerRepairGeometry.geometric_position_bound
#print axioms KroneckerRepairGeometry.geometric_position_ordinal
#print axioms KroneckerRepairGeometry.geometric_recovery_code
#print axioms KroneckerRepairGeometry.gradedWord_boundary
#print axioms KroneckerRepairGeometry.position_vertical_ordinal
#print axioms KroneckerRepairGeometry.positive_index_least
#print axioms KroneckerRepairGeometry.selectedEdge
#print axioms KroneckerRepairGeometry.verticalCount_geometric
#print axioms KroneckerRepairGeometry.wordList_credit
#print axioms KroneckerWrappedExchangeMap.exchangeMap_repairWord
