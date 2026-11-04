import KroneckerSourceAttachmentNeighbors
import KroneckerGluedSupportTree
import KroneckerUnrootedColoredRigidity

set_option autoImplicit false
namespace KroneckerSourceAttachmentTree
open SimpleGraph KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerColoredSourceAttachment KroneckerSourceAttachmentConnected
open KroneckerSourceAttachmentNeighbors KroneckerUnrootedColoredRigidity
open KroneckerGluedSupportTree KroneckerIncidenceDivergence
open KroneckerTreeFlowUniqueness
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))

theorem attachment_edge_count :
    Fintype.card (Edge (Incidence (sourceAttachment T r c hc hr)))=
      Fintype.card K+∑ k,Fintype.card (Edge (Incidence (T k))) := by
  rw [incidence_edge_count,Fintype.sum_option]
  simp only [attachment_root_degree,Fintype.sum_sigma,attachment_internal_degree,
    incidence_edge_count]

/-- The assembly of any finite family of actual trees is an actual tree; no assembly premise remains. -/
theorem source_attachment_tree (hT : ∀ k,(incidenceGraph (Incidence (T k))).IsTree) :
    (incidenceGraph (Incidence (sourceAttachment T r c hc hr))).IsTree := by
  classical
  apply isTree_iff_connected_and_card.mpr
  refine ⟨source_attachment_connected T r c hc hr (fun k => (hT k).connected),?_⟩
  have hs : (∑ k,Fintype.card (Edge (Incidence (T k))))+Fintype.card K=
      (∑ k,Fintype.card (I k))+(∑ k,Fintype.card (J k)) := by
    calc
      _ = ∑ k,(Fintype.card (Edge (Incidence (T k)))+1) := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
      _ = ∑ k,(Fintype.card (I k)+Fintype.card (J k)) :=
        Finset.sum_congr rfl (fun k _ => tree_incidence_card (Incidence (T k)) (hT k))
      _ = _ := Finset.sum_add_distrib
  rw [Nat.card_eq_fintype_card,←edgeFinset_card,incidence_edgeFinset_count,
    attachment_edge_count,Nat.card_eq_fintype_card,Fintype.card_sum,
    Fintype.card_option,Fintype.card_sigma,Fintype.card_sigma]
  omega

end KroneckerSourceAttachmentTree
