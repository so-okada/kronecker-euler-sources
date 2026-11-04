import KroneckerManuscriptBlockStatements
import KroneckerManuscriptEulerForms

/-! Dimensions, stability and generation are separate contracts. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
namespace KroneckerSplitReflectedLemmas
open Module KroneckerLinearCoverBlocks KroneckerGluedSubrepEquivalence
open KroneckerSaturatedBlockData KroneckerRetainedBlockSupport KroneckerCoverTitsForm
open KroneckerSparseBlockQuiver KroneckerManuscriptBlockStatements

theorem dimensions (T : SaturatedBlockData) :
    sourceDimension (supportedBlock T)=T.sources-1 ∧
    Fintype.card (supportedBlock T).Sink=T.sources ∧
    titsForm (supportedBlock T)=1 ∧
    (∀ i : (supportedBlock T).Sink, finrank ℂ (vertexSpace (supportedBlock T) (.inr i))=1) ∧
    (∀ j : (supportedBlock T).Source,
      (finrank ℂ ((supportedBlock T).Space j)=1 ∧
        (supportGraph (supportedBlock T)).degree (.inl j)=2) ∨
      (finrank ℂ ((supportedBlock T).Space j)=2 ∧
        (supportGraph (supportedBlock T)).degree (.inl j)=3)) := by
  have h := reflected_block_statement T
  refine ⟨h.1,h.2.1,h.2.2.1,?_,h.2.2.2.2.1⟩
  intro i
  change finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

theorem stable (T : SaturatedBlockData) : BlockKingStable (supportedBlock T) :=
  (reflected_block_statement T).2.2.2.1

theorem sinks_generated (T : SaturatedBlockData) :
    ∀ i : (supportedBlock T).Sink,
      ∃ j : (supportedBlock T).Source, Function.Surjective ((supportedBlock T).arrow j i) :=
  (reflected_block_statement T).2.2.2.2.2

end KroneckerSplitReflectedLemmas

#print axioms KroneckerSplitReflectedLemmas.dimensions
#print axioms KroneckerSplitReflectedLemmas.stable
#print axioms KroneckerSplitReflectedLemmas.sinks_generated
