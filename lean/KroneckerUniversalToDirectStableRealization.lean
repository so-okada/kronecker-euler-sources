import KroneckerColoredCoverPairDictionary
import KroneckerBoundedWordEulerRealization

/- Original module: KroneckerUniversalStableNormalization -/
section
/-! A nonzero actual stable universal-cover representation admits an actual
deck pullback whose entire support lies in the word ball of radius its total
dimension. Both source and sink roots are allowed. The representative retains
its matrices by deck pullback, the original dimension vector, and stability. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalStableNormalization
open KroneckerReducedColorWords KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportStability KroneckerUniversalWordBaseProjection
open KroneckerUniversalDeckBaseDimensions KroneckerConnectedDeckNormalization
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_normalized_pull (S : SupportedRepresentation coloredCoverQuiver) (hS : S.1 ≠ 0)
    (θ : Fin 2 → ℤ) (hstable : FiniteSupportStable S.1 (θ ∘ baseVertex) S.2) :
    ∃ g : Deck, (deckPull g S).1 ≠ 0 ∧
      (deckPull g S).1.sum (fun _ k => k) = S.1.sum (fun _ k => k) ∧
      (deckPull g S).1.mapDomain baseVertex = S.1.mapDomain baseVertex ∧
      FiniteSupportStable (deckPull g S).1 (θ ∘ baseVertex) (deckPull g S).2 ∧
      ∀ w ∈ (deckPull g S).1.support, w.val.length ≤ S.1.sum (fun _ k => k) := by
  have hc := KroneckerColoredCoverPairDictionary.ambient_stable_support_preconnected_any S.1 _ S.2 hstable
  obtain ⟨e,⟨g,hg⟩,ht,hb⟩ := normalize_connected_dimensions S.1 (Finsupp.support_nonempty_iff.mpr hS) hc
  have he : (deckPull (Deck.symm g) S).1 = e := by
    ext w
    change S.1 (g.equiv.symm w) = e w
    exact (hg (g.equiv.symm w)).symm.trans (congrArg e (g.equiv.apply_symm_apply w))
  refine ⟨Deck.symm g,?_,?_,deckPull_original_dimension _ S,
    (deckPull_original_stable _ S θ).mpr hstable,?_⟩
  · exact (not_congr (KroneckerDirectSumStablePullback.pull_zero_iff (deckQuiverAuto (Deck.symm g)) S.1)).mpr hS
  · rw [he]
    exact ht
  · rw [he]
    exact hb

end KroneckerUniversalStableNormalization
end
end

/- Original module: KroneckerUniversalToDirectStableRealization -/
section
/-! The radius assumption is eliminated: EVERY nonzero universal stable
object of total at most B has a direct-sum stable realization at depth3B+1,
with exactly the same original dimension vector, total and self-Euler form.
The proof normalizes its actual representation by an even deck pullback. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalToDirectStableRealization
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability KroneckerFiniteSupportEulerTransport
open KroneckerUniversalStableNormalization KroneckerBoundedWordEulerRealization
attribute [local instance] Classical.decEq Classical.propDecidable


end KroneckerUniversalToDirectStableRealization
end
end
