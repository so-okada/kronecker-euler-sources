import KroneckerExactDirectSumNormalForm

/-! Universal colored deck pullbacks preserve the complete original two-
vertex dimension vector. This exact statement also covers zero and arbitrary
infinite ambient word sets; stability is stated for any original character. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalDeckBaseDimensions
open KroneckerReducedColorWords KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportStability KroneckerUniversalWordBaseProjection
attribute [local instance] Classical.decEq Classical.propDecidable

theorem deck_base (g : Deck) (w : Word) : baseVertex (g w) = baseVertex w :=
  Fin.ext (g.preserves_parity w)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem deckPull_original_dimension (g : Deck) (S : SupportedRepresentation coloredCoverQuiver) :
    (deckPull g S).1.mapDomain baseVertex = S.1.mapDomain baseVertex := by
  change (pullDimension (deckQuiverAuto g) S.1).mapDomain baseVertex = _
  rw [KroneckerAccumulatedDeckBaseDimensions.pullDimension_eq_mapDomain,← Finsupp.mapDomain_comp]
  congr 1
  funext w
  exact deck_base (Deck.symm g) w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem deckPull_original_stable (g : Deck) (S : SupportedRepresentation coloredCoverQuiver) (θ : Fin 2 → ℤ) :
    FiniteSupportStable (deckPull g S).1 (θ ∘ baseVertex) (deckPull g S).2 ↔
      FiniteSupportStable S.1 (θ ∘ baseVertex) S.2 := by
  rw [character_eq]
  exact deckPull_stable_iff g _ _ S

end KroneckerUniversalDeckBaseDimensions
