import KroneckerProperColoringFiniteSupportArrows
import KroneckerUniversalDeckBaseDimensions

/-! The word-cover self-Euler formula agrees with the general full-support
Euler form. Consequently every actual universal deck pullback preserves this
same integer, so normalization is compatible with positive-Euler restrictions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalSupportEuler
open KroneckerReducedColorWords KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportEulerTransport
open KroneckerColoredCoverStableUniqueness
attribute [local instance] Classical.decEq Classical.propDecidable

instance wordSupportFinite (d : coloredCoverQuiver.V →₀ ℕ) :
    Finite (SupportArrow coloredCoverQuiver.source coloredCoverQuiver.target d) :=
  KroneckerProperColoringFiniteSupportArrows.support_arrows_finite KroneckerUniversalWordBaseProjection.coloring d

theorem supportEuler_eq_coverEuler (d : Word →₀ ℕ) : supportEuler coloredCoverQuiver d = coverEuler d := by
  unfold supportEuler finiteEuler coverEuler
  congr 1 <;> apply Finset.sum_congr
  all_goals first | (ext x; simp) | (intros; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem deckPull_selfEuler (g : Deck) (S : SupportedRepresentation coloredCoverQuiver) :
    supportEuler coloredCoverQuiver (deckPull g S).1 = supportEuler coloredCoverQuiver S.1 := by
  rw [supportEuler_eq_coverEuler,supportEuler_eq_coverEuler]
  exact KroneckerQuiverSupportEulerTransport.deck_cover_euler g S.1

end KroneckerUniversalSupportEuler
