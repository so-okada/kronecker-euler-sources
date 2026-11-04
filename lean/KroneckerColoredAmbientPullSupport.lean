import KroneckerWeightedColoredSupportIso
import KroneckerQuiverSupportEulerTransport
import KroneckerUniversalWordBaseProjection

/-! An ambient quiver isomorphism preserving the bipartition and actual
colors induces a weighted colored full-support isomorphism on its pulled
dimension. In particular actual even word-deck normalization retains the
same weighted colored support class, with the pullback direction explicit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerColoredAmbientPullSupport
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerWeightedColoredSupportIso
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportInducedQuiver KroneckerQuiverSupportEulerTransport
attribute [local instance] Classical.decEq Classical.propDecidable

def ambientPullIso {P Q : TypedQuiver} (C : Coloring P) (D : Coloring Q)
    (f : TypedQuiverIso P Q) (d : Q.V →₀ ℕ)
    (hs : ∀ v, D.side (f.vertexEquiv v) = C.side v)
    (hc : ∀ a, D.color (f.arrowEquiv a) = C.color a) :
    ColoredIso C D (pullDimension f d) d where
  iso := supportQuiverIso f d
  weight _ := rfl
  side v := hs v.val
  color a := hc a.val

def wordDeckPullIso (g : KroneckerCoverDeckTranslations.Deck)
    (S : SupportedRepresentation coloredCoverQuiver) :
    ColoredIso KroneckerUniversalWordBaseProjection.coloring KroneckerUniversalWordBaseProjection.coloring
      (deckPull g S).1 S.1 :=
  ambientPullIso _ _ (deckQuiverAuto g) S.1 g.preserves_parity (fun _ => rfl)


end KroneckerColoredAmbientPullSupport
