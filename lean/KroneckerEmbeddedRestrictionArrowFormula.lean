import KroneckerDimensionedCoverIsomorphisms
import KroneckerEmbeddedRepresentationEquivalence

/- Original module: KroneckerQuiverMapRepresentationPullback -/
section
/-! Every actual typed-quiver map pulls back coordinate representations and
commuting families of linear isomorphisms. Identity and composition are
proved on the arrow matrices, including dependent endpoint transports. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerQuiverMapRepresentationPullback
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerQuiverPullbackSubrepresentations
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q T : TypedQuiver}

def mapRep (f : QuiverMap P Q) (d : Q.V → ℕ) (R : Representation Q.source Q.target d) :
    Representation P.source P.target (d ∘ f.vertex) where
  arrow a := transportArrow d (f.source a) (f.target a) (R.arrow (f.arrow a))

theorem mapRep_arrow_heq (f : QuiverMap P Q) (d : Q.V → ℕ)
    (R : Representation Q.source Q.target d) (a : P.A) :
    (mapRep f d R).arrow a ≍ R.arrow (f.arrow a) := by
  simp only [mapRep,transportArrow]
  exact (cast_heq _ _).trans (cast_heq _ _)





end KroneckerQuiverMapRepresentationPullback
end
end

/- Original module: KroneckerEmbeddedRestrictionArrowFormula -/
section
/-! The support-based component equivalence is literally ordinary pullback
along the embedding on every arrow, including zero-dimensional endpoints.
Thus later naturality statements concern the actual ambient representation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedRestrictionArrowFormula
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportInducedQuiver
open KroneckerEmbeddedRepresentationEquivalence KroneckerDirectSumEmbeddingLocalLifts
open KroneckerQuiverMapRepresentationPullback
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

theorem representation_eq_mapRep (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) :
    KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd R = mapRep f d R := by
  apply (KroneckerFiniteSupportInducedQuiver.representationEquiv P (descend f.vertex hv d)).injective
  apply representation_ext
  funext a
  apply eq_of_heq
  exact (representation_on_support_arrow f hv ha hf d hd R a).trans
    (mapRep_arrow_heq f d R a.val).symm

theorem representation_arrow_heq (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) (a : P.A) :
    (KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd R).arrow a ≍
      R.arrow (f.arrow a) := by
  rw [representation_eq_mapRep]
  exact mapRep_arrow_heq f d R a

end KroneckerEmbeddedRestrictionArrowFormula
end
end
