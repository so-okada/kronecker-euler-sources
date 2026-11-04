import KroneckerEmbeddedSupportQuiverIso

/-! Every actual ambient representation supported in an embedded full component
has a unique coordinate representation on the smaller quiver. The equivalence
is constructed by support restriction, actual arrow reindexing, and extension
by zero, so it includes all ambient zero-dimensional vertices. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedRepresentationEquivalence
open KroneckerAbelianCover KroneckerFiniteQuiverHom KroneckerTypedQuiverMaps
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerDirectSumEmbeddingLocalLifts
open KroneckerEmbeddedSupportQuiverIso
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

def supportFinsupp {V : Type} (d : V →₀ ℕ) : SupportVertex d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (supportDimension d)

def representationEquiv (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d) :
    Representation Q.source Q.target (fun v => d v) ≃
      Representation P.source P.target (fun v => descend f.vertex hv d v) :=
  (KroneckerFiniteSupportInducedQuiver.representationEquiv Q d).trans
    ((pullRepresentationEquiv (supportIso f hv ha hf d hd) (supportFinsupp d)).trans
      (KroneckerFiniteSupportInducedQuiver.representationEquiv P (descend f.vertex hv d)).symm)

theorem restricted_representation (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) :
    restrictToSupport P (descend f.vertex hv d) (representationEquiv f hv ha hf d hd R) =
      pullRepresentation (supportIso f hv ha hf d hd) (supportFinsupp d) (restrictToSupport Q d R) :=
  restrict_extend P _ _

theorem representation_on_support_arrow (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v))
    (a : SupportArrow P.source P.target (descend f.vertex hv d)) :
    (representationEquiv f hv ha hf d hd R).arrow a.val ≍ R.arrow (f.arrow a.val) := by
  have h := congrArg (fun S => S.arrow a) (restricted_representation f hv ha hf d hd R)
  exact (heq_of_eq h).trans
    (KroneckerQuiverPullbackComposition.pull_arrow_heq (supportIso f hv ha hf d hd) (supportFinsupp d)
      (restrictToSupport Q d R) a)

end KroneckerEmbeddedRepresentationEquivalence
