import KroneckerEmbeddedRestrictionArrowFormula
import KroneckerEmbeddedStabilityEquivalence

/- Original module: KroneckerEmbeddedSupportedRepresentations -/
section
/-! Component descent is an actual equivalence on dimensioned representations,
with the image-support condition recorded in the source type. Its dimension
and all-subrepresentation stability formulas hold without choosing a dimension
vector in advance. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedSupportedRepresentations
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerEmbeddedFiniteDimensions KroneckerDirectSumEmbeddingLocalLifts
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportStability
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

abbrev ImageSupported (f : QuiverMap P Q) :=
  {S : SupportedRepresentation Q // InImage f.vertex S.1}

def supportedEquiv (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f) :
    ImageSupported f ≃ SupportedRepresentation P :=
  (Equiv.subtypeSigmaEquiv (fun d : Q.V →₀ ℕ => Representation Q.source Q.target (fun v => d v))
    (InImage f.vertex)).trans
    (Equiv.sigmaCongr (dimensionEquiv f.vertex hv).symm
      (fun d => KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d.val d.property))

theorem supportedEquiv_dimension (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f) (S : ImageSupported f) :
    (supportedEquiv f hv ha hf S).1 = descend f.vertex hv S.val.1 := rfl

theorem supportedEquiv_representation (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f) (S : ImageSupported f) :
    (supportedEquiv f hv ha hf S).2 = KroneckerQuiverMapRepresentationPullback.mapRep f S.val.1 S.val.2 :=
  KroneckerEmbeddedRestrictionArrowFormula.representation_eq_mapRep f hv ha hf _ S.property _

theorem supportedEquiv_stable (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f) (S : ImageSupported f) (θ : Q.V → ℤ) :
    FiniteSupportStable (supportedEquiv f hv ha hf S).1 (θ ∘ f.vertex) (supportedEquiv f hv ha hf S).2 ↔
      FiniteSupportStable S.val.1 θ S.val.2 :=
  KroneckerEmbeddedStabilityEquivalence.stable_iff f hv ha hf _ S.property θ _

theorem supportedEquiv_inverse_dimension (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f) (S : SupportedRepresentation P) :
    ((supportedEquiv f hv ha hf).symm S).val.1 = S.1.mapDomain f.vertex := by
  have h := congrArg Sigma.fst ((supportedEquiv f hv ha hf).apply_symm_apply S)
  change descend f.vertex hv ((supportedEquiv f hv ha hf).symm S).val.1 = S.1 at h
  rw [← h]
  exact (Finsupp.mapDomain_comapDomain f.vertex hv _ ((supportedEquiv f hv ha hf).symm S).property).symm

end KroneckerEmbeddedSupportedRepresentations
end
end

/- Original module: KroneckerEmbeddedRepresentationIsomorphisms -/
section
/-! Embedded-component descent is fully faithful on actual commuting
vertexwise linear isomorphisms. Restriction, full-support quiver pullback,
and extension by zero give an explicit bijection, not just dimension equality. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedRepresentationIsomorphisms
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerEmbeddedFiniteDimensions KroneckerDirectSumEmbeddingLocalLifts
open KroneckerEmbeddedRepresentationEquivalence KroneckerEmbeddedSupportQuiverIso
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportIsomorphisms
open KroneckerQuiverPullbackIsomorphisms
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

def isoEquiv (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R S : Representation Q.source Q.target (fun v => d v)) :
    Iso R S ≃ Iso
      (KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd R)
      (KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd S) := by
  let e := KroneckerFiniteSupportIsomorphisms.isoEquiv Q d R S
  let j := pullIsoEquiv (supportIso f hv ha hf d hd) (supportFinsupp d)
    (restrictToSupport Q d R) (restrictToSupport Q d S)
  refine e.trans (j.trans ?_)
  rw [← restricted_representation,← restricted_representation]
  exact (KroneckerFiniteSupportIsomorphisms.isoEquiv P (descend f.vertex hv d) _ _).symm

theorem iso_iff (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R S : Representation Q.source Q.target (fun v => d v)) :
    Nonempty (Iso
      (KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd R)
      (KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd S)) ↔ Nonempty (Iso R S) :=
  ⟨fun ⟨e⟩ => ⟨(isoEquiv f hv ha hf d hd R S).symm e⟩,
    fun ⟨e⟩ => ⟨isoEquiv f hv ha hf d hd R S e⟩⟩

end KroneckerEmbeddedRepresentationIsomorphisms
end
end

/- Original module: KroneckerEmbeddedAcrossIsomorphisms -/
section
/-! Full faithfulness also holds when finite dimension vectors are not assumed
equal: actual linear isomorphisms force that equality, and image-supported
pushforward reflects it. This is the gauge-isomorphism bridge on dimensioned
representations needed for the accumulated orbit dictionary. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedAcrossIsomorphisms
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerEmbeddedFiniteDimensions KroneckerDirectSumEmbeddingLocalLifts
open KroneckerEmbeddedSupportedRepresentations KroneckerQuiverPullbackComposition
open KroneckerDimensionedCoverIsomorphisms
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

theorem across_iff_iso (d : Q.V →₀ ℕ) (R S : Representation Q.source Q.target (fun v => d v)) :
    Nonempty (AcrossIso (⟨d,R⟩ : SupportedRepresentation Q) ⟨d,S⟩) ↔ Nonempty (Iso R S) :=
  ⟨fun ⟨e⟩ => ⟨⟨e.map,e.commutes⟩⟩,fun ⟨e⟩ => ⟨AcrossIso.ofIso e⟩⟩

theorem descend_dimension_eq_iff (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (d e : Q.V →₀ ℕ) (hd : InImage f.vertex d) (he : InImage f.vertex e) :
    descend f.vertex hv d = descend f.vertex hv e ↔ d = e := by
  constructor
  · intro h
    have hh : (⟨d,hd⟩ : {δ // InImage f.vertex δ}) = ⟨e,he⟩ :=
      (dimensionEquiv f.vertex hv).symm.injective h
    exact congrArg Subtype.val hh
  · intro h; rw [h]

theorem supported_across_iff (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (S T : ImageSupported f) :
    Nonempty (AcrossIso (supportedEquiv f hv ha hf S) (supportedEquiv f hv ha hf T)) ↔
      Nonempty (AcrossIso S.val T.val) := by
  rcases S with ⟨⟨d,R⟩,hd⟩
  rcases T with ⟨⟨e,T⟩,he⟩
  constructor
  · rintro ⟨a⟩
    have hde : d = e := (descend_dimension_eq_iff f hv d e hd he).mp a.dimension_eq
    subst e
    apply (across_iff_iso d R T).mpr
    apply (KroneckerEmbeddedRepresentationIsomorphisms.iso_iff f hv ha hf d hd R T).mp
    exact (across_iff_iso _ _ _).mp ⟨a⟩
  · rintro ⟨a⟩
    have hde : d = e := a.dimension_eq
    subst e
    apply (across_iff_iso _ _ _).mpr
    exact (KroneckerEmbeddedRepresentationIsomorphisms.iso_iff f hv ha hf d hd R T).mpr
      ((across_iff_iso d R T).mp ⟨a⟩)

end KroneckerEmbeddedAcrossIsomorphisms
end
end
