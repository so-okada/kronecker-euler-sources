import KroneckerEmbeddedAcrossIsomorphisms
import KroneckerFiniteSupportEulerTransport

section

/-! Fullness on an embedded vertex image suffices for an exact finite full-
support quiver isomorphism. This weaker condition allows a finite tree inside
an infinite cover: arrows leaving the image need not lift. Every arrow whose
BOTH endpoints lie in the image must lift, retaining parallel multiplicities. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullImageQuiverEmbedding
open KroneckerAbelianCover KroneckerTypedQuiverMaps
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerEmbeddedSupportQuiverIso
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q R : TypedQuiver}

def FullOnImage (f : QuiverMap P Q) : Prop :=
  ∀ (a : Q.A) (u v : P.V), Q.source a = f.vertex u → Q.target a = f.vertex v →
    ∃ b : P.A, f.arrow b = a


theorem supportArrowMap_bijective (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d) :
    Function.Bijective (KroneckerEmbeddedSupportQuiverIso.supportArrowMap f hv d) := by
  constructor
  · intro a b h
    exact Subtype.ext (ha (congrArg Subtype.val h))
  · intro a
    obtain ⟨x,hx⟩ := hd a.property.1
    obtain ⟨y,hy⟩ := hd a.property.2
    obtain ⟨b,hb⟩ := hf a.val x y hx.symm hy.symm
    refine ⟨⟨b,?_,?_⟩,Subtype.ext hb⟩
    · rw [Finsupp.mem_support_iff,descend_apply,← f.source,hb]
      exact Finsupp.mem_support_iff.mp a.property.1
    · rw [Finsupp.mem_support_iff,descend_apply,← f.target,hb]
      exact Finsupp.mem_support_iff.mp a.property.2

def supportIso (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d) :
    TypedQuiverIso (supportQuiver P (descend f.vertex hv d)) (supportQuiver Q d) where
  vertexEquiv := supportEquiv f.vertex hv d hd
  arrowEquiv := Equiv.ofBijective (KroneckerEmbeddedSupportQuiverIso.supportArrowMap f hv d)
    (supportArrowMap_bijective f hv ha hf d hd)
  map_source a := Subtype.ext (f.source a.val)
  map_target a := Subtype.ext (f.target a.val)

end KroneckerFullImageQuiverEmbedding
end
end

section

/- Original module: KroneckerFullImageRepresentationEquivalence -/
section
/-! A full embedding on its vertex image identifies actual ambient coordinate
representations of image-supported finite dimensions. The construction uses
all induced arrows and extension by zero, and equals ordinary quiver-map
pullback on EVERY arrow. No local surjectivity outside the image is assumed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullImageRepresentationEquivalence
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerFullImageQuiverEmbedding
open KroneckerEmbeddedRepresentationEquivalence KroneckerQuiverMapRepresentationPullback
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

def representationEquiv (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d) :
    Representation Q.source Q.target (fun v => d v) ≃
      Representation P.source P.target (fun v => descend f.vertex hv d v) :=
  (KroneckerFiniteSupportInducedQuiver.representationEquiv Q d).trans
    ((pullRepresentationEquiv (supportIso f hv ha hf d hd) (supportFinsupp d)).trans
      (KroneckerFiniteSupportInducedQuiver.representationEquiv P (descend f.vertex hv d)).symm)

theorem restricted_representation (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) :
    restrictToSupport P (descend f.vertex hv d) (representationEquiv f hv ha hf d hd R) =
      pullRepresentation (supportIso f hv ha hf d hd) (supportFinsupp d) (restrictToSupport Q d R) :=
  restrict_extend P _ _

theorem representation_on_support_arrow (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v))
    (a : SupportArrow P.source P.target (descend f.vertex hv d)) :
    (representationEquiv f hv ha hf d hd R).arrow a.val ≍ R.arrow (f.arrow a.val) := by
  have h := congrArg (fun S => S.arrow a) (restricted_representation f hv ha hf d hd R)
  exact (heq_of_eq h).trans
    (KroneckerQuiverPullbackComposition.pull_arrow_heq (supportIso f hv ha hf d hd) (supportFinsupp d)
      (restrictToSupport Q d R) a)

theorem representation_eq_mapRep (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) : representationEquiv f hv ha hf d hd R = mapRep f d R := by
  apply (KroneckerFiniteSupportInducedQuiver.representationEquiv P (descend f.vertex hv d)).injective
  apply representation_ext
  funext a
  exact eq_of_heq ((representation_on_support_arrow f hv ha hf d hd R a).trans (mapRep_arrow_heq f d R a.val).symm)

theorem representation_arrow_heq (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) (a : P.A) :
    (representationEquiv f hv ha hf d hd R).arrow a ≍ R.arrow (f.arrow a) := by
  rw [representation_eq_mapRep]
  exact mapRep_arrow_heq f d R a

end KroneckerFullImageRepresentationEquivalence
end
end

/- Original module: KroneckerFullImageIsomorphisms -/
section
/-! Representation descent through a full vertex-image embedding is fully
faithful on commuting vertexwise linear isomorphisms. The explicit bijection
uses the full induced support arrows, so finite tree embeddings need no
surjectivity on arrows that leave their image. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullImageIsomorphisms
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerEmbeddedFiniteDimensions KroneckerFullImageQuiverEmbedding
open KroneckerFullImageRepresentationEquivalence
open KroneckerEmbeddedRepresentationEquivalence (supportFinsupp)
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportIsomorphisms
open KroneckerQuiverPullbackIsomorphisms
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

def isoEquiv (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R S : Representation Q.source Q.target (fun v => d v)) :
    Iso R S ≃ Iso
      (KroneckerFullImageRepresentationEquivalence.representationEquiv f hv ha hf d hd R)
      (KroneckerFullImageRepresentationEquivalence.representationEquiv f hv ha hf d hd S) := by
  let e := KroneckerFiniteSupportIsomorphisms.isoEquiv Q d R S
  let j := pullIsoEquiv (supportIso f hv ha hf d hd) (supportFinsupp d)
    (restrictToSupport Q d R) (restrictToSupport Q d S)
  refine e.trans (j.trans ?_)
  rw [← restricted_representation,← restricted_representation]
  exact (KroneckerFiniteSupportIsomorphisms.isoEquiv P (descend f.vertex hv d) _ _).symm

theorem iso_iff (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R S : Representation Q.source Q.target (fun v => d v)) :
    Nonempty (Iso
      (KroneckerFullImageRepresentationEquivalence.representationEquiv f hv ha hf d hd R)
      (KroneckerFullImageRepresentationEquivalence.representationEquiv f hv ha hf d hd S)) ↔ Nonempty (Iso R S) :=
  ⟨fun ⟨e⟩ => ⟨(isoEquiv f hv ha hf d hd R S).symm e⟩,
    fun ⟨e⟩ => ⟨isoEquiv f hv ha hf d hd R S e⟩⟩

end KroneckerFullImageIsomorphisms
end
end

/- Original module: KroneckerFullImageStabilityEquivalence -/
section
/-! A full embedding on a finite support image identifies ALL actual
subrepresentations and preserves King stability in both directions. This
allows finite full trees in an infinite quiver: no lifting of arrows leaving
the image is required. The submodule formula is exact on positive vertices. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullImageStabilityEquivalence
open KroneckerAbelianCover KroneckerFiniteQuiverHom KroneckerTypedQuiverMaps
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerFullImageQuiverEmbedding
open KroneckerFullImageRepresentationEquivalence
open KroneckerEmbeddedRepresentationEquivalence (supportFinsupp)
open KroneckerEmbeddedSubrepresentationEquivalence (castSubrep castSubrep_space)
open KroneckerFiniteSupportSubrepresentations KroneckerQuiverPullbackSubrepresentations
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

def subrepEquiv (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) :
    Subrep R ≃ Subrep (KroneckerFullImageRepresentationEquivalence.representationEquiv f hv ha hf d hd R) :=
  (KroneckerFiniteSupportSubrepresentations.subrepEquiv Q d R).trans
    ((pullSubrepEquiv (supportIso f hv ha hf d hd) (supportFinsupp d) (restrictToSupport Q d R)).trans
      ((castSubrep (restricted_representation f hv ha hf d hd R).symm).trans
        (KroneckerFiniteSupportSubrepresentations.subrepEquiv P (descend f.vertex hv d)
          (KroneckerFullImageRepresentationEquivalence.representationEquiv f hv ha hf d hd R)).symm))

set_option backward.isDefEq.respectTransparency false in
theorem subrep_space_on_support (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) (U : Subrep R)
    (v : P.V) (h : v ∈ (descend f.vertex hv d).support) :
    (subrepEquiv f hv ha hf d hd R U).space v = U.space (f.vertex v) := by
  change (if h' : v ∈ (descend f.vertex hv d).support then
    (castSubrep (restricted_representation f hv ha hf d hd R).symm
      (pullSubrep (supportIso f hv ha hf d hd) (supportFinsupp d) (restrictToSupport Q d R)
        (restrictSubrep Q d R U))).space ⟨v,h'⟩ else (⊥ : Submodule ℂ (Space (descend f.vertex hv d v)))) = _
  rw [dite_eq_left h,castSubrep_space]
  rfl


open KroneckerFiniteSupportStability KroneckerFiniteQuiverPullbackStability

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)
local instance supportQuiverFintype (Q : TypedQuiver) (d : Q.V →₀ ℕ) : Fintype (supportQuiver Q d).V :=
  supportFintype d

theorem stable_iff (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d) (θ : Q.V → ℤ)
    (R : Representation Q.source Q.target (fun v => d v)) :
    FiniteSupportStable (descend f.vertex hv d) (θ ∘ f.vertex)
      (KroneckerFullImageRepresentationEquivalence.representationEquiv f hv ha hf d hd R) ↔
      FiniteSupportStable d θ R := by
  rw [finiteSupportStable_iff_restrict P,finiteSupportStable_iff_restrict Q,restricted_representation]
  exact finite_pull_stable_iff (supportIso f hv ha hf d hd) (supportFinsupp d)
    (supportCharacter d θ) (restrictToSupport Q d R)

end KroneckerFullImageStabilityEquivalence
end
end

/- Original module: KroneckerFullImageSupportedBridge -/
section
/-! Actual dimensioned representations supported on a full embedded vertex
image are equivalent to representations of the source quiver. The inverse
pushes dimensions and extends matrices by zero. Exact formulas preserve
King stability and reflect gauge isomorphism even across differing dimensions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullImageSupportedBridge
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerEmbeddedFiniteDimensions KroneckerFullImageQuiverEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportStability
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

abbrev ImageSupported (f : QuiverMap P Q) :=
  {S : SupportedRepresentation Q // InImage f.vertex S.1}

def supportedEquiv (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f) :
    ImageSupported f ≃ SupportedRepresentation P :=
  (Equiv.subtypeSigmaEquiv (fun d : Q.V →₀ ℕ => Representation Q.source Q.target (fun v => d v))
    (InImage f.vertex)).trans
    (Equiv.sigmaCongr (dimensionEquiv f.vertex hv).symm
      (fun d => KroneckerFullImageRepresentationEquivalence.representationEquiv f hv ha hf d.val d.property))

theorem supportedEquiv_dimension (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f) (S : ImageSupported f) :
    (supportedEquiv f hv ha hf S).1 = descend f.vertex hv S.val.1 := rfl

theorem supportedEquiv_representation (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f) (S : ImageSupported f) :
    (supportedEquiv f hv ha hf S).2 = KroneckerQuiverMapRepresentationPullback.mapRep f S.val.1 S.val.2 :=
  KroneckerFullImageRepresentationEquivalence.representation_eq_mapRep f hv ha hf _ S.property _

theorem supportedEquiv_stable (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f) (S : ImageSupported f) (θ : Q.V → ℤ) :
    FiniteSupportStable (supportedEquiv f hv ha hf S).1 (θ ∘ f.vertex) (supportedEquiv f hv ha hf S).2 ↔
      FiniteSupportStable S.val.1 θ S.val.2 :=
  KroneckerFullImageStabilityEquivalence.stable_iff f hv ha hf _ S.property θ _

theorem supportedEquiv_inverse_dimension (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f) (S : SupportedRepresentation P) :
    ((supportedEquiv f hv ha hf).symm S).val.1 = S.1.mapDomain f.vertex := by
  have h := congrArg Sigma.fst ((supportedEquiv f hv ha hf).apply_symm_apply S)
  change descend f.vertex hv ((supportedEquiv f hv ha hf).symm S).val.1 = S.1 at h
  rw [← h]
  exact (Finsupp.mapDomain_comapDomain f.vertex hv _ ((supportedEquiv f hv ha hf).symm S).property).symm


open KroneckerDimensionedCoverIsomorphisms KroneckerEmbeddedAcrossIsomorphisms

theorem supported_across_iff (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : FullOnImage f) (S T : ImageSupported f) :
    Nonempty (AcrossIso (supportedEquiv f hv ha hf S) (supportedEquiv f hv ha hf T)) ↔
      Nonempty (AcrossIso S.val T.val) := by
  rcases S with ⟨⟨d,R⟩,hd⟩
  rcases T with ⟨⟨e,T⟩,he⟩
  constructor
  · rintro ⟨a⟩
    have hde : d = e := (descend_dimension_eq_iff f hv d e hd he).mp a.dimension_eq
    subst e
    apply (across_iff_iso d R T).mpr
    apply (KroneckerFullImageIsomorphisms.iso_iff f hv ha hf d hd R T).mp
    exact (across_iff_iso _ _ _).mp ⟨a⟩
  · rintro ⟨a⟩
    have hde : d = e := a.dimension_eq
    subst e
    apply (across_iff_iso _ _ _).mpr
    exact (KroneckerFullImageIsomorphisms.iso_iff f hv ha hf d hd R T).mpr
      ((across_iff_iso d R T).mp ⟨a⟩)

end KroneckerFullImageSupportedBridge
end
end
end

section

/- Original module: KroneckerFullImagePushforward -/
section
/-! Actual representations push through an injective full vertex-image map,
with zero coordinate spaces outside the image. The push preserves and
reflects gauge isomorphisms and King stability, and its embedded arrow maps
are exactly the original matrices with dependent coordinate transports. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullImagePushforward
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFiniteQuiverHom
open KroneckerEmbeddedFiniteDimensions KroneckerFullImageQuiverEmbedding
open KroneckerFullImageSupportedBridge KroneckerQuiverPullbackComposition
open KroneckerDimensionedCoverIsomorphisms KroneckerFiniteSupportStability
open KroneckerFiniteSupportDeckRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver} (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
  (ha : Function.Injective f.arrow) (hf : FullOnImage f)

def push (S : SupportedRepresentation P) : SupportedRepresentation Q :=
  ((supportedEquiv f hv ha hf).symm S).val

theorem push_image (S : SupportedRepresentation P) : InImage f.vertex (push f hv ha hf S).1 :=
  ((supportedEquiv f hv ha hf).symm S).property

theorem push_dimension (S : SupportedRepresentation P) :
    (push f hv ha hf S).1 = S.1.mapDomain f.vertex := supportedEquiv_inverse_dimension f hv ha hf S

theorem push_injective : Function.Injective (push f hv ha hf) := by
  intro S T h
  apply (supportedEquiv f hv ha hf).symm.injective
  exact Subtype.ext h

theorem descend_push (S : SupportedRepresentation P) :
    supportedEquiv f hv ha hf ⟨push f hv ha hf S,push_image f hv ha hf S⟩ = S :=
  (supportedEquiv f hv ha hf).apply_symm_apply S

theorem push_descend (S : ImageSupported f) : push f hv ha hf (supportedEquiv f hv ha hf S) = S.val :=
  congrArg Subtype.val ((supportedEquiv f hv ha hf).symm_apply_apply S)

theorem push_across_iff (S T : SupportedRepresentation P) :
    Nonempty (AcrossIso (push f hv ha hf S) (push f hv ha hf T)) ↔ Nonempty (AcrossIso S T) := by
  have h := supported_across_iff f hv ha hf ((supportedEquiv f hv ha hf).symm S) ((supportedEquiv f hv ha hf).symm T)
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at h
  exact h.symm

theorem push_stable_iff (S : SupportedRepresentation P) (θ : Q.V → ℤ) :
    FiniteSupportStable (push f hv ha hf S).1 θ (push f hv ha hf S).2 ↔
      FiniteSupportStable S.1 (θ ∘ f.vertex) S.2 := by
  have h := supportedEquiv_stable f hv ha hf ((supportedEquiv f hv ha hf).symm S) θ
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem push_arrow_heq (S : SupportedRepresentation P) (a : P.A) :
    (push f hv ha hf S).2.arrow (f.arrow a) ≍ S.2.arrow a := by
  have h := KroneckerFullImageRepresentationEquivalence.representation_arrow_heq f hv ha hf
    (push f hv ha hf S).1 (push_image f hv ha hf S) (push f hv ha hf S).2 a
  exact h.symm.trans (dependent_apply_heq (fun T : SupportedRepresentation P => T.2.arrow a)
    ((supportedEquiv f hv ha hf).apply_symm_apply S))

end KroneckerFullImagePushforward
end
end

/- Original module: KroneckerFullImageNumericalTransport -/
section
/-! Pushforward through a full image embedding preserves total dimension,
nonzero support, all original-vertex pushforwards and the actual self-Euler
form whenever the induced arrow sets are finite. All original multiplicities
are summed, including multiple lifted vertices over one original vertex. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullImageNumericalTransport
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFullImagePushforward KroneckerFullImageSupportedBridge
open KroneckerEmbeddedFiniteDimensions KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportEulerTransport
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver} (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
  (ha : Function.Injective f.arrow) (hf : FullOnImage f)

theorem push_zero_iff (S : SupportedRepresentation P) : (push f hv ha hf S).1 = 0 ↔ S.1 = 0 := by
  rw [push_dimension,← Finsupp.mapDomain_zero (f:=f.vertex)]
  exact (Finsupp.mapDomain_injective hv).eq_iff

theorem push_sum (S : SupportedRepresentation P) :
    (push f hv ha hf S).1.sum (fun _ k => k) = S.1.sum (fun _ k => k) := by
  rw [push_dimension]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem push_original_dimension {Z : Type} (S : SupportedRepresentation P) (g : Q.V → Z) :
    (push f hv ha hf S).1.mapDomain g = S.1.mapDomain (g ∘ f.vertex) := by
  rw [push_dimension,← Finsupp.mapDomain_comp]

theorem supportEuler_congr {R : TypedQuiver} (d e : R.V →₀ ℕ)
    [Finite (SupportArrow R.source R.target d)] [Finite (SupportArrow R.source R.target e)]
    (h : d = e) : supportEuler R d = supportEuler R e := by
  cases h
  rfl

theorem push_selfEuler (S : SupportedRepresentation P)
    [Finite (SupportArrow P.source P.target S.1)]
    [Finite (SupportArrow Q.source Q.target (push f hv ha hf S).1)] :
    supportEuler P S.1 = supportEuler Q (push f hv ha hf S).1 := by
  have hd := congrArg Sigma.fst (descend_push f hv ha hf S)
  change descend f.vertex hv (push f hv ha hf S).1 = S.1 at hd
  let : Finite (SupportArrow P.source P.target (descend f.vertex hv (push f hv ha hf S).1)) := by
    rw [hd]
    infer_instance
  have h := supportEuler_iso _ _ (supportIso f hv ha hf (push f hv ha hf S).1 (push_image f hv ha hf S)) (fun _ => rfl)
  exact (supportEuler_congr _ _ hd).symm.trans h

end KroneckerFullImageNumericalTransport
end
end
end

