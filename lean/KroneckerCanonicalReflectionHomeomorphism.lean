import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Maps.Basic
import KroneckerStableKernelLocalOrbit
import KroneckerStableKernelBasedCover
import KroneckerStableReflectionEssentialSurjectivity
import KroneckerStableSourceReflectionIso
import KroneckerStableMatrixCokernelCover
import Mathlib.Topology.Algebra.Module.FiniteDimension

/- Original module: KroneckerCanonicalDimensionHomeomorphism -/
section
/-! Equality of dimension labels transports the actual canonical moduli
spaces homeomorphically, with an exact representative transport formula. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalDimensionHomeomorphism
open KroneckerCanonicalKroneckerModuli KroneckerStablePairFamilyEquivalence
variable {m a b c d : ℕ}
def homeomorph (ha : a=c) (hb : b=d) : space m a b ≃ₜ space m c d := by
  subst c;subst d;exact Homeomorph.refl _
def stableTransport (ha : a=c) (hb : b=d) (R : StablePair m a b) : StablePair m c d :=
  ⟨KroneckerPairDimensionTransport.transport ha hb R.val,
    (KroneckerPairDimensionTransport.stable_iff ha hb R.val).mpr R.property⟩
theorem on_representatives (ha : a=c) (hb : b=d) (R : StablePair m a b) :
    homeomorph ha hb (KroneckerStablePairProjection.project m a b R)=
      KroneckerStablePairProjection.project m c d (stableTransport ha hb R) := by
  subst c;subst d;rfl
end KroneckerCanonicalDimensionHomeomorphism
end
end

/- Original module: KroneckerOpenCoverContinuity -/
section
/-! Continuous local formulas on an open cover determine a continuous global
map even when the local lifts differ. Only their values after projection agree. -/
set_option autoImplicit false
namespace KroneckerOpenCoverContinuity
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
theorem of_local_formulas {ι : Type} (U : ι → Set X) (hU : ∀ i,IsOpen (U i))
    (cover : ∀ x,∃ i,x ∈ U i) (f : X → Y)
    (g : ∀ i,U i → Y) (hg : ∀ i,Continuous (g i))
    (agree : ∀ i (x : U i),g i x=f x.val) : Continuous f := by
  apply continuous_of_continuousOn_iUnion_of_isOpen (s := U)
  · intro i
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun x : U i => f x.val)=g i := funext fun x => (agree i x).symm
    change Continuous (fun x : U i => f x.val)
    rw [he]
    exact hg i
  · exact hU
  · exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (cover x)
end KroneckerOpenCoverContinuity
end

/- Original module: KroneckerQuotientLocalLifts -/
section
/-! A map out of a quotient is continuous when its composite on representatives
has continuous local lifts through another quotient on an open cover. -/
set_option autoImplicit false
namespace KroneckerQuotientLocalLifts
variable {X Q Y Z : Type} [TopologicalSpace X] [TopologicalSpace Q]
  [TopologicalSpace Y] [TopologicalSpace Z]
theorem continuous {ι : Type} (p : X → Q) (hp : Topology.IsQuotientMap p)
    (q : Y → Z) (hq : Continuous q) (f : Q → Z)
    (U : ι → Set X) (hU : ∀ i,IsOpen (U i)) (cover : ∀ x,∃ i,x∈U i)
    (lift : ∀ i,U i → Y) (hlift : ∀ i,Continuous (lift i))
    (agree : ∀ i (x : U i),q (lift i x)=f (p x.val)) : Continuous f := by
  apply hp.continuous_iff.mpr
  exact KroneckerOpenCoverContinuity.of_local_formulas U hU cover (f ∘ p)
    (fun i => q ∘ lift i) (fun i => hq.comp (hlift i)) agree
end KroneckerQuotientLocalLifts
end

/- Original module: KroneckerCanonicalReflectionContinuous -/
section
/-! The existing canonical reflection on actual stable matrix-orbit spaces
is continuous, proved by continuous local kernel frames on a covering family. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionContinuous
open KroneckerStableKernelBasedCover
theorem continuous (m a b : ℕ) (ha : 0<a) :
    Continuous (KroneckerCanonicalReflectionMap.map m a b ha) := by
  apply KroneckerQuotientLocalLifts.continuous
    (KroneckerStableMatrixProjection.project m a b)
    (KroneckerStableMatrixProjection.quotient_project m a b)
    (KroneckerStableMatrixProjection.project m (m*a-b) a)
    (KroneckerStableMatrixProjection.continuous_project m (m*a-b) a)
    (KroneckerCanonicalReflectionMap.map m a b ha)
    (domain m a b) (domain_open m a b) (cover m a b ha)
    (fun c => KroneckerStableKernelLocalFamily.family ha c.1 c.2)
    (fun c => KroneckerStableKernelLocalContinuity.continuous_family ha c.1 c.2)
    (fun c => KroneckerStableKernelLocalOrbit.agrees ha c.1 c.2)
end KroneckerCanonicalReflectionContinuous
end
end

/- Original module: KroneckerCanonicalReflectionInjective -/
section
/-! Global canonical reflection separates actual stable gauge orbits:
equality of reflected moduli points forces equality of the original points. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionInjective
open KroneckerCanonicalKroneckerModuli KroneckerCanonicalReflectionMap

theorem injective (m a b : ℕ) (ha : 0<a) : Function.Injective (map m a b ha) := by
  intro x y h
  obtain ⟨R,rfl⟩ := KroneckerStablePairProjection.surjective m a b x
  obtain ⟨S,rfl⟩ := KroneckerStablePairProjection.surjective m a b y
  rw [on_representatives,on_representatives] at h
  exact (KroneckerStablePairProjection.eq_iff m a b R S).mpr
    ((KroneckerStablePairReflection.isomorphic_iff m a b ha R S).mpr
      ((KroneckerStablePairProjection.eq_iff _ _ _ _ _).mp h))
end KroneckerCanonicalReflectionInjective
end
end

/- Original module: KroneckerCanonicalReflectionSurjective -/
section
/-! Every actual stable reflected moduli point has an actual stable original
preimage, provided the original source is positive and the dimension subtraction is valid. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionSurjective
open KroneckerCanonicalKroneckerModuli KroneckerCanonicalReflectionMap

theorem surjective (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) : Function.Surjective (map m a b ha) := by
  intro y
  obtain ⟨S,rfl⟩ := KroneckerStablePairProjection.surjective m (m*a-b) a y
  obtain ⟨R,hR⟩ := KroneckerStableReflectionEssentialSurjectivity.exists_preimage m a b ha hb S
  refine ⟨KroneckerStablePairProjection.project m a b R,?_⟩
  rw [on_representatives]
  exact (KroneckerStablePairProjection.eq_iff _ _ _ _ _).mpr hR
end KroneckerCanonicalReflectionSurjective
end
end

/- Original module: KroneckerCanonicalReflectionEquivalence -/
section
/-! Global sink reflection is now a bijection of the actual canonical stable
moduli sets. Continuity is a separate obligation and is not asserted here. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionEquivalence
open KroneckerCanonicalKroneckerModuli

def equiv (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) : space m a b ≃ space m (m*a-b) a :=
  Equiv.ofBijective (KroneckerCanonicalReflectionMap.map m a b ha)
    ⟨KroneckerCanonicalReflectionInjective.injective m a b ha,
      KroneckerCanonicalReflectionSurjective.surjective m a b ha hb⟩

theorem inverse_on_representatives (m a b : ℕ) (ha : 0<a) (hb : b≤m*a)
    (S : KroneckerStablePairFamilyEquivalence.StablePair m (m*a-b) a) :
    (equiv m a b ha hb).symm (KroneckerStablePairProjection.project m (m*a-b) a S)=
      KroneckerStablePairProjection.project m a b (KroneckerStablePairSourceReflection.inverse m a b ha hb S) := by
  apply (equiv m a b ha hb).injective
  rw [Equiv.apply_symm_apply]
  change KroneckerStablePairProjection.project m (m*a-b) a S=
    KroneckerCanonicalReflectionMap.map m a b ha (KroneckerStablePairProjection.project m a b
      (KroneckerStablePairSourceReflection.inverse m a b ha hb S))
  rw [KroneckerCanonicalReflectionMap.on_representatives]
  apply (KroneckerStablePairProjection.eq_iff _ _ _ _ _).mpr
  exact ⟨KroneckerStableReflectionEssentialSurjectivity.reconstructionIso m a b ha hb S⟩
end KroneckerCanonicalReflectionEquivalence
end
end

/- Original module: KroneckerCanonicalSourceReflectionMap -/
section
/-! Source-cokernel reflection descends to a well-defined map of the actual
canonical stable orbit spaces, with a representative evaluation law. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalSourceReflectionMap
open KroneckerCanonicalKroneckerModuli KroneckerStablePairFamilyEquivalence
def map (m a b : ℕ) (hb : 0<b) : space m a b → space m b (m*b-a) :=
  Quotient.lift (fun M : StableMatrix m a b =>
    KroneckerStablePairProjection.project m b (m*b-a)
      (KroneckerStablePairSourceReflection.reflect m a b hb (fromMatrix m a b M))) (by
    intro M N hMN
    apply (KroneckerStablePairProjection.eq_iff _ _ _ _ _).mpr
    apply (KroneckerStableSourceReflectionIso.isomorphic_iff m a b hb _ _).mp
    apply (KroneckerStablePairProjection.eq_iff _ _ _ _ _).mp
    rw [KroneckerStablePairProjection.fromMatrix_project,KroneckerStablePairProjection.fromMatrix_project]
    exact Quotient.sound hMN)
theorem on_representatives (m a b : ℕ) (hb : 0<b) (R : StablePair m a b) :
    map m a b hb (KroneckerStablePairProjection.project m a b R)=
      KroneckerStablePairProjection.project m b (m*b-a) (KroneckerStablePairSourceReflection.reflect m a b hb R) := by
  change KroneckerStablePairProjection.project m b (m*b-a)
    (KroneckerStablePairSourceReflection.reflect m a b hb (fromMatrix m a b (toMatrix m a b R)))=_
  rw [show fromMatrix m a b (toMatrix m a b R)=R from (equiv m a b).symm_apply_apply R]
end KroneckerCanonicalSourceReflectionMap
end
end

/- Original module: KroneckerCanonicalReflectionInverseFormula -/
section
/-! The set-theoretic inverse of canonical sink reflection is exactly source
reflection followed by the forced dimension-label homeomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionInverseFormula
open KroneckerCanonicalKroneckerModuli
theorem inverse (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) :
    (KroneckerCanonicalReflectionEquivalence.equiv m a b ha hb).symm =
      (KroneckerCanonicalDimensionHomeomorphism.homeomorph rfl (Nat.sub_sub_self hb)) ∘
        (KroneckerCanonicalSourceReflectionMap.map m (m*a-b) a ha) := by
  funext x
  obtain ⟨R,rfl⟩ := KroneckerStablePairProjection.surjective m (m*a-b) a x
  rw [KroneckerCanonicalReflectionEquivalence.inverse_on_representatives]
  change _ = KroneckerCanonicalDimensionHomeomorphism.homeomorph rfl (Nat.sub_sub_self hb)
    (KroneckerCanonicalSourceReflectionMap.map m (m*a-b) a ha _)
  rw [KroneckerCanonicalSourceReflectionMap.on_representatives,
    KroneckerCanonicalDimensionHomeomorphism.on_representatives]
  rfl
end KroneckerCanonicalReflectionInverseFormula
end
end

/- Original module: KroneckerStableCokernelBasedCover -/
section
/-! Nonempty source-reflection charts have stable base points and form an
open cover on which one fixed quotient-coordinate basis is available. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableCokernelBasedCover
open KroneckerStableMatrixCokernelCover KroneckerStableRectangularMatrices
variable (m a b : ℕ)
abbrev Index := Σ R : Matrix (Fin a) (Fin m × Fin b) ℂ,chart R
def domain (c : Index m a b) : Set (Stable m a b) := chart c.1
theorem domain_open (c : Index m a b) : IsOpen (domain m a b c) := chart_open c.1
theorem cover (hb : 0<b) (M : Stable m a b) : ∃ c : Index m a b,M ∈ domain m a b c := by
  obtain ⟨R,hR⟩ := KroneckerStableMatrixCokernelCover.cover hb M
  exact ⟨⟨R,⟨M,hR⟩⟩,hR⟩
end KroneckerStableCokernelBasedCover
end
end

/- Original module: KroneckerCokernelCoordinateFamily -/
section
/-! Arbitrary coordinates on the actual cokernel give the same source
reflection, and inherit stability through an explicit pair isomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCokernelCoordinateFamily
open KroneckerReflectionPairModel KroneckerFiniteQuiverHom KroneckerAbstractCokernelReflection
variable {m a b k : ℕ} (R : PairRep m a b) (e : Cokernel R ≃ₗ[ℂ] Space k)
def family : PairRep m b k := fun i => e.toLinearMap.comp (reflection R i)
def iso : KroneckerAbstractPairIso.Iso (reflection R) (family R e) where
  source := LinearEquiv.refl ℂ _
  sink := e
  commutes _ _ := rfl
def canonicalIso (h : Function.Injective (KroneckerReflectionOutgoingMap.outgoing R))
    (e : Cokernel R ≃ₗ[ℂ] Space (m*b-a)) :
    KroneckerAbstractPairIso.Iso (family R e) (KroneckerSourceReflectionCoordinates.reflected R h) :=
  KroneckerAbstractPairIso.trans (KroneckerAbstractPairIso.symm (iso R e))
    (KroneckerSourceReflectionCoordinates.coordinateIso R h)
theorem stable (hb : 0<b) (hs : PairStable R) (e : Cokernel R ≃ₗ[ℂ] Space (m*b-a)) :
    PairStable (family R e) := by
  let h := KroneckerReflectionOutgoingMap.outgoing_injective R hb hs
  exact (KroneckerPairIsoStability.stable_iff (canonicalIso R h e)).mpr
    (KroneckerSourceCoordinateStability.stable R hb hs h)
end KroneckerCokernelCoordinateFamily
end
end

/- Original module: KroneckerMatrixCokernelLinearProjection -/
section
/-! The matrix complement projection is surjective onto the fixed retraction
kernel and has exactly the moving injection image as its kernel. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixCokernelLinearProjection
open KroneckerMatrixCokernelChart KroneckerMatrixCokernelProjection
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
def project (R : Matrix v w ℂ) (I : Domain R) :
    (w → ℂ) →ₗ[ℂ] LinearMap.ker (Matrix.toLin' R) where
  toFun x := ⟨projection R I *ᵥ x,by
    change R *ᵥ (projection R I *ᵥ x)=0
    rw [Matrix.mulVec_mulVec,image_in_kernel,Matrix.zero_mulVec]⟩
  map_add' x y := by apply Subtype.ext;exact Matrix.mulVec_add _ _ _
  map_smul' c x := by apply Subtype.ext;exact Matrix.mulVec_smul _ _ _
theorem surjective (R : Matrix v w ℂ) (I : Domain R) : Function.Surjective (project R I) := by
  intro x
  refine ⟨x.val,?_⟩
  apply Subtype.ext
  exact fixes_kernel R I x.val x.property
theorem kernel_eq_range (R : Matrix v w ℂ) (I : Domain R) :
    LinearMap.ker (project R I)=LinearMap.range (Matrix.toLin' I.val) := by
  rw [← KroneckerMatrixCokernelExactness.kernel_eq_range R I]
  ext x
  change (project R I x=0) ↔ projection R I *ᵥ x=0
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
end KroneckerMatrixCokernelLinearProjection
end
end

/- Original module: KroneckerMatrixCokernelEquivalence -/
section
/-! Cokernels throughout a matrix chart are linearly isomorphic to one fixed
space, with a continuous formula for every quotient representative. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixCokernelEquivalence
open KroneckerMatrixCokernelChart KroneckerMatrixCokernelProjection
open KroneckerMatrixCokernelLinearProjection
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
def equiv (R : Matrix v w ℂ) (I : Domain R) :
    ((w → ℂ) ⧸ LinearMap.range (Matrix.toLin' I.val)) ≃ₗ[ℂ] LinearMap.ker (Matrix.toLin' R) :=
  (Submodule.quotEquivOfEq _ _ (kernel_eq_range R I).symm).trans
    ((project R I).quotKerEquivOfSurjective (surjective R I))
theorem on_representatives (R : Matrix v w ℂ) (I : Domain R) (x : w → ℂ) :
    equiv R I ((LinearMap.range (Matrix.toLin' I.val)).mkQ x)=project R I x := by
  simp [equiv]
theorem joint_representatives (R : Matrix v w ℂ) :
    Continuous (fun z : Domain R × (w → ℂ) =>
      (equiv R z.1 ((LinearMap.range (Matrix.toLin' z.1.val)).mkQ z.2)).val) := by
  simp only [on_representatives]
  exact ((continuous_projection R).comp continuous_fst).matrix_mulVec continuous_snd
end KroneckerMatrixCokernelEquivalence
end
end

/- Original module: KroneckerPairOutgoingRangeDictionary -/
section
/-! Flattening sends the abstract outgoing image exactly onto the matrix
outgoing image, supplying the required hypothesis for quotient transport. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairOutgoingRangeDictionary
open KroneckerPairMatrixCoordinates KroneckerPairMatrixOutgoing KroneckerPairMatrixIncoming
variable {m a b : ℕ}
theorem range_eq (M : Matrices m a b) :
    (LinearMap.range (KroneckerAbstractOutgoingNaturality.outgoing (pair M))).map flatten.toLinearMap =
      LinearMap.range (Matrix.toLin' (outgoing M)) := by
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨z,evaluate M z⟩
  · rintro ⟨z,rfl⟩
    exact ⟨KroneckerAbstractOutgoingNaturality.outgoing (pair M) z,⟨z,rfl⟩,(evaluate M z).symm⟩
end KroneckerPairOutgoingRangeDictionary
end
end

/- Original module: KroneckerPairOutgoingQuotientDictionary -/
section
/-! The actual abstract cokernel and the flattened matrix quotient are
linearly equivalent, with a specified formula on quotient representatives. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairOutgoingQuotientDictionary
open KroneckerPairMatrixCoordinates KroneckerPairMatrixOutgoing KroneckerPairMatrixIncoming
variable {m a b : ℕ}
def equiv (M : Matrices m a b) : KroneckerAbstractCokernelReflection.Cokernel (pair M) ≃ₗ[ℂ]
    (((Fin m × Fin b) → ℂ) ⧸ LinearMap.range (Matrix.toLin' (outgoing M))) :=
  Submodule.Quotient.equiv _ _ flatten (KroneckerPairOutgoingRangeDictionary.range_eq M)
theorem on_representatives (M : Matrices m a b) (x : Fin m → Fin b → ℂ) :
    equiv M (KroneckerAbstractCokernelReflection.quotient (pair M) x)=
      (LinearMap.range (Matrix.toLin' (outgoing M))).mkQ (flatten x) := rfl
end KroneckerPairOutgoingQuotientDictionary
end
end

/- Original module: KroneckerStableCokernelChartDimension -/
section
/-! The fixed retraction kernel has exactly the source-reflection target
dimension, proved via the actual cokernel equivalences at a stable chart point. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableCokernelChartDimension
open KroneckerStableMatrixCokernelCover KroneckerPairMatrixCoordinates
variable {m a b : ℕ} (R : Matrix (Fin a) (Fin m × Fin b) ℂ) (M₀ : chart R)
def equivalence : KroneckerAbstractCokernelReflection.Cokernel (pair M₀.val.val) ≃ₗ[ℂ]
    LinearMap.ker (Matrix.toLin' R) :=
  (KroneckerPairOutgoingQuotientDictionary.equiv M₀.val.val).trans
    (KroneckerMatrixCokernelEquivalence.equiv R (parameter R M₀))
include M₀ in
theorem dimension (hb : 0<b) : Module.finrank ℂ (LinearMap.ker (Matrix.toLin' R))=m*b-a := by
  rw [← (equivalence R M₀).finrank_eq]
  exact KroneckerCokernelDimension.dimension _
    (KroneckerReflectionOutgoingMap.outgoing_injective _ hb M₀.val.property)
end KroneckerStableCokernelChartDimension
end
end

/- Original module: KroneckerStableCokernelChartFrame -/
section
/-! A basis of the fixed retraction kernel coordinates every moving cokernel
in its canonical finite dimension, with an explicit representative formula. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableCokernelChartFrame
open KroneckerStableMatrixCokernelCover KroneckerPairMatrixCoordinates KroneckerFiniteQuiverHom
variable {m a b : ℕ} (hb : 0<b) (R : Matrix (Fin a) (Fin m × Fin b) ℂ) (M₀ : chart R)
def baseCoordinates : LinearMap.ker (Matrix.toLin' R) ≃ₗ[ℂ] Space (m*b-a) :=
  (Module.finBasisOfFinrankEq ℂ _ (KroneckerStableCokernelChartDimension.dimension R M₀ hb)).equivFun
def coordinates (M : chart R) :
    KroneckerAbstractCokernelReflection.Cokernel (pair M.val.val) ≃ₗ[ℂ] Space (m*b-a) :=
  ((KroneckerPairOutgoingQuotientDictionary.equiv M.val.val).trans
    (KroneckerMatrixCokernelEquivalence.equiv R (parameter R M))).trans (baseCoordinates hb R M₀)
set_option backward.isDefEq.respectTransparency false in
theorem formula (M : chart R) (x : Fin m → Fin b → ℂ) :
    coordinates hb R M₀ M (KroneckerAbstractCokernelReflection.quotient (pair M.val.val) x)=
      baseCoordinates hb R M₀ (KroneckerMatrixCokernelLinearProjection.project R (parameter R M)
        (KroneckerPairMatrixIncoming.flatten x)) := by
  simp only [coordinates,LinearEquiv.trans_apply]
  rw [KroneckerPairOutgoingQuotientDictionary.on_representatives]
  exact congrArg (baseCoordinates hb R M₀)
    (KroneckerMatrixCokernelEquivalence.on_representatives R (parameter R M)
      (KroneckerPairMatrixIncoming.flatten x))
end KroneckerStableCokernelChartFrame
end
end

/- Original module: KroneckerStableCokernelLocalFamily -/
section
/-! The cokernel chart coordinates define stable source-reflected matrix
families, with actual canonical dimensions and no assumed moduli comparison. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableCokernelLocalFamily
open KroneckerStableMatrixCokernelCover KroneckerPairMatrixCoordinates KroneckerStableRectangularMatrices
variable {m a b : ℕ} (hb : 0<b) (R : Matrix (Fin a) (Fin m × Fin b) ℂ) (M₀ : chart R)
def pairFamily (M : chart R) : KroneckerReflectionPairModel.PairRep m b (m*b-a) :=
  KroneckerCokernelCoordinateFamily.family (pair M.val.val)
    (KroneckerStableCokernelChartFrame.coordinates hb R M₀ M)
theorem stable (M : chart R) : KroneckerReflectionPairModel.PairStable (pairFamily hb R M₀ M) :=
  KroneckerCokernelCoordinateFamily.stable _ hb M.val.property _
def family (M : chart R) : Stable m b (m*b-a) :=
  ⟨matrices (pairFamily hb R M₀ M),by rw [pair_matrices];exact stable hb R M₀ M⟩
end KroneckerStableCokernelLocalFamily
end
end

/- Original module: KroneckerStableCokernelLocalContinuity -/
section
/-! Actual local source-reflected matrix families are continuous: their
coefficients are fixed linear coordinates of the continuous quotient projection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableCokernelLocalContinuity
open KroneckerStableMatrixCokernelCover KroneckerStableCokernelLocalFamily
variable {m a b : ℕ} (hb : 0<b) (R : Matrix (Fin a) (Fin m × Fin b) ℂ) (M₀ : chart R)
theorem representative_continuous (x : Fin m → Fin b → ℂ) :
    Continuous (fun M : chart R => KroneckerStableCokernelChartFrame.coordinates hb R M₀ M
      (KroneckerAbstractCokernelReflection.quotient (KroneckerPairMatrixCoordinates.pair M.val.val) x)) := by
  simp only [KroneckerStableCokernelChartFrame.formula]
  apply (KroneckerStableCokernelChartFrame.baseCoordinates hb R M₀).toLinearMap.continuous_of_finiteDimensional.comp
  apply Continuous.subtype_mk
  exact ((KroneckerMatrixCokernelProjection.continuous_projection R).comp
    (continuous_parameter R)).matrix_mulVec continuous_const
theorem continuous_family : Continuous (family hb R M₀) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  apply continuous_pi; intro k
  exact (continuous_apply j).comp
    (representative_continuous hb R M₀ (Pi.single i (Pi.single k 1)))
end KroneckerStableCokernelLocalContinuity
end
end

/- Original module: KroneckerStableCokernelLocalOrbit -/
section
/-! The continuous local cokernel family projects to the canonical source
reflection, identifying the local formula with the existing quotient map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableCokernelLocalOrbit
open KroneckerPairMatrixCoordinates KroneckerStableMatrixCokernelCover KroneckerStableCokernelLocalFamily
variable {m a b : ℕ} (hb : 0<b) (R : Matrix (Fin a) (Fin m × Fin b) ℂ) (M₀ : chart R)
theorem agrees (M : chart R) :
    KroneckerStableMatrixProjection.project m b (m*b-a) (family hb R M₀ M) =
      KroneckerCanonicalSourceReflectionMap.map m a b hb (KroneckerStableMatrixProjection.project m a b M.val) := by
  rw [KroneckerStableMatrixProjection.pair_project,KroneckerStableMatrixProjection.pair_project,
    KroneckerCanonicalSourceReflectionMap.on_representatives]
  apply (KroneckerStablePairProjection.eq_iff _ _ _ _ _).mpr
  refine ⟨?_⟩
  change KroneckerAbstractPairIso.Iso (pair (matrices (pairFamily hb R M₀ M))) _
  rw [pair_matrices]
  exact KroneckerCokernelCoordinateFamily.canonicalIso (pair M.val.val) _ _
end KroneckerStableCokernelLocalOrbit
end
end

/- Original module: KroneckerCanonicalSourceReflectionContinuous -/
section
/-! Canonical source reflection is continuous on the actual stable matrix
quotient topology, by its proved continuous local quotient-coordinate lifts. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalSourceReflectionContinuous
open KroneckerStableCokernelBasedCover
theorem continuous (m a b : ℕ) (hb : 0<b) :
    Continuous (KroneckerCanonicalSourceReflectionMap.map m a b hb) := by
  apply KroneckerQuotientLocalLifts.continuous
    (KroneckerStableMatrixProjection.project m a b)
    (KroneckerStableMatrixProjection.quotient_project m a b)
    (KroneckerStableMatrixProjection.project m b (m*b-a))
    (KroneckerStableMatrixProjection.continuous_project m b (m*b-a))
    (KroneckerCanonicalSourceReflectionMap.map m a b hb)
    (domain m a b) (domain_open m a b) (cover m a b hb)
    (fun c => KroneckerStableCokernelLocalFamily.family hb c.1 c.2)
    (fun c => KroneckerStableCokernelLocalContinuity.continuous_family hb c.1 c.2)
    (fun c => KroneckerStableCokernelLocalOrbit.agrees hb c.1 c.2)
end KroneckerCanonicalSourceReflectionContinuous
end
end

/- Original module: KroneckerCanonicalReflectionInverseContinuous -/
section
/-! The inverse of canonical reflection is continuous by the exact global
source-reflection formula; bijectivity alone is not used to infer continuity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionInverseContinuous
theorem continuous (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) :
    Continuous (KroneckerCanonicalReflectionEquivalence.equiv m a b ha hb).symm := by
  rw [KroneckerCanonicalReflectionInverseFormula.inverse]
  exact (KroneckerCanonicalDimensionHomeomorphism.homeomorph rfl (Nat.sub_sub_self hb)).continuous.comp
    (KroneckerCanonicalSourceReflectionContinuous.continuous m (m*a-b) a ha)
end KroneckerCanonicalReflectionInverseContinuous
end
end

/- Original module: KroneckerCanonicalReflectionHomeomorphism -/
section
/-! Canonical sink reflection is a homeomorphism of actual stable matrix
orbit spaces, including empty cases and zero reflected-source dimensions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionHomeomorphism
open KroneckerCanonicalKroneckerModuli
def homeomorph (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) :
    space m a b ≃ₜ space m (m*a-b) a where
  toEquiv := KroneckerCanonicalReflectionEquivalence.equiv m a b ha hb
  continuous_toFun := KroneckerCanonicalReflectionContinuous.continuous m a b ha
  continuous_invFun := KroneckerCanonicalReflectionInverseContinuous.continuous m a b ha hb
end KroneckerCanonicalReflectionHomeomorphism
end
end
