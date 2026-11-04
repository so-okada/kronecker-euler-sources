import KroneckerPairDimensionTransport
import KroneckerCoordinateKernelReflectionIso

section

/- Original module: KroneckerPairGaugeIsoDictionary -/
section
/-! Actual matrix gauge equivalence is exactly isomorphism of the two-space
arrow families. This is the bridge required to descend reflection to canonical orbits. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairGaugeIsoDictionary
open KroneckerCanonicalKroneckerModuli KroneckerReflectionPairModel
open KroneckerRingQuiverFamilies
variable (m a b : ℕ)

def family (R : PairRep m a b) : Family (source m) (target m) (dimension a b) ℂ :=
  ofRepresentation (source m) (target m) (dimension a b) (KroneckerReflectionPairModel.toRepresentation R)

theorem representation_family (R : PairRep m a b) :
    KroneckerRingQuiverFamilies.toRepresentation (source m) (target m) (dimension a b) (family m a b R)=
      KroneckerReflectionPairModel.toRepresentation R := by
  exact (complexRepresentationEquiv (source m) (target m) (dimension a b)).apply_symm_apply _

theorem gauge_iff (R S : PairRep m a b) :
    (∃ g : Gauge (dimension a b) ℂ,gauge (source m) (target m) (dimension a b) g (family m a b R)=family m a b S) ↔
      Nonempty (KroneckerAbstractPairIso.Iso R S) := by
  rw [complex_orbit_iff_iso,representation_family,representation_family]
  exact KroneckerPairIsoCanonicalDictionary.isomorphic_iff.symm
end KroneckerPairGaugeIsoDictionary
end
end

/- Original module: KroneckerStablePairFamilyEquivalence -/
section
/-! Actual stable two-space families and canonical stable matrix families
are equivalent, with explicit forward and inverse coordinate maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStablePairFamilyEquivalence
open KroneckerReflectionPairModel KroneckerCanonicalKroneckerModuli
open KroneckerStableOrbitEuler

abbrev StablePair (m a b : ℕ) := {R : PairRep m a b // PairStable R}
abbrev StableMatrix (m a b : ℕ) := StableFamily (source m) (target m) (dimension a b) (character a b)

def toMatrix (m a b : ℕ) (R : StablePair m a b) : StableMatrix m a b :=
  ⟨KroneckerPairGaugeIsoDictionary.family m a b R.val,by
    rw [KroneckerPairGaugeIsoDictionary.representation_family]
    exact (KroneckerReflectionPairStability.stable_iff R.val).mpr R.property⟩

def fromMatrix (m a b : ℕ) (M : StableMatrix m a b) : StablePair m a b :=
  ⟨fromRepresentation (KroneckerRingQuiverFamilies.toRepresentation (source m) (target m) (dimension a b) M.val),
    (KroneckerReflectionPairStability.stable_iff _).mp M.property⟩

def equiv (m a b : ℕ) : StablePair m a b ≃ StableMatrix m a b where
  toFun := toMatrix m a b
  invFun := fromMatrix m a b
  left_inv R := by
    apply Subtype.ext
    exact congrArg (fun P => P.arrow) (KroneckerPairGaugeIsoDictionary.representation_family m a b R.val)
  right_inv M := by
    apply Subtype.ext
    exact (KroneckerRingQuiverFamilies.complexRepresentationEquiv (source m) (target m) (dimension a b)).symm_apply_apply M.val
end KroneckerStablePairFamilyEquivalence
end
end
end

section

/-! Stable two-space representations surject onto the actual canonical
moduli orbit space, and fibers are exactly actual representation isomorphism classes. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStablePairProjection
open KroneckerCanonicalKroneckerModuli KroneckerStablePairFamilyEquivalence

 def project (m a b : ℕ) (R : StablePair m a b) : space m a b :=
  KroneckerCanonicalStableOrbit.project (source m) (target m) (dimension a b) (character a b) (toMatrix m a b R)

theorem surjective (m a b : ℕ) : Function.Surjective (project m a b) :=
  (KroneckerCanonicalStableOrbit.project_surjective (source m) (target m) (dimension a b) (character a b)).comp
    (equiv m a b).surjective

set_option backward.isDefEq.respectTransparency false in
theorem eq_iff (m a b : ℕ) (R S : StablePair m a b) :
    project m a b R=project m a b S ↔ Nonempty (KroneckerAbstractPairIso.Iso R.val S.val) := by
  rw [project,project,KroneckerCanonicalStableOrbit.project_eq_iff]
  exact KroneckerPairGaugeIsoDictionary.gauge_iff m a b R.val S.val

theorem fromMatrix_project (m a b : ℕ) (M : StableMatrix m a b) :
    project m a b (fromMatrix m a b M)=
      KroneckerCanonicalStableOrbit.project (source m) (target m) (dimension a b) (character a b) M := by
  unfold project
  rw [show toMatrix m a b (fromMatrix m a b M)=M from (equiv m a b).apply_symm_apply M]
end KroneckerStablePairProjection
end
end

section

/- Original module: KroneckerCoordinateReflectionIsomorphism -/
section
/-! Canonical coordinate reflection preserves and reflects isomorphism of
actual incoming-surjective representations, independently of the chosen kernel bases. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCoordinateReflectionIsomorphism
open KroneckerReflectionPairModel KroneckerAbstractPairIso
open KroneckerReflectionKernelCoordinates KroneckerReflectionIncomingMap
variable {m a b : ℕ} {R S : PairRep m a b}

def forward (hR : Function.Surjective (incoming R)) (hS : Function.Surjective (incoming S))
    (e : Iso R S) : Iso (reflected R hR) (reflected S hS) :=
  trans (symm (KroneckerCoordinateKernelReflectionIso.coordinateIso R hR))
    (trans (KroneckerKernelReflectionIso.reflectedIso e) (KroneckerCoordinateKernelReflectionIso.coordinateIso S hS))

def backward (hR : Function.Surjective (incoming R)) (hS : Function.Surjective (incoming S))
    (e : Iso (reflected R hR) (reflected S hS)) : Iso R S :=
  KroneckerKernelReflectionReflectsIso.liftIso hR hS
    (trans (KroneckerCoordinateKernelReflectionIso.coordinateIso R hR)
      (trans e (symm (KroneckerCoordinateKernelReflectionIso.coordinateIso S hS))))

theorem isomorphic_iff (hR : Function.Surjective (incoming R)) (hS : Function.Surjective (incoming S)) :
    Nonempty (Iso R S) ↔ Nonempty (Iso (reflected R hR) (reflected S hS)) :=
  ⟨fun ⟨e⟩ => ⟨forward hR hS e⟩,fun ⟨e⟩ => ⟨backward hR hS e⟩⟩
end KroneckerCoordinateReflectionIsomorphism
end
end

/- Original module: KroneckerStablePairReflection -/
section
/-! Canonical sink reflection maps actual stable two-space families to
actual stable families and preserves and reflects their orbit relation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStablePairReflection
open KroneckerCanonicalKroneckerModuli KroneckerStablePairFamilyEquivalence
open KroneckerReflectionKernelCoordinates

 def incoming_surjective (m a b : ℕ) (ha : 0<a) (R : StablePair m a b) :=
  KroneckerReflectionStableSurjectivity.incoming_surjective R.val ha R.property

def reflect (m a b : ℕ) (ha : 0<a) (R : StablePair m a b) : StablePair m (m*a-b) a :=
  ⟨reflected R.val (incoming_surjective m a b ha R),
    KroneckerReflectionCoordinateStability.reflected_stable R.val ha R.property (incoming_surjective m a b ha R)⟩

theorem isomorphic_iff (m a b : ℕ) (ha : 0<a) (R S : StablePair m a b) :
    Nonempty (KroneckerAbstractPairIso.Iso R.val S.val) ↔
      Nonempty (KroneckerAbstractPairIso.Iso (reflect m a b ha R).val (reflect m a b ha S).val) :=
  KroneckerCoordinateReflectionIsomorphism.isomorphic_iff
    (incoming_surjective m a b ha R) (incoming_surjective m a b ha S)
end KroneckerStablePairReflection
end
end
end

