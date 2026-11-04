import KroneckerPairIsoStability
import KroneckerCanonicalReflectionMap

/- Original module: KroneckerKernelCoordinateFamily -/
section
/-! Any linear coordinate frame of the actual incoming kernel realizes the
same reflected representation, with a specified abstract pair isomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerKernelCoordinateFamily
open KroneckerReflectionPairModel KroneckerFiniteQuiverHom
open KroneckerAbstractKernelReflection
variable {m a b k : ℕ} (R : PairRep m a b) (e : Space k ≃ₗ[ℂ] Kernel R)
def family : PairRep m k a := fun i => (reflection R i).comp e.toLinearMap
def iso : KroneckerAbstractPairIso.Iso (family R e) (reflection R) where
  source := e
  sink := LinearEquiv.refl ℂ _
  commutes _ _ := rfl
def canonicalIso (h : Function.Surjective (KroneckerReflectionIncomingMap.incoming R))
    (e : Space (m*a-b) ≃ₗ[ℂ] Kernel R) :
    KroneckerAbstractPairIso.Iso (family R e) (KroneckerReflectionKernelCoordinates.reflected R h) :=
  KroneckerAbstractPairIso.trans (iso R e) (KroneckerCoordinateKernelReflectionIso.coordinateIso R h)
theorem stable (ha : 0<a) (hs : PairStable R)
    (e : Space (m*a-b) ≃ₗ[ℂ] Kernel R) : PairStable (family R e) := by
  let h := KroneckerReflectionStableSurjectivity.incoming_surjective R ha hs
  exact (KroneckerPairIsoStability.stable_iff (canonicalIso R h e)).mpr
    (KroneckerReflectionCoordinateStability.reflected_stable R ha hs h)
end KroneckerKernelCoordinateFamily
end
end

/- Original module: KroneckerPairIncomingKernelDictionary -/
section
/-! Flattening identifies the abstract incoming kernel with the rectangular
matrix kernel, and preserves every coordinate used by the reflected arrows. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairIncomingKernelDictionary
open KroneckerPairMatrixCoordinates KroneckerPairMatrixIncoming
variable {m a b : ℕ}
def equiv (M : Matrices m a b) : KroneckerAbstractKernelReflection.Kernel (pair M) ≃ₗ[ℂ]
    KroneckerMatrixKernelEquivalence.kernel (incoming M) where
  toFun x := ⟨flatten x.val,by change Matrix.toLin' (incoming M) (flatten x.val)=0;rw [evaluate];exact x.property⟩
  invFun x := ⟨flatten.symm x.val,by
    rw [LinearMap.mem_ker,← evaluate,LinearEquiv.apply_symm_apply];exact x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_smul' c x := Subtype.ext rfl
end KroneckerPairIncomingKernelDictionary
end
end

/- Original module: KroneckerStableKernelChartFrame -/
section
/-! A fixed coordinate frame at one stable base point is transported through
the matrix kernel chart into exact coordinates on each abstract incoming kernel. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerStableKernelChartFrame
open KroneckerPairMatrixCoordinates KroneckerStableRectangularMatrices KroneckerStableMatrixKernelCover
open KroneckerFiniteQuiverHom
variable {m a b : ℕ} (ha : 0<a) (S : Matrix (Fin m × Fin a) (Fin b) ℂ) (M₀ : chart S)
def baseFrame : Space (m*a-b) ≃ₗ[ℂ]
    KroneckerMatrixKernelEquivalence.kernel (KroneckerPairMatrixIncoming.incoming M₀.val.val) :=
  (KroneckerReflectionKernelCoordinates.coordinates (pair M₀.val.val)
    (KroneckerReflectionStableSurjectivity.incoming_surjective _ ha M₀.val.property)).symm.trans
      (KroneckerPairIncomingKernelDictionary.equiv M₀.val.val)
def frame (M : chart S) : Space (m*a-b) ≃ₗ[ℂ]
    KroneckerAbstractKernelReflection.Kernel (pair M.val.val) :=
  ((baseFrame ha S M₀).trans
    (KroneckerMatrixKernelEquivalence.equiv S (parameter S M₀) (parameter S M))).trans
      (KroneckerPairIncomingKernelDictionary.equiv M.val.val).symm
theorem formula (M : chart S) (x : Space (m*a-b)) (i : Fin m) (j : Fin a) :
    (frame ha S M₀ M x).val i j =
      (KroneckerMatrixKernelProjection.projection S (parameter S M) *ᵥ
        (baseFrame ha S M₀ x).val) (i,j) := rfl
end KroneckerStableKernelChartFrame
end
end

/- Original module: KroneckerStableKernelLocalFamily -/
section
/-! Moving kernel frames define stable reflected pair families at every
point of the stable matrix chart, with the exact canonical dimension vector. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableKernelLocalFamily
open KroneckerPairMatrixCoordinates KroneckerStableRectangularMatrices KroneckerStableMatrixKernelCover
variable {m a b : ℕ} (ha : 0<a) (S : Matrix (Fin m × Fin a) (Fin b) ℂ) (M₀ : chart S)
def pairFamily (M : chart S) : KroneckerReflectionPairModel.PairRep m (m*a-b) a :=
  KroneckerKernelCoordinateFamily.family (pair M.val.val) (KroneckerStableKernelChartFrame.frame ha S M₀ M)
theorem stable (M : chart S) : KroneckerReflectionPairModel.PairStable (pairFamily ha S M₀ M) :=
  KroneckerKernelCoordinateFamily.stable _ ha M.val.property _
def family (M : chart S) : Stable m (m*a-b) a :=
  ⟨matrices (pairFamily ha S M₀ M),by rw [pair_matrices];exact stable ha S M₀ M⟩
end KroneckerStableKernelLocalFamily
end
end

/- Original module: KroneckerStableKernelLocalContinuity -/
section
/-! The exact stable local reflected family is continuous: each arrow-matrix
coefficient is a continuous projection of a fixed base-frame basis vector. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerStableKernelLocalContinuity
open KroneckerPairMatrixCoordinates KroneckerStableMatrixKernelCover KroneckerStableKernelLocalFamily
variable {m a b : ℕ} (ha : 0<a) (S : Matrix (Fin m × Fin a) (Fin b) ℂ) (M₀ : chart S)
theorem coefficient (M : chart S) (i : Fin m) (j : Fin a) (k : Fin (m*a-b)) :
    (family ha S M₀ M).val i j k =
      (KroneckerMatrixKernelProjection.projection S (parameter S M) *ᵥ
        (KroneckerStableKernelChartFrame.baseFrame ha S M₀ (Pi.single k 1)).val) (i,j) := by
  rfl
theorem continuous_family : Continuous (family ha S M₀) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  apply continuous_pi; intro k
  change Continuous (fun M : chart S => (family ha S M₀ M).val i j k)
  simp only [coefficient]
  exact (continuous_apply (i,j)).comp
    (((KroneckerMatrixKernelProjection.continuous_projection S).comp
      (continuous_parameter S)).matrix_mulVec continuous_const)
end KroneckerStableKernelLocalContinuity
end
end

/- Original module: KroneckerStableKernelLocalOrbit -/
section
/-! The continuous local reflected family projects to the already-defined
canonical reflection, so no new map of moduli points is silently substituted. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableKernelLocalOrbit
open KroneckerPairMatrixCoordinates KroneckerStableMatrixKernelCover KroneckerStableKernelLocalFamily
variable {m a b : ℕ} (ha : 0<a) (S : Matrix (Fin m × Fin a) (Fin b) ℂ) (M₀ : chart S)
theorem agrees (M : chart S) :
    KroneckerStableMatrixProjection.project m (m*a-b) a (family ha S M₀ M) =
      KroneckerCanonicalReflectionMap.map m a b ha (KroneckerStableMatrixProjection.project m a b M.val) := by
  rw [KroneckerStableMatrixProjection.pair_project,KroneckerStableMatrixProjection.pair_project,
    KroneckerCanonicalReflectionMap.on_representatives]
  apply (KroneckerStablePairProjection.eq_iff _ _ _ _ _).mpr
  refine ⟨?_⟩
  change KroneckerAbstractPairIso.Iso (pair (matrices (pairFamily ha S M₀ M))) _
  rw [pair_matrices]
  exact KroneckerKernelCoordinateFamily.canonicalIso (pair M.val.val) _ _
end KroneckerStableKernelLocalOrbit
end
end
