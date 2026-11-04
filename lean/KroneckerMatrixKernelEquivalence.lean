import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

section

noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixInverseContinuity
variable {n : Type} [Fintype n] [DecidableEq n]
theorem inverse_at (A : Matrix n n ℂ) (hA : A.det ≠ 0) :
    ContinuousAt (fun B : Matrix n n ℂ => B⁻¹) A := by
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hA)
theorem domain_open : IsOpen {A : Matrix n n ℂ | A.det ≠ 0} :=
  isOpen_ne.preimage continuous_id.matrix_det
end KroneckerMatrixInverseContinuity
end
end

section

/- Original module: KroneckerMatrixCokernelChart -/
section
/-! Fixed retractions give open charts for moving injective matrices. The
corrected injection is continuous and remains a right inverse of the retraction. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixCokernelChart
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v]
def Domain (R : Matrix v w ℂ) := {I : Matrix w v ℂ | (R * I).det ≠ 0}
theorem isOpen_domain (R : Matrix v w ℂ) : IsOpen (Domain R) :=
  KroneckerMatrixInverseContinuity.domain_open.preimage
    (continuous_const.matrix_mul continuous_id)
theorem inverse_continuous (R : Matrix v w ℂ) :
    Continuous (fun I : Domain R => (R * I.val)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro I
  exact (KroneckerMatrixInverseContinuity.inverse_at (R*I.val) I.property).comp
    (f := fun J : Domain R => R * J.val)
    (continuous_const.matrix_mul continuous_subtype_val).continuousAt
def corrected (R : Matrix v w ℂ) (I : Domain R) : Matrix w v ℂ := I.val * (R*I.val)⁻¹
theorem continuous_corrected (R : Matrix v w ℂ) : Continuous (corrected R) :=
  continuous_subtype_val.matrix_mul (inverse_continuous R)
theorem right_inverse (R : Matrix v w ℂ) (I : Domain R) : R * corrected R I = 1 := by
  unfold corrected
  rw [← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.property)]
end KroneckerMatrixCokernelChart
end
end

/- Original module: KroneckerMatrixCokernelProjection -/
section
/-! The moving quotient is represented by a continuous projection onto a
fixed retraction kernel. Its kernel contains the moving injection image. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixCokernelProjection
open KroneckerMatrixCokernelChart
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
def projection (R : Matrix v w ℂ) (I : Domain R) : Matrix w w ℂ :=
  1 - corrected R I * R
theorem continuous_projection (R : Matrix v w ℂ) : Continuous (projection R) :=
  continuous_const.sub ((continuous_corrected R).matrix_mul continuous_const)
theorem image_in_kernel (R : Matrix v w ℂ) (I : Domain R) : R * projection R I = 0 := by
  unfold projection
  rw [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc,right_inverse,Matrix.one_mul,sub_self]
theorem kills_injection (R : Matrix v w ℂ) (I : Domain R) : projection R I * I.val = 0 := by
  unfold projection corrected
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr I.property),Matrix.mul_one,sub_self]
theorem fixes_kernel (R : Matrix v w ℂ) (I : Domain R) (x : w → ℂ) (hx : R *ᵥ x=0) :
    projection R I *ᵥ x=x := by
  simp only [projection,Matrix.sub_mulVec,Matrix.one_mulVec,← Matrix.mulVec_mulVec,hx,
    Matrix.mulVec_zero,sub_zero]
end KroneckerMatrixCokernelProjection
end
end

/- Original module: KroneckerMatrixCokernelExactness -/
section
/-! The complement projection has exactly the moving image as kernel,
so its quotient coordinates do not collapse additional vectors. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixCokernelExactness
open KroneckerMatrixCokernelChart KroneckerMatrixCokernelProjection
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
theorem kernel_eq_range (R : Matrix v w ℂ) (I : Domain R) :
    LinearMap.ker (Matrix.toLin' (projection R I)) = LinearMap.range (Matrix.toLin' I.val) := by
  ext x
  constructor
  · intro hx
    change projection R I *ᵥ x=0 at hx
    simp only [projection,corrected,Matrix.sub_mulVec,Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec,sub_eq_zero] at hx
    exact ⟨(R*I.val)⁻¹ *ᵥ (R *ᵥ x),hx.symm⟩
  · rintro ⟨y,rfl⟩
    change projection R I *ᵥ (I.val *ᵥ y)=0
    rw [Matrix.mulVec_mulVec,kills_injection,Matrix.zero_mulVec]
end KroneckerMatrixCokernelExactness
end
end
end

section

/- Original module: KroneckerMatrixKernelChart -/
section
/-! A single fixed section supplies an open matrix chart, with continuous
inversion of the moving target block. No rank-stratum topology is assumed. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixKernelChart
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq w]
def Domain (S : Matrix v w ℂ) := {P : Matrix w v ℂ | (P * S).det ≠ 0}
theorem isOpen_domain (S : Matrix v w ℂ) : IsOpen (Domain S) :=
  KroneckerMatrixInverseContinuity.domain_open.preimage
    (continuous_id.matrix_mul continuous_const)
theorem inverse_continuous (S : Matrix v w ℂ) :
    Continuous (fun P : Domain S => (P.val * S)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro P
  exact (KroneckerMatrixInverseContinuity.inverse_at (P.val*S) P.property).comp (f := fun Q : Domain S => Q.val * S)
    (continuous_subtype_val.matrix_mul continuous_const).continuousAt
def sectionMatrix (S : Matrix v w ℂ) (P : Domain S) : Matrix v w ℂ :=
  S * (P.val * S)⁻¹
theorem section_continuous (S : Matrix v w ℂ) : Continuous (sectionMatrix S) :=
  continuous_const.matrix_mul (inverse_continuous S)
theorem section_right_inverse (S : Matrix v w ℂ) (P : Domain S) :
    P.val * sectionMatrix S P = 1 := by
  unfold sectionMatrix
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr P.property)]
end KroneckerMatrixKernelChart
end
end

/- Original module: KroneckerMatrixKernelProjection -/
section
/-! The open matrix chart has a continuous idempotent projection onto the
moving kernel, expressed without choosing moving basis vectors. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixKernelProjection
open KroneckerMatrixKernelChart
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
def projection (S : Matrix v w ℂ) (P : Domain S) : Matrix v v ℂ :=
  1 - sectionMatrix S P * P.val
theorem continuous_projection (S : Matrix v w ℂ) : Continuous (projection S) :=
  continuous_const.sub ((section_continuous S).matrix_mul continuous_subtype_val)
theorem annihilated (S : Matrix v w ℂ) (P : Domain S) : P.val * projection S P = 0 := by
  unfold projection
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, section_right_inverse,
    Matrix.one_mul, sub_self]
theorem idempotent (S : Matrix v w ℂ) (P : Domain S) :
    projection S P * projection S P = projection S P := by
  nth_rw 1 [projection]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    annihilated, Matrix.mul_zero, sub_zero]
theorem fixes_kernel (S : Matrix v w ℂ) (P : Domain S) (x : v → ℂ)
    (hx : P.val *ᵥ x = 0) : projection S P *ᵥ x = x := by
  simp only [projection, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    hx, Matrix.mulVec_zero, sub_zero]
end KroneckerMatrixKernelProjection
end
end

/- Original module: KroneckerMatrixKernelTransition -/
section
/-! Projections defined using the same fixed section have absorption identities.
These identities give explicit inverse maps between the two kernels. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixKernelTransition
open KroneckerMatrixKernelChart KroneckerMatrixKernelProjection
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
theorem kills_section (S : Matrix v w ℂ) (P : Domain S) : projection S P * S = 0 := by
  unfold projection sectionMatrix
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr P.property), Matrix.mul_one, sub_self]
theorem absorbs (S : Matrix v w ℂ) (P Q : Domain S) :
    projection S P * projection S Q = projection S P := by
  change projection S P * (1 - sectionMatrix S Q * Q.val) = projection S P
  rw [Matrix.mul_sub, Matrix.mul_one]
  unfold sectionMatrix
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, kills_section, Matrix.zero_mul,
    Matrix.zero_mul, sub_zero]
theorem inverse_on_kernel (S : Matrix v w ℂ) (P Q : Domain S)
    (x : v → ℂ) (hx : P.val *ᵥ x = 0) :
    projection S P *ᵥ (projection S Q *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, absorbs, fixes_kernel S P x hx]
end KroneckerMatrixKernelTransition
end
end

/- Original module: KroneckerMatrixKernelEquivalence -/
section
/-! Any two kernels in a fixed-section chart are linearly equivalent, with
both directions given by the proved matrix projections. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixKernelEquivalence
open KroneckerMatrixKernelChart KroneckerMatrixKernelProjection KroneckerMatrixKernelTransition
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
def kernel (P : Matrix w v ℂ) := LinearMap.ker (Matrix.toLin' P)
def map (S : Matrix v w ℂ) (P Q : Domain S) : kernel P.val →ₗ[ℂ] kernel Q.val where
  toFun x := ⟨projection S Q *ᵥ x.val,by
    change Q.val *ᵥ (projection S Q *ᵥ x.val)=0
    rw [Matrix.mulVec_mulVec,annihilated,Matrix.zero_mulVec]⟩
  map_add' x y := by apply Subtype.ext;exact Matrix.mulVec_add _ _ _
  map_smul' c x := by apply Subtype.ext;exact Matrix.mulVec_smul _ _ _
def equiv (S : Matrix v w ℂ) (P Q : Domain S) : kernel P.val ≃ₗ[ℂ] kernel Q.val where
  toLinearMap := map S P Q
  invFun := map S Q P
  left_inv x := by apply Subtype.ext;exact inverse_on_kernel S P Q x.val x.property
  right_inv x := by apply Subtype.ext;exact inverse_on_kernel S Q P x.val x.property
end KroneckerMatrixKernelEquivalence
end
end
end

