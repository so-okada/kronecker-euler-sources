import KroneckerSlopeSymmetry

section

/-! The real sink-reflection map preserves the strict root interval and
strictly decreases every interior slope, providing a genuine reduction dynamics. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealReflectionDynamics
open KroneckerEndpointRoots
def step (m r : ℝ) : ℝ := (m-r)⁻¹
theorem denominator {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) : 0<m-r := by
  have hs := root_sum m
  have hp := lowerRoot_positive hm
  linarith [hr.2]
theorem interior {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    step m r∈Set.Ioo (lowerRoot m) (upperRoot m) := by
  simpa [step,KroneckerSlopeSymmetry.exchange,KroneckerSlopeSymmetry.reflect] using
    KroneckerSlopeSymmetry.exchange_mem_interior hm (KroneckerSlopeSymmetry.reflect_mem_interior hm hr)
theorem decrease {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) : step m r<r := by
  have hq : 0<KroneckerSlopeSymmetry.slopeQuadratic m r := by
    rw [← KroneckerSlopeSymmetry.root_gap_product hm.le]
    exact mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr hr.1)
  simpa [step,KroneckerSlopeSymmetry.exchange,KroneckerSlopeSymmetry.reflect] using
    KroneckerSlopeSymmetry.combined_decreases hq (denominator hm hr)
end KroneckerRealReflectionDynamics
end
end

section

/-! Iterated real reflection stays inside the root interval and forms a
strictly decreasing sequence for every interior starting slope. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealReflectionIterates
open KroneckerEndpointRoots KroneckerRealReflectionDynamics
def orbit (m r : ℝ) : ℕ → ℝ
  | 0 => r
  | n+1 => step m (orbit m r n)
theorem interior {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) (n : ℕ) :
    orbit m r n∈Set.Ioo (lowerRoot m) (upperRoot m) := by
  induction n with
  | zero => exact hr
  | succ n ih => exact KroneckerRealReflectionDynamics.interior hm ih
end KroneckerRealReflectionIterates
end
end

