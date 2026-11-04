import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The two real boundary slopes and their exact quadratic identities. -/
set_option autoImplicit false
namespace KroneckerEndpointRoots

noncomputable def discriminant (m : ℝ) : ℝ := Real.sqrt (m^2-4)
noncomputable def lowerRoot (m : ℝ) : ℝ := (m-discriminant m)/2
noncomputable def upperRoot (m : ℝ) : ℝ := (m+discriminant m)/2

theorem discriminant_sq {m : ℝ} (hm : 2 ≤ m) : discriminant m ^ 2=m^2-4 := by
  rw [discriminant,Real.sq_sqrt]
  nlinarith

theorem discriminant_nonnegative (m : ℝ) : 0 ≤ discriminant m := Real.sqrt_nonneg _

theorem discriminant_lt {m : ℝ} (hm : 2 < m) : discriminant m < m := by
  have hs := discriminant_sq hm.le
  have hd := discriminant_nonnegative m
  nlinarith

theorem root_sum (m : ℝ) : lowerRoot m+upperRoot m=m := by
  simp [lowerRoot,upperRoot]
  ring

theorem root_product {m : ℝ} (hm : 2 ≤ m) : lowerRoot m*upperRoot m=1 := by
  rw [lowerRoot,upperRoot]
  have hs := discriminant_sq hm
  nlinarith

theorem lowerRoot_positive {m : ℝ} (hm : 2 < m) : 0 < lowerRoot m := by
  rw [lowerRoot]
  have h := discriminant_lt hm
  linarith

theorem lower_lt_upper {m : ℝ} (hm : 2 < m) : lowerRoot m < upperRoot m := by
  rw [lowerRoot,upperRoot]
  have hs : 0 < discriminant m := Real.sqrt_pos.mpr (by nlinarith)
  linarith

theorem upperRoot_positive {m : ℝ} (hm : 2 < m) : 0 < upperRoot m :=
  (lowerRoot_positive hm).trans (lower_lt_upper hm)

theorem lowerRoot_lt_one {m : ℝ} (hm : 2 < m) : lowerRoot m < 1 := by
  have hp := root_product hm.le
  have hlo := lowerRoot_positive hm
  have hu : 1 < upperRoot m := by
    rw [upperRoot]
    have hs : m < m+discriminant m := by
      have : 0 < discriminant m := Real.sqrt_pos.mpr (by nlinarith)
      linarith
    linarith
  nlinarith

theorem one_lt_upperRoot {m : ℝ} (hm : 2 < m) : 1 < upperRoot m := by
  have hp := root_product hm.le
  have hlo := lowerRoot_positive hm
  have hlt := lowerRoot_lt_one hm
  nlinarith

theorem upperRoot_gt_m_sub_one {m : ℝ} (hm : 2 < m) : m-1 < upperRoot m := by
  rw [upperRoot]
  have hs : m-2 < discriminant m := by
    have hsq := discriminant_sq hm.le
    have hm2 : 0 < m-2 := by linarith
    have hd := discriminant_nonnegative m
    nlinarith
  linarith

theorem lowerRoot_lt_half {m : ℝ} (hm : 2 < m) : lowerRoot m < m/2 := by
  rw [lowerRoot]
  have : 0 < discriminant m := Real.sqrt_pos.mpr (by nlinarith)
  linarith

theorem upperRoot_gt_half {m : ℝ} (hm : 2 < m) : m/2 < upperRoot m := by
  rw [upperRoot]
  have : 0 < discriminant m := Real.sqrt_pos.mpr (by nlinarith)
  linarith

theorem lowerRoot_quadratic {m : ℝ} (hm : 2 ≤ m) :
    m*lowerRoot m-1-(lowerRoot m)^2=0 := by
  have hs := root_sum m
  have hp := root_product hm
  nlinarith

theorem upperRoot_quadratic {m : ℝ} (hm : 2 ≤ m) :
    m*upperRoot m-1-(upperRoot m)^2=0 := by
  have hs := root_sum m
  have hp := root_product hm
  nlinarith

theorem quadratic_factorization {m r : ℝ} (hm : 2 ≤ m) :
    m*r-1-r^2=(upperRoot m-r)*(r-lowerRoot m) := by
  have hs := root_sum m
  have hp := root_product hm
  calc
    m*r-1-r^2=(lowerRoot m+upperRoot m)*r-lowerRoot m*upperRoot m-r^2 := by
      rw [hs,hp]
    _=(upperRoot m-r)*(r-lowerRoot m) := by ring

end KroneckerEndpointRoots
