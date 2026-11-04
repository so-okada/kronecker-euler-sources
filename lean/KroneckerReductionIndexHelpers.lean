import KroneckerApproachingDimensionReduction
import KroneckerRootCrossRatioOrbit

/-! The explicit stopping index for the finite reflection word. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerReductionIndexHelpers
open KroneckerEndpointRoots KroneckerRootCrossRatio
open KroneckerRealReflectionIterates KroneckerRealReflectionFiniteHit

theorem ratio_strictMono (m : ℝ) (hm : 2 < m) :
    StrictMonoOn (ratio m) (Set.Ioo (lowerRoot m) (upperRoot m)) := by
  intro a ha b hb hab
  unfold ratio
  apply (div_lt_div_iff₀ (sub_pos.mpr ha.2) (sub_pos.mpr hb.2)).mpr
  have hroots := lower_lt_upper hm
  nlinarith

theorem ratio_le_threshold (m t : ℝ) (hm : 2 < m)
    (ht : t ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    ratio m t ≤ upperRoot m ↔ t ≤ m-1 := by
  have hb := upperRoot_positive hm
  have hs := root_sum m
  have hq := upperRoot_quadratic hm.le
  unfold ratio
  rw [div_le_iff₀ (sub_pos.mpr ht.2)]
  have hc : (upperRoot m)^2+lowerRoot m = (1+upperRoot m)*(m-1) := by nlinarith
  constructor
  · intro h
    apply (mul_le_mul_iff_right₀ (show 0 < 1+upperRoot m by linarith)).mp
    nlinarith
  · intro h
    have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ 1+upperRoot m by linarith)
    nlinarith

theorem log_lower (m : ℝ) (hm : 2 < m) :
    Real.log (lowerRoot m) = -Real.log (upperRoot m) := by
  have h := Real.log_mul (ne_of_gt (lowerRoot_positive hm))
    (ne_of_gt (upperRoot_positive hm))
  rw [root_product hm.le, Real.log_one] at h
  linarith

theorem log_ratio_orbit (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) (n : ℕ) :
    Real.log (ratio m (orbit m r n)) =
      Real.log (ratio m r)-2*(n : ℝ)*Real.log (upperRoot m) := by
  have hl := lowerRoot_positive hm
  have hu := upperRoot_positive hm
  have hz := positive hr
  rw [KroneckerRootCrossRatioOrbit.formula hm hr n,
    Real.log_mul (pow_ne_zero n (ne_of_gt (div_pos hl hu))) (ne_of_gt hz),
    Real.log_pow, Real.log_div (ne_of_gt hl) (ne_of_gt hu), log_lower m hm]
  ring

def threshold (m r : ℝ) : ℝ :=
  Real.log (ratio m r / upperRoot m) / (2*Real.log (upperRoot m))

theorem orbit_hit_iff (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) (n : ℕ) :
    orbit m r n ≤ m-1 ↔ threshold m r ≤ (n : ℝ) := by
  have hi := KroneckerRealReflectionIterates.interior hm hr n
  have hb := upperRoot_positive hm
  have hz := positive hr
  have hl : 0 < Real.log (upperRoot m) := Real.log_pos (one_lt_upperRoot hm)
  rw [← ratio_le_threshold m (orbit m r n) hm hi]
  rw [← Real.log_le_log_iff (positive hi) hb, log_ratio_orbit m r hm hr n]
  unfold threshold
  rw [Real.log_div (ne_of_gt hz) (ne_of_gt hb), div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

def stoppingIndex (m r : ℝ) : ℕ := (⌈threshold m r⌉ : ℤ).toNat

theorem ceiling_toNat_le (A : ℝ) (n : ℕ) :
    (⌈A⌉ : ℤ).toNat ≤ n ↔ A ≤ (n : ℝ) := by
  rw [Int.toNat_le, Int.ceil_le]
  rfl

theorem stopping_le_iff (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) (n : ℕ) :
    stoppingIndex m r ≤ n ↔ orbit m r n ≤ m-1 := by
  rw [stoppingIndex, ceiling_toNat_le, orbit_hit_iff m r hm hr n]

theorem stopping_eq_firstHit (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    stoppingIndex m r = firstHit hm hr := by
  apply Nat.le_antisymm
  · exact (stopping_le_iff m r hm hr _).mpr (at_first hm hr)
  · by_contra h
    have hb := before_first hm hr (stoppingIndex m r) (by omega)
    have ha := (stopping_le_iff m r hm hr (stoppingIndex m r)).mp le_rfl
    linarith

theorem stopping_strip (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) (h1 : 1 ≤ r) :
    orbit m r (stoppingIndex m r) ∈ Set.Icc 1 (m-1) := by
  rw [stopping_eq_firstHit m r hm hr]
  exact KroneckerRealReflectionEntryStrip.strip hm hr h1

theorem stopping_zero (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) (h : r ≤ m-1) :
    stoppingIndex m r = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (stopping_le_iff m r hm hr 0).mpr h

end KroneckerReductionIndexHelpers
