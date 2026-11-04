import KroneckerMechanicalWords
import KroneckerPeriodicLimit

section

/-! The exact slope prescribed by the finite-frame construction. This module
does not identify the resulting word count with a moduli Euler characteristic. -/
set_option autoImplicit false
namespace KroneckerFrameSlope

noncomputable def frameSlope (a b d : ℕ) : ℝ := (b : ℝ)/(a : ℝ)-1/((a : ℝ)*(d : ℝ))

theorem frameSlope_mul (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    (a : ℝ)*frameSlope a b d = (b : ℝ)-1/(d : ℝ) := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  unfold frameSlope
  field_simp

theorem frameSlope_nonnegative (a b d : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    0 ≤ frameSlope a b d := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hinv : 1/(d : ℝ) ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num) hd'
  have hmul := frameSlope_mul a b d ha hd
  nlinarith

theorem frameSlope_le_ratio (a b d : ℕ) : frameSlope a b d ≤ (b : ℝ)/(a : ℝ) := by
  unfold frameSlope
  have h : (0 : ℝ) ≤ 1/((a : ℝ)*(d : ℝ)) := by positivity
  linarith

end KroneckerFrameSlope
end

section

/- Original module: KroneckerFrameError -/
section
/-! The ambient denominator contributes at most 1/a to the frame slope. -/
set_option autoImplicit false
namespace KroneckerFrameError
open KroneckerFrameSlope

theorem frame_slope_error (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    0 ≤ (b : ℝ)/(a : ℝ)-frameSlope a b d ∧
    (b : ℝ)/(a : ℝ)-frameSlope a b d ≤ 1/(a : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmul : (a : ℝ) ≤ (a : ℝ)*(d : ℝ) := by nlinarith
  have hupper := one_div_le_one_div_of_le ha' hmul
  unfold frameSlope
  constructor
  · have h : (0 : ℝ) ≤ 1/((a : ℝ)*(d : ℝ)) := by positivity
    linarith
  · linarith


end KroneckerFrameError
end

/- Original module: KroneckerFrameSlopeLimit -/
section
/-! The mechanical frame slope has the same limit as the dimension ratio. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFrameSlopeLimit
open KroneckerFrameSlope KroneckerFrameError

theorem frame_slope_error_limit (a b d : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hd : ∀ n, 0 < d n) :
    Tendsto (fun n => (b n : ℝ)/(a n : ℝ)-frameSlope (a n) (b n) (d n)) atTop (𝓝 (0 : ℝ)) := by
  have hone : Tendsto (fun n => (1 : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hone
  · filter_upwards [ha.eventually (eventually_ge_atTop 1)] with n hn
    exact (frame_slope_error (a n) (b n) (d n) (by omega) (hd n)).1
  · filter_upwards [ha.eventually (eventually_ge_atTop 1)] with n hn
    exact (frame_slope_error (a n) (b n) (d n) (by omega) (hd n)).2

theorem frame_slope_limit (a b d : ℕ → ℕ) (r : ℝ) (ha : Tendsto a atTop atTop)
    (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r)) :
    Tendsto (fun n => frameSlope (a n) (b n) (d n)) atTop (𝓝 r) := by
  have h := hr.sub (frame_slope_error_limit a b d ha hd)
  simpa only [sub_sub_cancel, sub_zero] using h

end KroneckerFrameSlopeLimit
end
end

