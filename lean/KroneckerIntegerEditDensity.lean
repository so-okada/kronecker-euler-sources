import KroneckerWordEditCost
import KroneckerFrameWord

/- Original module: KroneckerFrameEditCost -/
section
/-! Exact manuscript integer-run edit distance, including the exceptional appended run. -/
set_option autoImplicit false
namespace KroneckerFrameEditCost
open KroneckerFrameSlope KroneckerFrameBadDensity KroneckerFramePrefix
open KroneckerWordEditCost KroneckerMechanicalEditCost

theorem frame_edit_cost (a b d k : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hk : 1 ≤ k) :
    (wordEditCost (frameWord a b d) k : ℤ) = |(b : ℤ)-1-(a : ℤ)*(k : ℤ)|+(k : ℤ)-1 := by
  rw [frameWord, wordEditCost_append, Nat.cast_add,
    wordEditCost_mechanical _ _ _ _ _ (frameSlope_nonnegative a b d ha hb hd),
    mechanical_edit_cost_prefix, frame_prefix_floor a b d ha hd,
    Int.floor_zero, sub_zero, wordEditCost_singleton, Int.natCast_natAbs]
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  simp only [Nat.cast_one]
  rw [abs_of_nonpos (by omega : (1 : ℤ)-(k : ℤ) ≤ 0)]
  ring

theorem frame_edit_cost_real (a b d k : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hk : 1 ≤ k) :
    (wordEditCost (frameWord a b d) k : ℝ) = |(b : ℝ)-1-(a : ℝ)*(k : ℝ)|+(k : ℝ)-1 := by
  exact_mod_cast frame_edit_cost a b d k ha hb hd hk

end KroneckerFrameEditCost
end

/- Original module: KroneckerIntegerDeviation -/
section
/-! Dimension convergence to an integer makes the normalized total discrepancy vanish. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIntegerDeviation

theorem integer_dimension_deviation (a b : ℕ → ℕ) (k : ℝ)
    (ha : Tendsto a atTop atTop)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 k)) :
    Tendsto (fun n => |(b n : ℝ)-1-(a n : ℝ)*k|/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hone : Tendsto (fun n => (1 : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  have h := ((hr.sub hone).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => k) atTop (𝓝 k))).abs
  simp only [sub_zero, sub_self, abs_zero] at h
  apply h.congr'
  filter_upwards [ha.eventually (eventually_ge_atTop 1)] with n hn
  have ha' : (0 : ℝ) < a n := by exact_mod_cast hn
  have ha0 : (a n : ℝ) ≠ 0 := ne_of_gt ha'
  change |(b n : ℝ)/(a n : ℝ)-1/(a n : ℝ)-k| = |(b n : ℝ)-1-(a n : ℝ)*k|/(a n : ℝ)
  have heq : (b n : ℝ)/(a n : ℝ)-1/(a n : ℝ)-k = ((b n : ℝ)-1-(a n : ℝ)*k)/(a n : ℝ) := by
    field_simp
  rw [heq, abs_div, abs_of_pos ha']

end KroneckerIntegerDeviation
end

/- Original module: KroneckerIntegerEditDensity -/
section
/-! The exact integer-run edit cost is sublinear along dimension ratios tending to k. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIntegerEditDensity
open KroneckerFrameBadDensity KroneckerWordEditCost KroneckerFrameEditCost KroneckerIntegerDeviation


end KroneckerIntegerEditDensity
end
