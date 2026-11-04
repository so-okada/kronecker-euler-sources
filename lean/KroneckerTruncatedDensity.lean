import KroneckerPeriodicLimit

/-! Normalized natural subtraction is positive-part subtraction; this keeps
truncation exact when a bad-hole budget exceeds the number of holes. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerTruncatedDensity

theorem cast_sub_eq_max (a b : ℕ) : ((a-b : ℕ) : ℝ) = max ((a : ℝ)-(b : ℝ)) 0 := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_left]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have h' : a ≤ b := by omega
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero, max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast h')

theorem normalized_sub_eq_max (a b d : ℕ) :
    ((a-b : ℕ) : ℝ)/(d : ℝ) = max ((a : ℝ)/(d : ℝ)-(b : ℝ)/(d : ℝ)) 0 := by
  rw [cast_sub_eq_max, ← max_div_div_right (Nat.cast_nonneg d)]
  simp [sub_div]

theorem truncated_difference_density (a h b : ℕ → ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hh : Tendsto (fun n => (h n : ℝ)/(a n : ℝ)) atTop (𝓝 L))
    (hb : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ((h n-b n : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 L) := by
  have hmax := (hh.sub hb).max
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  simpa only [sub_zero, max_eq_left hL, ← normalized_sub_eq_max] using hmax

end KroneckerTruncatedDensity
