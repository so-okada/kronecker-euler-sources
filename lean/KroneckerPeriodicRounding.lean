import KroneckerRoundedScaling

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPeriodicRounding

noncomputable def lowerPeriods (q : ℕ) (c : ℝ) (n : ℕ) : ℕ := ⌊(c/(q : ℝ))*(n : ℝ)⌋₊
noncomputable def upperPeriods (q : ℕ) (c : ℝ) (n : ℕ) : ℕ := ⌈(c/(q : ℝ))*(n : ℝ)⌉₊

theorem lower_period_length_density (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (q : ℕ) (hq : 0 < q) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n => ((lowerPeriods q c (a n)*q : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 c) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have h := (KroneckerRoundedScaling.floor_scaling a ha (c/(q : ℝ)) (by positivity)).mul_const (q : ℝ)
  simpa only [lowerPeriods,Nat.cast_mul,div_mul_cancel₀ _ hqR,mul_div_right_comm] using h

theorem upper_period_length_density (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (q : ℕ) (hq : 0 < q) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n => ((upperPeriods q c (a n)*q : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 c) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have h := (KroneckerRoundedScaling.ceil_scaling a ha (c/(q : ℝ)) (by positivity)).mul_const (q : ℝ)
  simpa only [upperPeriods,Nat.cast_mul,div_mul_cancel₀ _ hqR,mul_div_right_comm] using h

end KroneckerPeriodicRounding
