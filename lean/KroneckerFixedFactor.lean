import KroneckerPeriodicLimit

/-! Multiplication by a fixed positive integer changes normalized logarithms
by a term tending to zero. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFixedFactor

theorem scaled_log_difference (a E : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (m : ℕ) (hm : 0 < m) (hE : ∀ᶠ n in atTop, 0 < E n) :
    Tendsto (fun n => (Real.log ((m*E n : ℕ) : ℝ)-Real.log (E n : ℝ))/(a n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hconst : Tendsto (fun n => Real.log (m : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  apply hconst.congr'
  filter_upwards [hE] with n hn
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hE0 : (E n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [Nat.cast_mul, Real.log_mul hm0 hE0]

theorem normalized_scaled_log_difference (a E : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (m : ℕ) (hm : 0 < m) (hE : ∀ᶠ n in atTop, 0 < E n) :
    Tendsto (fun n => Real.log ((m*E n : ℕ) : ℝ)/(a n : ℝ)-Real.log (E n : ℝ)/(a n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  simpa only [sub_div] using scaled_log_difference a E ha m hm hE

end KroneckerFixedFactor
