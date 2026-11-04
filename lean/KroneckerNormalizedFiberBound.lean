import KroneckerFiberBudget

/- Original module: KroneckerLogBinomialBound -/
section
/-! Logarithmic binomial bounds with a freely chosen positive generating parameter. -/
set_option autoImplicit false
namespace KroneckerLogBinomialBound
open KroneckerBinomialBudgetBound

theorem log_additive_choose_bound (n D : ℕ) (t : ℝ) (ht : 0 < t) :
    Real.log ((n+D).choose D : ℝ) ≤
      ((n : ℝ)+(D : ℝ))*Real.log (1+t)-(D : ℝ)*Real.log t := by
  have hc : (0 : ℝ) < (n+D).choose D := by exact_mod_cast additive_choose_positive n D
  have hp : 0 < t^D := pow_pos ht D
  have h := Real.log_le_log (mul_pos hc hp) (additive_choose_weighted n D t ht.le)
  rw [Real.log_mul hc.ne' hp.ne',Real.log_pow,Real.log_pow,Nat.cast_add] at h
  linarith

end KroneckerLogBinomialBound
end

/- Original module: KroneckerLogFiberBudget -/
section
/-! Separate the composition and color terms in the exact logarithmic fiber budget. -/
set_option autoImplicit false
namespace KroneckerLogFiberBudget
open KroneckerFiberBudget KroneckerBinomialBudgetBound KroneckerLogBinomialBound

theorem log_fiberBudget (m n D : ℕ) :
    Real.log (fiberBudget m n D : ℝ) = Real.log ((n+D).choose D : ℝ)+
      (2*(m : ℝ)*(D : ℝ))*Real.log 2 := by
  have hc : (0 : ℝ) < (n+D).choose D := by exact_mod_cast additive_choose_positive n D
  have hp : (0 : ℝ) < 2^(2*m*D) := by positivity
  rw [fiberBudget,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Real.log_mul hc.ne' hp.ne',Real.log_pow]
  push_cast
  rfl

theorem log_fiberBudget_bound (m n D : ℕ) (t : ℝ) (ht : 0 < t) :
    Real.log (fiberBudget m n D : ℝ) ≤
      ((n : ℝ)+(D : ℝ))*Real.log (1+t)+
        (D : ℝ)*(2*(m : ℝ)*Real.log 2-Real.log t) := by
  rw [log_fiberBudget]
  have h := log_additive_choose_bound n D t ht
  nlinarith

end KroneckerLogFiberBudget
end

/- Original module: KroneckerNormalizedFiberBound -/
section
/-! A normalized, nonnegative logarithmic fiber cost and its elementary envelope. -/
set_option autoImplicit false
namespace KroneckerNormalizedFiberBound
open KroneckerFiberBudget KroneckerLogFiberBudget

noncomputable def normalizedFiberLog (m n D : ℕ) : ℝ :=
  Real.log (fiberBudget m n D : ℝ)/(n : ℝ)

theorem normalizedFiberLog_nonneg (m n D : ℕ) : 0 ≤ normalizedFiberLog m n D := by
  apply div_nonneg
  · apply Real.log_nonneg
    exact_mod_cast one_le_fiberBudget m n D
  · positivity

theorem normalizedFiberLog_bound (m n D : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    normalizedFiberLog m n D ≤
      (1+(D : ℝ)/(n : ℝ))*Real.log (1+t)+
        ((D : ℝ)/(n : ℝ))*(2*(m : ℝ)*Real.log 2-Real.log t) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := div_le_div_of_nonneg_right (log_fiberBudget_bound m n D t ht) hn'.le
  unfold normalizedFiberLog
  calc
    _ ≤ (((n : ℝ)+(D : ℝ))*Real.log (1+t)+
      (D : ℝ)*(2*(m : ℝ)*Real.log 2-Real.log t))/(n : ℝ) := h
    _ = _ := by field_simp

end KroneckerNormalizedFiberBound
end
