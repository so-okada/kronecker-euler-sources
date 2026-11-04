import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import KroneckerLogFactorialRemainder

/- Original module: KroneckerLogBinomialFactorials -/
section
/-! The exact logarithm of a positive binomial coefficient. -/
set_option autoImplicit false
namespace KroneckerLogBinomialFactorials

theorem log_choose_factorials (N K : ℕ) (hK : K ≤ N) :
    Real.log (N.choose K : ℝ)=Real.log (N.factorial : ℝ)-
      Real.log (K.factorial : ℝ)-Real.log ((N-K).factorial : ℝ) := by
  have hc : 0 < (N.choose K : ℝ) := by exact_mod_cast Nat.choose_pos hK
  have hp : (N.choose K : ℝ)*(K.factorial : ℝ)*((N-K).factorial : ℝ)=(N.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hK
  have h := congrArg Real.log hp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at h
  linarith

end KroneckerLogBinomialFactorials
end

/- Original module: KroneckerNormalizedBinomialIdentity -/
section
/-! Cancel all n log n and linear terms in the normalized binomial logarithm. -/
set_option autoImplicit false
namespace KroneckerNormalizedBinomialIdentity
open KroneckerLogBinomialFactorials KroneckerLogFactorialRemainder

theorem normalized_binomial_identity (N n : ℕ) (hn : 0 < n) (hN : n < N) :
    Real.log (N.choose n : ℝ)/(n : ℝ)=
      ((N : ℝ)/n)*Real.log ((N : ℝ)/n)-
        (((N-n : ℕ) : ℝ)/n)*Real.log (((N-n : ℕ) : ℝ)/n)+
        (remainder N-remainder n-remainder (N-n))/(n : ℝ) := by
  have hnR : (n : ℝ)≠0 := by positivity
  have hNR : (N : ℝ)≠0 := by have := lt_trans hn hN; positivity
  have hMR : ((N-n : ℕ) : ℝ)≠0 := by have : 0 < N-n := Nat.sub_pos_of_lt hN; positivity
  have hsum : (N : ℝ)=(n : ℝ)+((N-n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hN.le]
    ring
  rw [log_choose_factorials N n hN.le,Real.log_div hNR hnR,Real.log_div hMR hnR]
  unfold remainder
  rw [hsum]
  field_simp
  ring

end KroneckerNormalizedBinomialIdentity
end
