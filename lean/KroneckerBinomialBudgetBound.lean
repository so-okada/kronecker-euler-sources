import KroneckerAsymptotics
import Mathlib.Data.Nat.Choose.Sum

section

/-! A positive binomial summand is bounded by the full binomial expansion. -/
set_option autoImplicit false
namespace KroneckerBinomialTermBound

theorem binomial_term_bound (N D : ℕ) (hD : D ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    (N.choose D : ℝ)*t^D ≤ (1+t)^N := by
  have h := Finset.single_le_sum
    (f := fun k : ℕ => t^k*(1 : ℝ)^(N-k)*(N.choose k : ℝ))
    (fun k (_ : k ∈ Finset.range (N+1)) => by positivity)
    (Finset.mem_range.mpr (show D < N+1 by omega))
  rw [← add_pow] at h
  simpa only [one_pow,mul_one,mul_comm,add_comm] using h

end KroneckerBinomialTermBound
end

section

/-! A generating-function bound for the weak-composition counting budget. -/
set_option autoImplicit false
namespace KroneckerBinomialBudgetBound
open KroneckerBinomialTermBound

theorem additive_choose_positive (n D : ℕ) : 0 < (n+D).choose D :=
  Nat.choose_pos (by omega)

theorem additive_choose_weighted (n D : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((n+D).choose D : ℝ)*t^D ≤ (1+t)^(n+D) :=
  binomial_term_bound (n+D) D (by omega) t ht

end KroneckerBinomialBudgetBound
end

