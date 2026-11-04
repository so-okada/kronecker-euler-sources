import KroneckerBinomialBudgetBound

/-! Definition 4.9: Fib_m(ν,D) = choose(ν+D,D) * 2^(2*m*D).
The Lean parameter n denotes ν. B_m(r,η) denotes a different constant. -/
set_option autoImplicit false
namespace KroneckerFiberBudget
open KroneckerBinomialBudgetBound

def fiberBudget (m n D : ℕ) : ℕ := (n+D).choose D*2^(2*m*D)

theorem fiberBudget_positive (m n D : ℕ) : 0 < fiberBudget m n D := by
  unfold fiberBudget
  exact Nat.mul_pos (additive_choose_positive n D) (by positivity)

theorem one_le_fiberBudget (m n D : ℕ) : 1 ≤ fiberBudget m n D :=
  fiberBudget_positive m n D

theorem fiberBudget_zero (m n : ℕ) : fiberBudget m n 0=1 := by
  simp [fiberBudget]

end KroneckerFiberBudget
