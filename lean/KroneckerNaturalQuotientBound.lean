import KroneckerRoundedBlockLength

set_option autoImplicit false
namespace KroneckerNaturalQuotientBound

theorem natural_quotient_bound (n L : ℕ) (hL : 0 < L) :
    ((n/L : ℕ) : ℝ) ≤ (n : ℝ)/(L : ℝ) := by
  apply (le_div_iff₀ (show (0 : ℝ) < L by exact_mod_cast hL)).mpr
  exact_mod_cast Nat.div_mul_le_self n L

end KroneckerNaturalQuotientBound
