import Mathlib.Tactic

set_option autoImplicit false
namespace KroneckerRoundedBlockLength

theorem rounded_block_length (n L : ℕ) (hL : 0 < L) :
    n ≤ (n/L+1)*L ∧ (n/L+1)*L ≤ n+L := by
  have hmod := Nat.mod_lt n hL
  have hdiv := Nat.div_add_mod n L
  constructor
  · nlinarith
  · have h := Nat.div_mul_le_self n L
    nlinarith


end KroneckerRoundedBlockLength
