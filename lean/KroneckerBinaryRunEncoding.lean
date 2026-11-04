import KroneckerBinarySwapRuns

/-! Exact dictionaries between binary bit words and run lists over types one and two. -/
set_option autoImplicit false
namespace KroneckerBinaryRunEncoding
open KroneckerBinarySwapRuns

def bits (rs : List ℕ) : List Bool := rs.map (fun r => decide (r=2))

theorem bitRuns_bits (rs : List ℕ) (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 2) : bitRuns (bits rs)=rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have h := hr r (by simp)
    have ht : ∀ x ∈ rs, 1 ≤ x ∧ x ≤ 2 := fun x hx => hr x (by simp [hx])
    have he : r=1 ∨ r=2 := by omega
    rcases he with rfl | rfl <;> simp [bits,bitRuns] at ih ⊢ <;> exact ih ht


theorem bits_length (rs : List ℕ) : (bits rs).length=rs.length := by simp [bits]

theorem bitRuns_sum (xs : List Bool) : (bitRuns xs).sum=xs.length+xs.count true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [bitRuns] at ih ⊢ <;> omega

end KroneckerBinaryRunEncoding
