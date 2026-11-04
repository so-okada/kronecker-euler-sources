import KroneckerPeriodicWords
import Mathlib.Algebra.Order.Floor.Ring

section

/-! Integer mechanical run lengths, with exact finite mechanicalPrefix and block sums. -/
set_option autoImplicit false
namespace KroneckerMechanicalRuns

noncomputable def mechanicalPrefix (s u : ℝ) (i : ℕ) : ℤ := ⌊u+(i : ℝ)*s⌋

noncomputable def mechanicalRun (s u : ℝ) (i : ℕ) : ℤ := mechanicalPrefix s u (i+1)-mechanicalPrefix s u i

theorem mechanical_block_sum (s u : ℝ) (start n : ℕ) :
    (∑ i ∈ Finset.range n, mechanicalRun s u (start+i)) = mechanicalPrefix s u (start+n)-mechanicalPrefix s u start := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [mechanicalRun, Nat.add_assoc]
    ring

theorem mechanical_prefix_sum (s u : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, mechanicalRun s u i) = mechanicalPrefix s u n-⌊u⌋ := by
  simpa [mechanicalPrefix] using mechanical_block_sum s u 0 n

theorem mechanical_shift (s u : ℝ) (start i : ℕ) :
    mechanicalRun s u (start+i) = mechanicalRun s (u+(start : ℝ)*s) i := by
  unfold mechanicalRun mechanicalPrefix
  have h1 : u+((start+i+1 : ℕ) : ℝ)*s = (u+(start : ℝ)*s)+((i+1 : ℕ) : ℝ)*s := by
    push_cast
    ring
  have h0 : u+((start+i : ℕ) : ℝ)*s = (u+(start : ℝ)*s)+(i : ℝ)*s := by
    push_cast
    ring
  rw [h1, h0]

end KroneckerMechanicalRuns
end

section

/-! Rational mechanical increments are periodic, and every complete period
has the prescribed total vertical length, for every intercept. -/
set_option autoImplicit false
namespace KroneckerMechanicalPeriodicity
open KroneckerMechanicalRuns

theorem prefix_period_shift (s u : ℝ) (p : ℤ) (q i : ℕ) (hp : (q : ℝ)*s = (p : ℝ)) :
    mechanicalPrefix s u (i+q) = mechanicalPrefix s u i+p := by
  unfold mechanicalPrefix
  rw [Nat.cast_add, add_mul, hp, ← add_assoc, Int.floor_add_intCast]

theorem mechanical_period (s u : ℝ) (p : ℤ) (q i : ℕ) (hp : (q : ℝ)*s = (p : ℝ)) :
    mechanicalRun s u (i+q) = mechanicalRun s u i := by
  unfold mechanicalRun
  rw [show i+q+1 = (i+1)+q by omega, prefix_period_shift s u p q (i+1) hp,
    prefix_period_shift s u p q i hp]
  ring

theorem rational_mechanical_period (p : ℤ) (q : ℕ) (hq : 0 < q) (u : ℝ) :
    Function.Periodic (mechanicalRun ((p : ℝ)/(q : ℝ)) u) q := by
  intro i
  apply mechanical_period ((p : ℝ)/(q : ℝ)) u p q i
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp


end KroneckerMechanicalPeriodicity
end

