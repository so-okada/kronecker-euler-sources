import KroneckerMechanicalPeriodicity

section

/-! Mechanical increments occupy the two adjacent integer grades and obey
the prescribed alphabet bounds independently of the intercept. -/
set_option autoImplicit false
namespace KroneckerMechanicalBounds
open KroneckerMechanicalRuns


theorem mechanical_run_increment (s u : ℝ) (i : ℕ) :
    mechanicalRun s u i = ⌊(u+(i : ℝ)*s)+s⌋-⌊u+(i : ℝ)*s⌋ := by
  unfold mechanicalRun mechanicalPrefix
  congr 2
  push_cast
  ring


theorem floor_increment_integer_bounds (x s : ℝ) (k M : ℤ) (hk : (k : ℝ) ≤ s) (hM : s ≤ (M : ℝ)) :
    k ≤ ⌊x+s⌋-⌊x⌋ ∧ ⌊x+s⌋-⌊x⌋ ≤ M := by
  have hlo := Int.floor_mono (add_le_add_left hk x)
  have hhi := Int.floor_mono (add_le_add_left hM x)
  rw [Int.floor_intCast_add] at hlo hhi
  rw [add_comm s x] at hlo hhi
  omega

theorem mechanical_run_legal (s u : ℝ) (i M : ℕ) (hs : 1 ≤ s) (hM : s ≤ (M : ℝ)) :
    (1 : ℤ) ≤ mechanicalRun s u i ∧ mechanicalRun s u i ≤ (M : ℤ) := by
  rw [mechanical_run_increment]
  exact floor_increment_integer_bounds (u+(i : ℝ)*s) s 1 M (by simpa using hs) (by simpa using hM)

end KroneckerMechanicalBounds
end

section

/-! Window sums are single floor increments at the multiplied slope. -/
set_option autoImplicit false
namespace KroneckerMechanicalWindows
open KroneckerMechanicalRuns KroneckerMechanicalBounds

noncomputable def windowSum (s u : ℝ) (q start : ℕ) : ℤ :=
  ∑ i ∈ Finset.range q, mechanicalRun s u (start+i)

theorem window_floor (s u : ℝ) (q start : ℕ) :
    windowSum s u q start = ⌊(u+(start : ℝ)*s)+(q : ℝ)*s⌋-⌊u+(start : ℝ)*s⌋ := by
  rw [windowSum, mechanical_block_sum]
  unfold mechanicalPrefix
  congr 2
  push_cast
  ring


theorem window_integer_bounds (s u : ℝ) (q start : ℕ) (k M : ℤ)
    (hk : (k : ℝ) ≤ (q : ℝ)*s) (hM : (q : ℝ)*s ≤ (M : ℝ)) :
    k ≤ windowSum s u q start ∧ windowSum s u q start ≤ M := by
  rw [window_floor]
  exact floor_increment_integer_bounds _ _ k M hk hM

end KroneckerMechanicalWindows
end

