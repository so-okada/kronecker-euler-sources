import KroneckerGeometricCounts
import Mathlib.Data.Nat.Periodic

set_option autoImplicit false

namespace KroneckerPeriodicWords

theorem rotate_repeatRuns_period (W : List ℕ) (n : ℕ) :
    (repeatRuns W n).rotate W.length = repeatRuns W n := by
  cases n with
  | zero => simp [repeatRuns]
  | succ n =>
    rw [repeatRuns_succ_left, List.rotate_append_length_eq]
    exact repeatRuns_succ_left W n

theorem rotate_repeatRuns_short (W : List ℕ) (n j : ℕ) (hj : j ≤ W.length) :
    (repeatRuns W n).rotate j = repeatRuns (W.rotate j) n := by
  cases n with
  | zero => simp [repeatRuns]
  | succ n =>
    have hlen : j ≤ (repeatRuns W (n + 1)).length := by
      rw [repeatRuns_length]
      nlinarith
    rw [List.rotate_eq_drop_append_take hlen, repeatRuns_succ_left,
      List.drop_append_of_le_length hj, List.take_append_of_le_length hj,
      List.rotate_eq_drop_append_take hj, KroneckerRotatedWords.repeat_conjugate]
    rw [List.take_append_drop]

theorem rotate_repeatRuns (W : List ℕ) (n j : ℕ) (hne : W ≠ []) :
    (repeatRuns W n).rotate j = repeatRuns (W.rotate (j % W.length)) n := by
  have hp : Function.Periodic (fun j => (repeatRuns W n).rotate j) W.length := by
    intro j
    change (repeatRuns W n).rotate (j + W.length) = (repeatRuns W n).rotate j
    rw [Nat.add_comm, ← List.rotate_rotate, rotate_repeatRuns_period]
  rw [← hp.map_mod_nat j]
  exact rotate_repeatRuns_short W n _ (Nat.mod_lt _ (List.length_pos_iff.mpr hne)).le

end KroneckerPeriodicWords

namespace KroneckerPaperPaths
open KroneckerPeriodicWords

theorem rotateRuns_power (W : List ℕ) (o : LatticePoint) (n j : ℕ) (hne : W ≠ []) :
    rotateRuns (power (runPath W o) n) j =
      power (rotateRuns (runPath W o) (j % W.length)) n := by
  rw [runPath_power, rotateRuns_runPath, rotateRuns_runPath, runPath_power,
    rotate_repeatRuns W n j hne]

end KroneckerPaperPaths

namespace KroneckerPaperPathGradings
noncomputable section
open KroneckerPaperPaths

theorem geometric_power_rotation_count (m : ℕ) (hm : 3 ≤ m)
    (W : List ℕ) (o : LatticePoint) (J j : ℕ) (hJ : 3 ≤ J) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m - 1) :
    connectedCount m (power (runPath W o) (J - 3)) 0 ≤
      connectedCount m (rotateRuns (power (runPath W o) J) j) 0 := by
  rw [rotateRuns_power W o J j hne]
  exact geometric_rotation_count m hm W o _ J
    (Nat.mod_lt _ (List.length_pos_iff.mpr hne)).le hJ hr

end
end KroneckerPaperPathGradings
