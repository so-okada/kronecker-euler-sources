import KroneckerGeometricOperations
import KroneckerPeriodicGrowth
import KroneckerRotatedCounts
import KroneckerDeleteBinaryCount

set_option autoImplicit false

namespace KroneckerPaperPathGradings
noncomputable section
open KroneckerPaperPaths KroneckerWordCounts KroneckerPeriodicWords
open KroneckerPeriodicTail KroneckerPeriodicLog Filter
open scoped Topology

@[simp] theorem connectedCount_runPath (m : ℕ) (rs : List ℕ) (o : LatticePoint) (d : ℕ) :
    connectedCount m (runPath rs o) d = runCount m rs d := by
  rw [connectedCount_eq_pathCount]
  rfl

@[simp] theorem connectedCount_power_runPath (m : ℕ) (rs : List ℕ)
    (o : LatticePoint) (n : ℕ) :
    connectedCount m (power (runPath rs o) n) 0 = periodicCount m rs n := by
  rw [runPath_power, connectedCount_runPath]
  rfl

theorem geometric_word_bounds (m L : ℕ) (hm : 3 ≤ m) (hL : L ≤ m - 1)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ L) :
    m ^ ((rs.length + 1) / 2) ≤ connectedCount m (runPath rs o) 0 ∧
      connectedCount m (runPath rs o) 0 ≤ 2 ^ (m * (L + 1) * rs.length) := by
  simpa only [connectedCount_runPath] using
    KroneckerWordBounds.runCount_bounds m L hm hL rs hne hr

theorem geometric_periodic_positive (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m - 1) (n : ℕ) (hn : 1 ≤ n) :
    0 < connectedCount m (power (runPath rs o) n) 0 := by
  rw [connectedCount_power_runPath]
  exact KroneckerPeriodicBounds.periodicCount_pos m hm rs hne hr n hn

theorem geometric_periodic_sup (m : ℕ) (rs : List ℕ) (o : LatticePoint) :
    periodicGrowth m rs =
      sSup ((fun n : ℕ => Real.log (connectedCount m (power (runPath rs o) n) 0 : ℝ) /
        ((n : ℝ) + 2)) '' Set.Ici 1) := by
  simpa only [connectedCount_power_runPath, periodicLog] using
    KroneckerPeriodicGrowth.periodicGrowth_sup m rs

theorem geometric_periodic_limit (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m - 1) :
    Tendsto (fun n : ℕ => Real.log (connectedCount m (power (runPath rs o) n) 0 : ℝ) /
      (n : ℝ)) atTop (𝓝 (periodicGrowth m rs)) := by
  simpa only [connectedCount_power_runPath, periodicLog] using
    KroneckerPeriodicLimit.periodicLog_limit m hm rs hne hr

theorem geometric_periodic_finite_bound (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m - 1) (n : ℕ) :
    (connectedCount m (power (runPath rs o) n) 0 : ℝ) ≤
      Real.exp (periodicGrowth m rs * ((n : ℝ) + 2)) := by
  by_cases hn : n = 0
  · simp [hn, Real.exp_nonneg]
  · have hn' : 1 ≤ n := by omega
    have hc : 0 < (periodicCount m rs n : ℝ) := by
      exact_mod_cast KroneckerPeriodicBounds.periodicCount_pos m hm rs hne hr n hn'
    have hl := KroneckerPeriodicGrowth.periodicRatio_le_growth m hm rs hne hr n hn'
    have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hb := (div_le_iff₀ hd).mp hl
    rw [connectedCount_power_runPath, ← Real.exp_log hc]
    exact Real.exp_le_exp.mpr hb

theorem geometric_rotation_count (m : ℕ) (hm : 3 ≤ m)
    (rs : List ℕ) (o : LatticePoint) (j J : ℕ) (hj : j ≤ rs.length) (hJ : 3 ≤ J)
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m - 1) :
    connectedCount m (power (runPath rs o) (J - 3)) 0 ≤
      connectedCount m (power (rotateRuns (runPath rs o) j) J) 0 := by
  rw [rotateRuns_runPath, connectedCount_power_runPath, connectedCount_power_runPath]
  exact KroneckerRotatedCounts.periodic_hole_bound m hm rs j J hj hJ hr

theorem repeatRuns_singleton (r n : ℕ) : repeatRuns [r] n = List.replicate n r := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatRuns, ih, List.replicate_succ']

theorem geometric_binary_deletion (rs : List ℕ) (o : LatticePoint)
    (hr : ∀ r ∈ rs, r = 1 ∨ r = 2) :
    connectedCount 3 (runPath rs o) 0 ≤
      (rs.length + rs.count 2).choose (rs.count 2) * 64 ^ (rs.count 2) *
        connectedCount 3 (power (simpleRun 1 (by decide))
          (rs.length + 2 + 8 * rs.count 2)) 0 := by
  rw [← runPath_singleton 1 (by decide), runPath_power, repeatRuns_singleton]
  simpa only [connectedCount_runPath] using KroneckerDeleteBinaryCount.binary_count rs hr

end
end KroneckerPaperPathGradings
