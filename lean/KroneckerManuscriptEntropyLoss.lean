import KroneckerNormalizedFiberBound
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Definition 4.11 and Lemma 4.12, including the value and limit at zero.
The generating-parameter estimate is specialized with its two coefficients
made nonnegative before applying the manuscript's real-valued bounds. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerManuscriptEntropyLoss
open KroneckerFiberBudget KroneckerLogFiberBudget

def psi (m : ℕ) (x : ℝ) : ℝ :=
  (1 + x) * Real.log (1 + x) - x * Real.log x + 2 * m * x * Real.log 2

@[simp] theorem psi_zero (m : ℕ) : psi m 0 = 0 := by simp [psi]

theorem psi_continuous (m : ℕ) : Continuous (psi m) := by
  unfold psi
  exact ((Real.continuous_mul_log.comp (continuous_const.add continuous_id)).sub
    Real.continuous_mul_log).add
      ((continuous_const.mul continuous_id).mul continuous_const)

theorem psi_tendsto_zero (m : ℕ) :
    Filter.Tendsto (psi m) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : ContinuousWithinAt (psi m) (Set.Ioi 0) 0 :=
    (psi_continuous m).continuousAt.continuousWithinAt
  simpa only [ContinuousWithinAt, psi_zero] using h

theorem entropy_loss (m n D : ℕ) (N x : ℝ) (hN : 0 < N) (hx : 0 ≤ x)
    (hn : (n : ℝ) ≤ N) (hD : (D : ℝ) ≤ x * N) :
    Real.log (fiberBudget m n D : ℝ) ≤ N * psi m x := by
  by_cases hz : x = 0
  · subst x
    have hle : D ≤ 0 := by exact_mod_cast (show (D : ℝ) ≤ 0 by simpa using hD)
    have hzero : D = 0 := Nat.eq_zero_of_le_zero hle
    subst D
    simp [fiberBudget]
  · have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    have hlog : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
    have hratio : 0 ≤ Real.log (1 + x) - Real.log x := by
      have := Real.log_le_log hpos (show x ≤ 1 + x by linarith)
      linarith
    have hcolor : 0 ≤ 2 * (m : ℝ) * Real.log 2 := by positivity
    have hc : 0 ≤ Real.log (1 + x) - Real.log x + 2 * m * Real.log 2 := by linarith
    have h1 := mul_le_mul_of_nonneg_right hn hlog
    have h2 := mul_le_mul_of_nonneg_right hD hc
    have h := log_fiberBudget_bound m n D x hpos
    unfold psi
    nlinarith

end KroneckerManuscriptEntropyLoss
