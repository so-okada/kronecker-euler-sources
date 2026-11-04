import KroneckerScaffoldCounts
import KroneckerSelectedProducts
import KroneckerRotatedCounts
import KroneckerPeriodicLimit

/- Original module: KroneckerScaffoldSelection -/
section
/-! A finite scaffold lower bound allowing a specified budget of bad holes. -/
set_option autoImplicit false
namespace KroneckerScaffoldSelection
open KroneckerWordCounts KroneckerWordBounds KroneckerHoleGrammar KroneckerHoleChains
open KroneckerScaffoldCounts KroneckerSelectedProducts


end KroneckerScaffoldSelection
end

/- Original module: KroneckerPeriodicScaffold -/
section
/-! Finite rational lower bound from periodic holes and a bounded number of
exceptional holes; extraction of such holes from a frame is a later step. -/
set_option autoImplicit false
namespace KroneckerPeriodicScaffold
open KroneckerWordCounts KroneckerHoleGrammar KroneckerHoleChains
open KroneckerScaffoldSelection KroneckerPeriodicWords KroneckerPeriodicBounds KroneckerRotatedCounts


end KroneckerPeriodicScaffold
end

/- Original module: KroneckerLogCountBounds -/
section
/-! Logarithmic forms of finite colored-count lower bounds. -/
set_option autoImplicit false
namespace KroneckerLogCountBounds
open KroneckerWordCounts KroneckerHoleGrammar KroneckerHoleChains
open KroneckerPeriodicWords KroneckerPeriodicScaffold KroneckerPeriodicBounds

theorem log_power_lower {A C k : ℕ} (hA : 0 < A) (hbound : A^k ≤ C) :
    (k : ℝ) * Real.log (A : ℝ) ≤ Real.log (C : ℝ) := by
  have hp : 0 < (A : ℝ)^k := pow_pos (by exact_mod_cast hA) _
  have hcast : (A : ℝ)^k ≤ (C : ℝ) := by exact_mod_cast hbound
  simpa only [Real.log_pow] using Real.log_le_log hp hcast

theorem normalized_log_power_lower {A C k : ℕ} (hA : 0 < A) (hbound : A^k ≤ C)
    (N : ℝ) (hN : 0 < N) :
    ((k : ℝ)/N) * Real.log (A : ℝ) ≤ Real.log (C : ℝ)/N := by
  have h := div_le_div_of_nonneg_right (log_power_lower hA hbound) hN.le
  simpa only [div_mul_eq_mul_div] using h


end KroneckerLogCountBounds
end
