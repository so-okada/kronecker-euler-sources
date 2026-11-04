import KroneckerIntegerEditDensity
import KroneckerScaffoldDensity

/-! The prescribed integer-comparison padding has zero density when the edit cost does. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerSurgeryPadding
open KroneckerScaffoldDensity KroneckerIntegerEditDensity KroneckerFrameBadDensity KroneckerWordEditCost

def surgeryPadding (m D : ℕ) : ℕ := (m+2)*D+1

theorem surgery_padding_density (m : ℕ) (a D : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hD : Tendsto (fun n => (D n : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => (surgeryPadding m (D n) : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hm := hD.const_mul ((m+2 : ℕ) : ℝ)
  simp only [mul_zero] at hm
  have hmul : Tendsto (fun n => (((m+2)*D n : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_mul, mul_div_assoc] using hm
  exact bad_budget_with_constant a (fun n => (m+2)*D n) ha hmul 1


end KroneckerSurgeryPadding
