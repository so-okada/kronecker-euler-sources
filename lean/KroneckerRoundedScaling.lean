import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerRoundedScaling

theorem floor_scaling (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n => (⌊c*(a n : ℝ)⌋₊ : ℝ)/(a n : ℝ)) atTop (𝓝 c) :=
  (tendsto_nat_floor_mul_div_atTop hc).comp (tendsto_natCast_atTop_atTop.comp ha)

theorem ceil_scaling (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n => (⌈c*(a n : ℝ)⌉₊ : ℝ)/(a n : ℝ)) atTop (𝓝 c) :=
  (tendsto_nat_ceil_mul_div_atTop hc).comp (tendsto_natCast_atTop_atTop.comp ha)

end KroneckerRoundedScaling
