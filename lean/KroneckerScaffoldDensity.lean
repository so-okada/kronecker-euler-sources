import KroneckerShiftedBlockDensity
import KroneckerTruncatedDensity

/-! The exact surviving-hole exponent has the expected density after a
sublinear bad-hole budget and any fixed boundary offsets. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerScaffoldDensity
open KroneckerShiftedBlockDensity KroneckerTruncatedDensity

theorem bad_budget_with_constant (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hb : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ))) (s : ℕ) :
    Tendsto (fun n => ((b n+s : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hz : Tendsto (fun n => (s : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  simpa [Nat.cast_add, add_div] using hb.add hz

theorem surviving_hole_density (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hb : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)))
    (c s K : ℕ) (hK : 0 < K) :
    Tendsto (fun n => ((((a n-c)/K-(b n+s) : ℕ) : ℝ)/(a n : ℝ)))
      atTop (𝓝 (1/(K : ℝ))) :=
  truncated_difference_density a (fun n => (a n-c)/K) (fun n => b n+s)
    (1/(K : ℝ)) (by positivity) (shifted_block_density a ha c K hK)
    (bad_budget_with_constant a b ha hb s)

end KroneckerScaffoldDensity
