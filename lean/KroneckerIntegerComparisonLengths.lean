import KroneckerSurgeryPadding

/-! Sublinear padding preserves the normalized inner and outer comparison
lengths; the edit cost remains sublinear relative to the retained middle. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIntegerComparisonLengths
open KroneckerShiftedBlockDensity KroneckerScaffoldDensity KroneckerTruncatedDensity

def middleLength (a P : ℕ) : ℕ := a-(2*P+1)
def paddedLength (a P : ℕ) : ℕ := a+2*P+3

theorem middleLength_eq (a P : ℕ) : middleLength a P = a+1-2*P-2 := by
  unfold middleLength
  omega

theorem middle_length_density (a P : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hP : Tendsto (fun n => (P n : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => (middleLength (a n) (P n) : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have hone : Tendsto (fun n => (a n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Nat.sub_zero] using sub_height_ratio a ha 0
  have htwo : Tendsto (fun n => ((2*P n : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_zero, mul_div_assoc] using hP.const_mul 2
  exact truncated_difference_density a a (fun n => 2*P n+1) 1 (by norm_num) hone
    (bad_budget_with_constant a (fun n => 2*P n) ha htwo 1)

theorem padded_length_density (a P : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hP : Tendsto (fun n => (P n : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => (paddedLength (a n) (P n) : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have hone : Tendsto (fun n => (a n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Nat.sub_zero] using sub_height_ratio a ha 0
  have htwo : Tendsto (fun n => ((2*P n : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_zero, mul_div_assoc] using hP.const_mul 2
  have hbudget := bad_budget_with_constant a (fun n => 2*P n) ha htwo 3
  simpa only [paddedLength, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_div, add_assoc, add_zero]
    using hone.add hbudget



end KroneckerIntegerComparisonLengths
