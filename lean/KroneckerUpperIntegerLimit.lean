import KroneckerParameterDimensionBounds
import KroneckerEventualFrameAlphabet

/- Original module: KroneckerLiteratureIntegerLimit -/
section
/-! The manuscript integer-slope limit for alphabet-admissible frames, relative only to Literature. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerLiteratureIntegerLimit
open KroneckerPeriodicTail KroneckerFrameBadDensity KroneckerFrameIdentity
open KroneckerActualIntegerLimit KroneckerLiteratureCountNatural KroneckerParameterDimensionBounds


end KroneckerLiteratureIntegerLimit
end

/- Original module: KroneckerInteriorIntegerLimit -/
section
/-! Strictly interior integer slopes need no separate alphabet premise. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerInteriorIntegerLimit
open KroneckerPeriodicTail KroneckerFrameIdentity KroneckerParameterDimensionBounds
open KroneckerLiteratureIntegerLimit KroneckerEventualFrameAlphabet


end KroneckerInteriorIntegerLimit
end

/- Original module: KroneckerFrameLowerBoundary -/
section
/-! The primitive-frame dimension inequality supplies the lower alphabet bound at slope one. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFrameLowerBoundary
open KroneckerFrameSlope KroneckerFrameSlopeLimit KroneckerFrameBadDensity KroneckerFrameWord

theorem frameSlope_ge_one (a b d : ℕ) (ha : 0 < a) (hab : a < b) (hd : 0 < d) :
    1 ≤ frameSlope a b d := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hab' : (a : ℝ)+1 ≤ b := by exact_mod_cast (show a+1 ≤ b by omega)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hi : 1/(d : ℝ) ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd'
  have he := frameSlope_mul a b d ha hd
  nlinarith


end KroneckerFrameLowerBoundary
end

/- Original module: KroneckerLowerIntegerLimit -/
section
/-! The integer limit at one holds for every primitive frame sequence approaching from above. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerLowerIntegerLimit
open KroneckerPeriodicTail KroneckerFrameIdentity KroneckerParameterDimensionBounds
open KroneckerLiteratureIntegerLimit KroneckerFrameLowerBoundary


end KroneckerLowerIntegerLimit
end

/- Original module: KroneckerUpperIntegerLimit -/
section
/-! The upper alphabet endpoint is admissible along approaches from below. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerUpperIntegerLimit
open KroneckerPeriodicTail KroneckerFrameIdentity KroneckerParameterDimensionBounds
open KroneckerFrameSlope KroneckerFrameBadDensity KroneckerFrameWord
open KroneckerLiteratureIntegerLimit KroneckerFrameLowerBoundary

theorem parameter_below_alphabet (p : Parameters) (M : ℕ)
    (h : (p.b : ℝ)/(p.a : ℝ) ≤ M) :
    ∀ r ∈ frameWord p.a p.b p.d₁,1 ≤ r ∧ r ≤ M := by
  have hp := parameter_dimensions_positive p
  exact frameWord_legal _ _ _ M (frameSlope_ge_one _ _ _ hp.1 p.hab hp.2.2)
    ((frameSlope_le_ratio _ _ _).trans h)


end KroneckerUpperIntegerLimit
end
