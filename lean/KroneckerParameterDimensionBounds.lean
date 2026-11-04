import KroneckerFrameIntegerLower
import KroneckerConditionalIntegerEulerLimit
import KroneckerConditionalEulerLower

/- Original module: KroneckerFrameEulerIntegerComparisons -/
section
/-! Both actual finite comparisons transfer through the exact frame/Euler dictionary. -/
set_option autoImplicit false
namespace KroneckerFrameEulerIntegerComparisons
open KroneckerWordCounts KroneckerPeriodicWords KroneckerFiberBudget KroneckerWordEditCost
open KroneckerFrameBadDensity KroneckerSurgeryPadding KroneckerIntegerComparisonLengths
open KroneckerFrameIntegerUpper KroneckerFrameIntegerLower


end KroneckerFrameEulerIntegerComparisons
end

/- Original module: KroneckerEventualIntegerComparisons -/
section
/-! Actual comparisons hold eventually as soon as the literal frames are admissible. -/
set_option autoImplicit false
open Filter
namespace KroneckerEventualIntegerComparisons
open KroneckerWordCounts KroneckerPeriodicWords KroneckerFiberBudget KroneckerWordEditCost
open KroneckerFrameBadDensity KroneckerSurgeryPadding KroneckerIntegerComparisonLengths
open KroneckerFrameEulerIntegerComparisons


end KroneckerEventualIntegerComparisons
end

/- Original module: KroneckerActualIntegerLimit -/
section
/-! Discharge both formerly assumed finite inequalities in the integer Euler limit. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerActualIntegerLimit
open KroneckerWordCounts KroneckerPeriodicTail KroneckerFrameBadDensity
open KroneckerEventualIntegerComparisons KroneckerConditionalIntegerEulerLimit


end KroneckerActualIntegerLimit
end

/- Original module: KroneckerLiteratureCountNatural -/
section
/-! The named literature interface gives the natural-valued frame dictionary. -/
set_option autoImplicit false
namespace KroneckerLiteratureCountNatural
open KroneckerWordCounts KroneckerFrameBadDensity KroneckerFrameIdentity KroneckerConditionalEulerLower

theorem literal_frame_identity_nat (p : Parameters) (E : ℕ) (s : Literature p (E : ℤ)) :
    runCount p.m (frameWord p.a p.b p.d₁) 0=p.m*E := by
  exact_mod_cast literal_frame_identity p (E : ℤ) s

end KroneckerLiteratureCountNatural
end

/- Original module: KroneckerParameterDimensionBounds -/
section
/-! Every primitive frame parameter package has the positive dimensions used in limits. -/
set_option autoImplicit false
namespace KroneckerParameterDimensionBounds
open KroneckerFrameIdentity

theorem parameter_dimensions_positive (p : Parameters) : 0 < p.a ∧ 0 < p.b ∧ 0 < p.d₁ := by
  have ha := p.ha
  have hb := p.hab
  have hd := p.hd₁
  omega

end KroneckerParameterDimensionBounds
end
