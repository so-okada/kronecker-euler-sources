import Mathlib.Tactic

set_option autoImplicit false
namespace KroneckerComparisonIntervalWidth

theorem comparison_interval_width (F B E h ε : ℝ) (hFB : F ≤ B)
    (hE : 0 ≤ E) (hh : 0 ≤ h) :
    ((1+h)*F+E+ε)-((1-h)*(F-E)-ε) ≤ 2*h*B+2*E+2*ε := by
  have hmul := mul_le_mul_of_nonneg_left hFB (show 0 ≤ 2*h by positivity)
  have hprod := mul_nonneg hh hE
  nlinarith

end KroneckerComparisonIntervalWidth
