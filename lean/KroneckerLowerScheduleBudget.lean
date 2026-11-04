import KroneckerComparisonSchedules
import KroneckerAsymptoticCollarBudget

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerLowerScheduleBudget
open KroneckerComparisonSchedules KroneckerComparisonScales KroneckerPeriodicRounding

theorem lower_schedule_budget (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (m q N : ℕ) (hq : 0 < q) (η : ℝ) (hη : 0 < η) (hsmall : inflationScale m*η < 1) :
    ∀ᶠ n in atTop, N ≤ lowerLength m q η (a n) ∧
      (1+η)*(lowerLength m q η (a n) : ℝ) ≤ lowerMiddle m η (a n) ∧
      ((lowerMiddle m η (a n)-lowerLength m q η (a n) : ℕ) : ℝ)+
        (m+1 : ℕ)*η*(lowerLength m q η (a n) : ℝ) ≤ collar m η (a n) ∧
      collar m η (a n)+1+lowerMiddle m η (a n)+1+collar m η (a n)=a n := by
  have hs := lower_scale_slack m η hη hsmall
  have hl := lower_period_length_density a ha q hq (1-inflationScale m*η) hs.1.le
  have htop := KroneckerPositiveDensity.positive_density_atTop a
    (fun n => lowerLength m q η (a n)) ha _ hs.1 hl
  have hb := KroneckerAsymptoticCollarBudget.eventual_collar_budget a
    (fun n => lowerLength m q η (a n)) (fun n => lowerMiddle m η (a n))
    (fun n => collar m η (a n)) ha m η _ _ _ hη.le hl
    (lower_middle_density a ha m η hη hsmall) (collar_density a ha m η hη) hs.2.2.1 hs.2.2.2
  filter_upwards [htop.eventually (eventually_ge_atTop (max N 1)),hb] with n hn hb
  have hpos : (0 : ℝ) < lowerLength m q η (a n) := by exact_mod_cast (show 0 < lowerLength m q η (a n) by omega)
  have htpos : 0 < lowerMiddle m η (a n) := by
    have : (0 : ℝ) < lowerMiddle m η (a n) := lt_of_lt_of_le (by positivity) hb.1
    exact_mod_cast this
  refine ⟨by omega,hb.1,hb.2,?_⟩
  dsimp [lowerMiddle] at *
  omega

end KroneckerLowerScheduleBudget
