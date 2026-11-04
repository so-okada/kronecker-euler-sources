import KroneckerComparisonSchedules
import KroneckerAsymptoticCollarBudget

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerUpperScheduleBudget
open KroneckerComparisonSchedules KroneckerComparisonScales

theorem upper_schedule_budget (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (m q N : ℕ) (hq : 0 < q) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, N ≤ a n ∧
      (1+η)*(a n : ℝ) ≤ upperMiddle m q η (a n) ∧
      ((upperMiddle m q η (a n)-a n : ℕ) : ℝ)+(m+1 : ℕ)*η*(a n : ℝ) ≤ collar m η (a n) ∧
      collar m η (a n)+1+upperMiddle m q η (a n)+1+collar m η (a n)=upperLength m q η (a n) := by
  have hslack := upper_scale_slack m η hη
  have hb := KroneckerAsymptoticCollarBudget.eventual_collar_budget a a
    (fun n => upperMiddle m q η (a n)) (fun n => collar m η (a n)) ha m η 1 (1+2*η)
    (collarScale m*η) hη.le (self_density a ha) (upper_middle_density a ha m q hq η hη)
    (collar_density a ha m η hη) hslack.2.2.2.1 hslack.2.2.2.2
  filter_upwards [ha.eventually (eventually_ge_atTop (max N 1)),hb] with n hn hb
  have hpos : (0 : ℝ) < a n := by exact_mod_cast (show 0 < a n by omega)
  have htpos : 0 < upperMiddle m q η (a n) := by
    have : (0 : ℝ) < upperMiddle m q η (a n) := lt_of_lt_of_le (by positivity) hb.1
    exact_mod_cast this
  refine ⟨by omega,hb.1,hb.2,?_⟩
  dsimp [upperMiddle] at *
  omega

end KroneckerUpperScheduleBudget
