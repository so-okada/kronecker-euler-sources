import KroneckerSampledPeriodicLimit
import KroneckerFixedFactor

/- Original module: KroneckerIntegerFrameFiberCost -/
section
/-! The exact integer-frame edit allowance has vanishing logarithmic fiber cost. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIntegerFrameFiberCost
open KroneckerFrameBadDensity KroneckerWordEditCost KroneckerIntegerEditDensity
open KroneckerNormalizedFiberBound KroneckerSublinearFiberCost


end KroneckerIntegerFrameFiberCost
end

/- Original module: KroneckerLogComparison -/
section
/-! Finite comparison inequalities pass to logarithms without hiding positivity. -/
set_option autoImplicit false
namespace KroneckerLogComparison

theorem positive_of_lower_comparison (C E B : ℕ) (hC : 0 < C)
    (h : C ≤ E*B) : 0 < E := by
  by_contra hn
  have he : E = 0 := by omega
  simp only [he, zero_mul] at h
  omega

theorem log_lower_comparison (C E B : ℕ) (hC : 0 < C) (hB : 0 < B)
    (h : C ≤ E*B) :
    Real.log (C : ℝ)-Real.log (B : ℝ) ≤ Real.log (E : ℝ) := by
  have hE := positive_of_lower_comparison C E B hC h
  have hlog : Real.log (C : ℝ) ≤ Real.log ((E*B : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hC) (by exact_mod_cast h)
  have he : (E : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hE
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  rw [Nat.cast_mul, Real.log_mul he hb] at hlog
  linarith

theorem log_upper_comparison (E C B : ℕ) (hE : 0 < E) (hC : 0 < C) (hB : 0 < B)
    (h : E ≤ C*B) :
    Real.log (E : ℝ) ≤ Real.log (C : ℝ)+Real.log (B : ℝ) := by
  have hlog : Real.log (E : ℝ) ≤ Real.log ((C*B : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hE) (by exact_mod_cast h)
  have hc : (C : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hC
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  simpa only [Nat.cast_mul, Real.log_mul hc hb] using hlog

end KroneckerLogComparison
end

/- Original module: KroneckerLogSandwich -/
section
/-! Actual finite counting comparisons and negligible budgets imply a common log limit. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerLogSandwich
open KroneckerLogComparison

theorem logarithmic_sandwich (a E L U B₁ B₂ : ℕ → ℕ) (ℓ : ℝ)
    (hL : ∀ᶠ n in atTop, 0 < L n) (hU : ∀ᶠ n in atTop, 0 < U n)
    (hB₁ : ∀ᶠ n in atTop, 0 < B₁ n) (hB₂ : ∀ᶠ n in atTop, 0 < B₂ n)
    (hlower : ∀ᶠ n in atTop, L n ≤ E n*B₁ n)
    (hupper : ∀ᶠ n in atTop, E n ≤ U n*B₂ n)
    (hlimL : Tendsto (fun n => Real.log (L n : ℝ)/(a n : ℝ)) atTop (𝓝 ℓ))
    (hlimU : Tendsto (fun n => Real.log (U n : ℝ)/(a n : ℝ)) atTop (𝓝 ℓ))
    (hcost₁ : Tendsto (fun n => Real.log (B₁ n : ℝ)/(a n : ℝ)) atTop (𝓝 0))
    (hcost₂ : Tendsto (fun n => Real.log (B₂ n : ℝ)/(a n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (E n : ℝ)/(a n : ℝ)) atTop (𝓝 ℓ) := by
  have hlo := hlimL.sub hcost₁
  have hhi := hlimU.add hcost₂
  simp only [sub_zero] at hlo
  simp only [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hL,hB₁,hlower] with n hn hb hc
    simpa only [sub_div] using div_le_div_of_nonneg_right
      (log_lower_comparison (L n) (E n) (B₁ n) hn hb hc) (by positivity : (0 : ℝ) ≤ a n)
  · filter_upwards [hL,hU,hB₂,hlower,hupper] with n hn hu hb hl hc
    have he := positive_of_lower_comparison (L n) (E n) (B₁ n) hn hl
    simpa only [add_div] using div_le_div_of_nonneg_right
      (log_upper_comparison (E n) (U n) (B₂ n) he hu hb hc) (by positivity : (0 : ℝ) ≤ a n)

end KroneckerLogSandwich
end

/- Original module: KroneckerPeriodicFiberSandwich -/
section
/-! The asymptotic consequence of explicit finite periodic comparisons.
The comparison inequalities themselves are hypotheses, not constructed maps. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPeriodicFiberSandwich
open KroneckerPeriodicWords KroneckerPeriodicBounds KroneckerPeriodicTail
open KroneckerFiberBudget KroneckerLogSandwich KroneckerSampledPeriodicLimit
open KroneckerComparisonLengthDivergence

theorem periodic_fiber_sandwich (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hlegal : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (a E l u c D : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hl : Tendsto (fun n => (l n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)))
    (hu : Tendsto (fun n => (u n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)))
    (hc : Tendsto (fun n => (c n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)))
    (hD : Tendsto (fun n => (D n : ℝ)/(a n : ℝ)) atTop (𝓝 0))
    (hlower : ∀ᶠ n in atTop, periodicCount m W (l n) ≤ E n*fiberBudget m (l n) (D n))
    (hupper : ∀ᶠ n in atTop, E n ≤ periodicCount m W (u n)*fiberBudget m (c n) (D n)) :
    Tendsto (fun n => Real.log (E n : ℝ)/(a n : ℝ)) atTop (𝓝 (periodicGrowth m W)) := by
  have hlpos : ∀ᶠ n in atTop, 0 < periodicCount m W (l n) := by
    filter_upwards [(tendsto_atTop_of_ratio_one a l ha hl).eventually (eventually_ge_atTop 1)] with n hn
    exact periodicCount_pos m hm W hne hlegal (l n) hn
  have hupos : ∀ᶠ n in atTop, 0 < periodicCount m W (u n) := by
    filter_upwards [(tendsto_atTop_of_ratio_one a u ha hu).eventually (eventually_ge_atTop 1)] with n hn
    exact periodicCount_pos m hm W hne hlegal (u n) hn
  exact logarithmic_sandwich a E (fun n => periodicCount m W (l n))
    (fun n => periodicCount m W (u n)) (fun n => fiberBudget m (l n) (D n))
    (fun n => fiberBudget m (c n) (D n)) (periodicGrowth m W)
    hlpos hupos (Eventually.of_forall (fun n => fiberBudget_positive m (l n) (D n)))
    (Eventually.of_forall (fun n => fiberBudget_positive m (c n) (D n))) hlower hupper
    (sampled_periodic_limit m hm W hne hlegal a l ha hl)
    (sampled_periodic_limit m hm W hne hlegal a u ha hu)
    (sampled_fiber_cost m a l D ha hl hD) (sampled_fiber_cost m a c D ha hc hD)

end KroneckerPeriodicFiberSandwich
end

/- Original module: KroneckerConditionalIntegerEulerLimit -/
section
/-! Integer-frame limit conditional on the two finite surgery comparisons.
The exact edit allowance, padding, comparison lengths and logarithmic budget
are discharged here. Actual surgery maps and their fiber bounds remain open. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerConditionalIntegerEulerLimit
open KroneckerPeriodicWords KroneckerPeriodicBounds KroneckerPeriodicTail
open KroneckerFiberBudget KroneckerFrameBadDensity KroneckerWordEditCost
open KroneckerIntegerEditDensity KroneckerSurgeryPadding KroneckerIntegerComparisonLengths
open KroneckerPeriodicFiberSandwich KroneckerSampledPeriodicLimit KroneckerComparisonLengthDivergence


end KroneckerConditionalIntegerEulerLimit
end
