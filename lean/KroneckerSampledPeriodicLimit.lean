import KroneckerIntegerComparisonLengths
import KroneckerSublinearFiberCost

/- Original module: KroneckerComparisonLengthDivergence -/
section
/-! Comparison lengths asymptotic to the dimension themselves tend to infinity. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerComparisonLengthDivergence
open KroneckerIntegerComparisonLengths

theorem tendsto_atTop_of_ratio_one (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ))) :
    Tendsto b atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [ha.eventually (eventually_ge_atTop (2*K+1)),
    (tendsto_order.1 hr).1 (1/2) (by norm_num)] with n hn hratio
  have ha₀ : (0 : ℝ) < a n := by exact_mod_cast (show 0 < a n by omega)
  have hb := (lt_div_iff₀ ha₀).mp hratio
  have hK : (2 : ℝ)*(K : ℝ)+1 ≤ (a n : ℝ) := by exact_mod_cast hn
  have hKB : (K : ℝ) ≤ (b n : ℝ) := by linarith
  exact_mod_cast hKB


end KroneckerComparisonLengthDivergence
end

/- Original module: KroneckerSampledPeriodicLimit -/
section
/-! Periodic entropy is unchanged by sampling at comparison lengths asymptotic to a. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerSampledPeriodicLimit
open KroneckerPeriodicWords KroneckerPeriodicLog KroneckerPeriodicTail KroneckerPeriodicLimit
open KroneckerComparisonLengthDivergence

theorem sampled_periodic_limit (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hlegal : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (a b : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ))) :
    Tendsto (fun n => Real.log (periodicCount m W (b n) : ℝ)/(a n : ℝ))
      atTop (𝓝 (periodicGrowth m W)) := by
  have hb := tendsto_atTop_of_ratio_one a b ha hr
  have h := ((periodicLog_limit m hm W hne hlegal).comp hb).mul hr
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [hb.eventually (eventually_ge_atTop 1)] with n hn
  have hb₀ : (b n : ℝ) ≠ 0 := by exact_mod_cast (show b n ≠ 0 by omega)
  dsimp [Function.comp_def, periodicLog]
  field_simp

theorem sampled_fiber_cost (m : ℕ) (a b D : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)))
    (hD : Tendsto (fun n => (D n : ℝ)/(a n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => Real.log (KroneckerFiberBudget.fiberBudget m (b n) (D n) : ℝ)/(a n : ℝ))
      atTop (𝓝 0) := by
  have hb := tendsto_atTop_of_ratio_one a b ha hr
  have hDb : Tendsto (fun n => (D n : ℝ)/(b n : ℝ)) atTop (𝓝 0) := by
    have h := hD.div hr (by norm_num)
    simp only [zero_div] at h
    apply h.congr'
    filter_upwards [ha.eventually (eventually_ge_atTop 1)] with n hn
    have ha₀ : (a n : ℝ) ≠ 0 := by exact_mod_cast (show a n ≠ 0 by omega)
    change ((D n : ℝ)/(a n : ℝ))/((b n : ℝ)/(a n : ℝ)) = (D n : ℝ)/(b n : ℝ)
    field_simp
  have h := (KroneckerSublinearFiberCost.normalized_fiber_cost_limit m b D hb hDb).mul hr
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [hb.eventually (eventually_ge_atTop 1)] with n hn
  have hb₀ : (b n : ℝ) ≠ 0 := by exact_mod_cast (show b n ≠ 0 by omega)
  unfold KroneckerNormalizedFiberBound.normalizedFiberLog
  field_simp

theorem successor_length_density (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => ((a n+1 : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have hone : Tendsto (fun n => (a n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Nat.sub_zero] using KroneckerShiftedBlockDensity.sub_height_ratio a ha 0
  have hz : Tendsto (fun n => (1 : ℝ)/(a n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using hone.add hz

end KroneckerSampledPeriodicLimit
end
