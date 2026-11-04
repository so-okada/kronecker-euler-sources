import KroneckerScaffoldDensity
import KroneckerLogCountBounds

/- Original module: KroneckerPowerLowerLimits -/
section
/-! Pass a finite power lower bound to an eventual logarithmic lower bound. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPowerLowerLimits
open KroneckerLogCountBounds KroneckerScaffoldDensity

theorem eventual_lower_of_powers (a C k : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (δ : ℝ) (hk : Tendsto (fun n => (k n : ℝ)/(a n : ℝ)) atTop (𝓝 δ))
    (A : ℕ) (hA : 0 < A) (hpow : ∀ᶠ n in atTop, A^(k n) ≤ C n) :
    ∀ ε > 0, ∀ᶠ n in atTop, δ * Real.log (A : ℝ)-ε ≤ Real.log (C n : ℝ)/(a n : ℝ) := by
  intro ε hε
  have hlim := hk.mul (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => Real.log (A : ℝ)) atTop (𝓝 (Real.log (A : ℝ))))
  have hlo := (tendsto_order.1 hlim).1 (δ * Real.log (A : ℝ)-ε) (by linarith)
  filter_upwards [hlo, hpow, ha.eventually (eventually_ge_atTop 1)] with n hn hp han
  have hpos : (0 : ℝ) < a n := by exact_mod_cast han
  exact (le_of_lt hn).trans (normalized_log_power_lower hA hp (a n : ℝ) hpos)

theorem scaffold_eventual_lower (a b C : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hb : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)))
    (c s K A : ℕ) (hK : 0 < K) (hA : 0 < A)
    (hpow : ∀ᶠ n in atTop, A^((a n-c)/K-(b n+s)) ≤ C n) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      Real.log (A : ℝ)/(K : ℝ)-ε ≤ Real.log (C n : ℝ)/(a n : ℝ) := by
  have h := eventual_lower_of_powers a C (fun n => (a n-c)/K-(b n+s)) ha
    (1/(K : ℝ)) (surviving_hole_density a b ha hb c s K hK) A hA hpow
  simpa [div_eq_mul_inv, mul_comm] using h

end KroneckerPowerLowerLimits
end

/- Original module: KroneckerRationalPeriodLimit -/
section
/-! The final period-length normalization in the rational lower bound. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerRationalPeriodLimit
open KroneckerShiftedBlockDensity KroneckerPeriodicLog KroneckerPeriodicTail KroneckerPeriodicLimit

theorem hole_period_scale (q : ℕ) (hq : 0 < q) :
    Tendsto (fun J : ℕ => ((J-3 : ℕ) : ℝ)/((J*q+3 : ℕ) : ℝ)) atTop (𝓝 (1/(q : ℝ))) := by
  have hsub := sub_height_ratio (fun n => n) tendsto_id 3
  have hz : Tendsto (fun J : ℕ => (3 : ℝ)/(J : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun J : ℕ => (q : ℝ)+3/(J : ℝ)) atTop (𝓝 (q : ℝ)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (q : ℝ)) atTop (𝓝 (q : ℝ))).add hz
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  apply (hsub.div hden hq0).congr'
  filter_upwards [eventually_ge_atTop 1] with J hJ
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 from by omega)
  have hd0 : (J : ℝ)*(q : ℝ)+3 ≠ 0 := by positivity
  change (((J-3 : ℕ) : ℝ)/(J : ℝ))/((q : ℝ)+3/(J : ℝ)) =
    ((J-3 : ℕ) : ℝ)/((J*q+3 : ℕ) : ℝ)
  push_cast
  field_simp

theorem periodic_hole_log_limit (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (q : ℕ) (hq : 0 < q) :
    Tendsto (fun J : ℕ => periodicLog m W (J-3)/((J*q+3 : ℕ) : ℝ)) atTop
      (𝓝 (periodicGrowth m W/(q : ℝ))) := by
  have hlimit := (periodicLog_limit m hm W hne hr).comp
    (sub_height_atTop (fun n => n) tendsto_id 3)
  have hb : ∀ᶠ J : ℕ in atTop, ((J-3 : ℕ) : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 4] with J hJ
    exact_mod_cast (show J-3 ≠ 0 from by omega)
  have h := KroneckerLogic.normalization_transport
    (a := fun J : ℕ => ((J*q+3 : ℕ) : ℝ)) (b := fun J : ℕ => ((J-3 : ℕ) : ℝ))
    (V := fun J => periodicLog m W (J-3)) (1/(q : ℝ)) (periodicGrowth m W)
    hb (hole_period_scale q hq) hlimit
  simpa [div_eq_mul_inv, mul_comm] using h

end KroneckerRationalPeriodLimit
end

/- Original module: KroneckerTwoStageLower -/
section
/-! Passing from every fixed-period lower bound to their limiting value
without assuming a convergence rate uniform in the period. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerTwoStageLower

theorem eventual_lower_of_limit_of_bounds (H L : ℕ → ℝ) (ell : ℝ)
    (hL : Tendsto L atTop (𝓝 ell)) (J0 : ℕ)
    (hbound : ∀ J, J0 ≤ J → ∀ ε > 0, ∀ᶠ n in atTop, L J-ε ≤ H n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ell-ε ≤ H n := by
  intro ε hε
  have hnear := (tendsto_order.1 hL).1 (ell-ε/2) (by linarith)
  obtain ⟨J,hJ,hnearJ⟩ := ((eventually_ge_atTop J0).and hnear).exists
  filter_upwards [hbound J hJ (ε/2) (by linarith)] with n hn
  linarith

end KroneckerTwoStageLower
end

/- Original module: KroneckerRationalLowerReduction -/
section
/-! The rational lower-limit argument reduced to explicit finite scaffold
power bounds and a sublinear bad-window budget. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerRationalLowerReduction
open KroneckerPeriodicWords KroneckerPeriodicBounds KroneckerPeriodicLog KroneckerPeriodicTail
open KroneckerPowerLowerLimits KroneckerRationalPeriodLimit KroneckerTwoStageLower

theorem rational_lower_of_scaffold_bounds (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (q : ℕ) (hq : 0 < q)
    (a b C : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hb : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)))
    (hpow : ∀ J, 4 ≤ J → ∀ᶠ n in atTop,
      (periodicCount m W (J-3))^((a n-2)/(J*q+3)-(b n+1)) ≤ C n) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      periodicGrowth m W/(q : ℝ)-ε ≤ Real.log (C n : ℝ)/(a n : ℝ) := by
  apply eventual_lower_of_limit_of_bounds (fun n => Real.log (C n : ℝ)/(a n : ℝ))
    (fun J => periodicLog m W (J-3)/((J*q+3 : ℕ) : ℝ))
    (periodicGrowth m W/(q : ℝ)) (periodic_hole_log_limit m hm W hne hr q hq) 4
  intro J hJ
  exact scaffold_eventual_lower a b C ha hb 2 1 (J*q+3)
    (periodicCount m W (J-3)) (by omega)
    (periodicCount_pos m hm W hne hr (J-3) (by omega)) (hpow J hJ)

end KroneckerRationalLowerReduction
end
