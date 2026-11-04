import KroneckerPeriodicLimit

/- Original module: KroneckerBlockDensity -/
section
/-! Exact floor-error bounds and the asymptotic density of fixed-size blocks. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerBlockDensity

theorem normalized_div_bounds (a K : ℕ) (ha : 0 < a) (hK : 0 < K) :
    1/(K : ℝ)-1/(a : ℝ) ≤ ((a/K : ℕ) : ℝ)/(a : ℝ) ∧
      ((a/K : ℕ) : ℝ)/(a : ℝ) ≤ 1/(K : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hlo : (a : ℝ) < (K : ℝ)*(((a/K : ℕ) : ℝ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ a hK
  have hup : ((a/K : ℕ) : ℝ)*(K : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self a K
  constructor
  · apply (le_div_iff₀ ha').2
    have heq : (1/(K : ℝ)-1/(a : ℝ))*(a : ℝ) = (a : ℝ)/(K : ℝ)-1 := by
      field_simp
    rw [heq]
    have h : (a : ℝ)/(K : ℝ) < ((a/K : ℕ) : ℝ)+1 :=
      (div_lt_iff₀ hK').2 (by nlinarith)
    linarith
  · apply (div_le_iff₀ ha').2
    have h := (le_div_iff₀ hK').2 hup
    simpa [div_eq_mul_inv, mul_comm] using h

theorem block_density_limit (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (K : ℕ) (hK : 0 < K) :
    Tendsto (fun n => ((a n/K : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (1/(K : ℝ))) := by
  have hreal : Tendsto (fun n => (a n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp ha
  have hz : Tendsto (fun n => (1 : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hreal
  have hlo : Tendsto (fun n => 1/(K : ℝ)-1/(a n : ℝ)) atTop (𝓝 (1/(K : ℝ))) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1/(K : ℝ)) atTop (𝓝 (1/(K : ℝ)))).sub hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [ha.eventually (eventually_ge_atTop 1)] with n hn
    exact (normalized_div_bounds (a n) K hn hK).1
  · filter_upwards [ha.eventually (eventually_ge_atTop 1)] with n hn
    exact (normalized_div_bounds (a n) K hn hK).2

end KroneckerBlockDensity
end

/- Original module: KroneckerShiftedBlockDensity -/
section
/-! Fixed boundary offsets do not change the density of fixed-size blocks. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerShiftedBlockDensity
open KroneckerBlockDensity

theorem sub_height_atTop (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (c : ℕ) :
    Tendsto (fun n => a n-c) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [ha.eventually (eventually_ge_atTop (b+c))] with n hn
  omega

theorem sub_height_ratio (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (c : ℕ) :
    Tendsto (fun n => ((a n-c : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have hreal : Tendsto (fun n => (a n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp ha
  have hz : Tendsto (fun n => (c : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hreal
  have h : Tendsto (fun n => (1 : ℝ)-(c : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hz
  apply h.congr'
  filter_upwards [ha.eventually (eventually_ge_atTop (c+1))] with n hn
  have hne : (a n : ℝ) ≠ 0 := by exact_mod_cast (show a n ≠ 0 from by omega)
  rw [Nat.cast_sub (by omega : c ≤ a n)]
  field_simp

theorem shifted_block_density (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (c K : ℕ) (hK : 0 < K) :
    Tendsto (fun n => (((a n-c)/K : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (1/(K : ℝ))) := by
  have hlimit := block_density_limit (fun n => a n-c) (sub_height_atTop a ha c) K hK
  have hb : ∀ᶠ n in atTop, ((a n-c : ℕ) : ℝ) ≠ 0 := by
    filter_upwards [ha.eventually (eventually_ge_atTop (c+1))] with n hn
    exact_mod_cast (show a n-c ≠ 0 from by omega)
  have h := KroneckerLogic.normalization_transport
    (a := fun n => (a n : ℝ)) (b := fun n => ((a n-c : ℕ) : ℝ))
    (V := fun n => (((a n-c)/K : ℕ) : ℝ)) 1 (1/(K : ℝ)) hb
    (sub_height_ratio a ha c) hlimit
  simpa only [one_mul] using h

end KroneckerShiftedBlockDensity
end
