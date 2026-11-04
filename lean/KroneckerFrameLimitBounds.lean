import KroneckerFrameObservables

/- Original module: KroneckerFiniteFrameLogBounds -/
section
set_option autoImplicit false
namespace KroneckerFiniteFrameLogBounds
open KroneckerWordCounts KroneckerFrameBadDensity KroneckerFrameWord KroneckerFrameObservables

theorem finite_frame_log_bounds (m : ℕ) (hm : 3 ≤ m) (x : FramePoint) (ha : 0 < x.a)
    (hlegal : ∀ r ∈ frameWord x.a x.b x.d, 1 ≤ r ∧ r ≤ m-1) :
    Real.log (m : ℝ)/2 ≤ value m x ∧
      value m x ≤ ((m : ℝ)*m*Real.log 2)*(((x.a : ℝ)+1)/(x.a : ℝ)) := by
  have hne : frameWord x.a x.b x.d ≠ [] := by
    intro he
    have h := congrArg List.length he
    simp only [frameWord_length,List.length_nil] at h
    omega
  have hb := KroneckerWordBounds.runCount_bounds m (m-1) hm le_rfl _ hne hlegal
  have hp := KroneckerWordBounds.runCount_pos m hm _ hne hlegal
  have haR : (0 : ℝ) < x.a := by exact_mod_cast ha
  have hmR : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  constructor
  · have hl := KroneckerLogCountBounds.log_power_lower (by omega : 0 < m) hb.1
    rw [frameWord_length] at hl
    have he : (x.a : ℝ) ≤ 2*(((x.a+1+1)/2 : ℕ) : ℝ) := by
      exact_mod_cast (show x.a ≤ 2*((x.a+1+1)/2) by omega)
    apply (le_div_iff₀ haR).mpr
    have hmul := mul_le_mul_of_nonneg_right he hmR
    nlinarith
  · have hu := Real.log_le_log (by exact_mod_cast hp : (0 : ℝ) < runCount m (frameWord x.a x.b x.d) 0)
      (by exact_mod_cast hb.2 : (runCount m (frameWord x.a x.b x.d) 0 : ℝ) ≤
        (2 : ℝ)^(m*((m-1)+1)*(frameWord x.a x.b x.d).length))
    rw [Real.log_pow,frameWord_length,show m-1+1=m by omega] at hu
    have h := div_le_div_of_nonneg_right hu haR.le
    simpa only [value,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm,
      div_eq_mul_inv] using h

end KroneckerFiniteFrameLogBounds
end

/- Original module: KroneckerFrameLimitBounds -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFrameLimitBounds
open KroneckerFrameObservables KroneckerFrameBadDensity

theorem frame_limit_bounds (m : ℕ) (hm : 3 ≤ m) (x : ℕ → FramePoint) (L : ℝ)
    (ha : Tendsto (fun n => (x n).a) atTop atTop)
    (hlegal : ∀ᶠ n in atTop, ∀ r ∈ frameWord (x n).a (x n).b (x n).d, 1 ≤ r ∧ r ≤ m-1)
    (hL : Tendsto (fun n => value m (x n)) atTop (𝓝 L)) :
    Real.log (m : ℝ)/2 ≤ L ∧ L ≤ (m : ℝ)*m*Real.log 2 := by
  have hb : ∀ᶠ n in atTop, Real.log (m : ℝ)/2 ≤ value m (x n) ∧
      value m (x n) ≤ ((m : ℝ)*m*Real.log 2)*(((x n).a : ℝ)+1)/((x n).a : ℝ) := by
    filter_upwards [ha.eventually (eventually_ge_atTop 1),hlegal] with n hn hl
    have h := KroneckerFiniteFrameLogBounds.finite_frame_log_bounds m hm (x n) (by omega) hl
    exact ⟨h.1,by simpa only [mul_div_assoc] using h.2⟩
  have hu : Tendsto (fun n => ((m : ℝ)*m*Real.log 2)*(((x n).a : ℝ)+1)/((x n).a : ℝ))
      atTop (𝓝 ((m : ℝ)*m*Real.log 2)) := by
    simpa only [Nat.cast_add,Nat.cast_one,mul_div_assoc,mul_one] using
      (KroneckerSampledPeriodicLimit.successor_length_density (fun n => (x n).a) ha).const_mul
        ((m : ℝ)*m*Real.log 2)
  exact ⟨ge_of_tendsto hL (hb.mono (fun _ h => h.1)),
    le_of_tendsto_of_tendsto hL hu (hb.mono (fun _ h => h.2))⟩

end KroneckerFrameLimitBounds
end
