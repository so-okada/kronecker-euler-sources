import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-! The logarithmic correction in the finite lower bound vanishes jointly as
a tends to infinity and k/a tends to zero. This does not assume convergence of
the Euler observable and does not turn a lower bound into a limit theorem. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerLowerEntropyKernel
open Filter
open scoped Topology

theorem log_ratio_bounds (a k : ℕ) (hk : 1 ≤ k) (hka : k ≤ a) :
    -Real.log (a : ℝ)/(a : ℝ) ≤ Real.log ((k : ℝ)/a)/(a : ℝ) ∧
      Real.log ((k : ℝ)/a)/(a : ℝ) ≤ 0 := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  constructor
  · apply div_le_div_of_nonneg_right _ hap.le
    rw [Real.log_div hkp.ne' hap.ne']
    linarith [Real.log_natCast_nonneg k]
  · apply div_nonpos_of_nonpos_of_nonneg _ hap.le
    apply Real.log_nonpos (div_nonneg hkp.le hap.le)
    exact (div_le_one hap).mpr (by exact_mod_cast hka)

variable {α : Type*} {l : Filter α} (a k : α → ℕ)

theorem eventually_positive (ha : Tendsto (fun i => (a i : ℝ)) l atTop) :
    ∀ᶠ i in l, 0 < a i := by
  filter_upwards [ha.eventually_gt_atTop 0] with i hi
  exact_mod_cast hi

theorem eventually_small_ratio (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0)) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ i in l, c * (k i : ℝ) ≤ (a i : ℝ) := by
  have hr := hk.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1/c))
  filter_upwards [eventually_positive a ha, hr] with i hai hri
  have hap : (0 : ℝ) < a i := by exact_mod_cast hai
  have h := (div_lt_iff₀ hap).mp hri
  have hh := mul_lt_mul_of_pos_left h hc
  have hcan : c * (1/c * (a i : ℝ)) = a i := by field_simp
  rw [hcan] at hh
  exact hh.le

theorem eventually_le (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0)) :
    ∀ᶠ i in l, k i ≤ a i := by
  filter_upwards [eventually_small_ratio a k ha hk 1 (by norm_num)] with i hi
  exact_mod_cast (by simpa using hi : (k i : ℝ) ≤ a i)

theorem log_over_height (ha : Tendsto (fun i => (a i : ℝ)) l atTop) :
    Tendsto (fun i => Real.log (a i : ℝ)/(a i : ℝ)) l (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ha
  simpa [Function.comp_def] using h

theorem constant_over_height (ha : Tendsto (fun i => (a i : ℝ)) l atTop) (c : ℝ) :
    Tendsto (fun i => c/(a i : ℝ)) l (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp ha).const_mul c
  simpa [div_eq_mul_inv] using h

theorem log_ratio_over_height (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hkpos : ∀ᶠ i in l, 1 ≤ k i) :
    Tendsto (fun i => Real.log ((k i : ℝ)/a i)/(a i : ℝ)) l (𝓝 0) := by
  have hb : ∀ᶠ i in l,
      0 ≤ -(Real.log ((k i : ℝ)/a i)/(a i : ℝ)) ∧
      -(Real.log ((k i : ℝ)/a i)/(a i : ℝ)) ≤ Real.log (a i : ℝ)/(a i : ℝ) := by
    filter_upwards [hkpos, eventually_le a k ha hk] with i hi hia
    have h := log_ratio_bounds (a i) (k i) hi hia
    simp only [neg_div] at h
    constructor <;> linarith
  have hs := squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)
    (log_over_height a ha)
  simpa using hs.neg

theorem predecessor_ratio (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hkpos : ∀ᶠ i in l, 1 ≤ k i) :
    Tendsto (fun i => ((k i-1 : ℕ) : ℝ)/(a i : ℝ)) l (𝓝 0) := by
  have h := hk.sub (constant_over_height a ha 1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [hkpos] with i hi
  rw [Nat.cast_sub hi, Nat.cast_one, sub_div]

def correction (C q : ℝ) (a k : ℕ) : ℝ :=
  Real.log C/a + (5/2 : ℝ)*(Real.log ((k : ℝ)/a)/a) +
    ((k-1 : ℕ) : ℝ)/a*Real.log q

theorem correction_tendsto (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hkpos : ∀ᶠ i in l, 1 ≤ k i) (C q : ℝ) :
    Tendsto (fun i => correction C q (a i) (k i)) l (𝓝 0) := by
  have h₁ := constant_over_height a ha (Real.log C)
  have h₂ := (log_ratio_over_height a k ha hk hkpos).const_mul (5/2 : ℝ)
  have h₃ := (predecessor_ratio a k ha hk hkpos).mul_const (Real.log q)
  simpa [correction] using (h₁.add h₂).add h₃

end KroneckerLowerEntropyKernel
