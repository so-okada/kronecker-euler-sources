import KroneckerPositiveDensity

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerAsymptoticCollarBudget

theorem eventual_collar_budget (a L T P : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (m : ℕ) (η l t p : ℝ) (hη : 0 ≤ η)
    (hl : Tendsto (fun n => (L n : ℝ)/(a n : ℝ)) atTop (𝓝 l))
    (ht : Tendsto (fun n => (T n : ℝ)/(a n : ℝ)) atTop (𝓝 t))
    (hp : Tendsto (fun n => (P n : ℝ)/(a n : ℝ)) atTop (𝓝 p))
    (hroom : (1+η)*l < t) (hbudget : t-l+(m+1 : ℕ)*η*l < p) :
    ∀ᶠ n in atTop, (1+η)*(L n : ℝ) ≤ T n ∧
      ((T n-L n : ℕ) : ℝ)+(m+1 : ℕ)*η*(L n : ℝ) ≤ P n := by
  have hroomlim := ht.sub (hl.const_mul (1+η))
  have hbudgetlim := (hp.sub (ht.sub hl)).sub (hl.const_mul ((m+1 : ℕ)*η))
  filter_upwards [ha.eventually (eventually_ge_atTop 1),
    (tendsto_order.1 hroomlim).1 0 (by linarith),
    (tendsto_order.1 hbudgetlim).1 0 (by linarith)] with n hn hroomn hbudgetn
  have haR : (0 : ℝ) < a n := by exact_mod_cast (show 0 < a n by omega)
  have hr : 0 < (T n : ℝ)-(1+η)*(L n : ℝ) :=
    (div_pos_iff_of_pos_right haR).mp (by simpa only [sub_div,mul_div_assoc] using hroomn)
  have hb : 0 < (P n : ℝ)-((T n : ℝ)-(L n : ℝ))-(m+1 : ℕ)*η*(L n : ℝ) :=
    (div_pos_iff_of_pos_right haR).mp (by simpa only [sub_div,mul_div_assoc] using hbudgetn)
  have hLT : L n ≤ T n := by
    have hnon : 0 ≤ η*(L n : ℝ) := mul_nonneg hη (Nat.cast_nonneg _)
    exact_mod_cast (show (L n : ℝ) ≤ T n by nlinarith)
  refine ⟨by linarith,?_⟩
  rw [Nat.cast_sub hLT]
  linarith

end KroneckerAsymptoticCollarBudget
