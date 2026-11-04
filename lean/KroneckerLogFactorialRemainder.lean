import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

/-! An exact logarithmic factorial remainder, preparing the adjacent-dimension asymptotic. -/
set_option autoImplicit false
namespace KroneckerLogFactorialRemainder

noncomputable def remainder (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ)-((n : ℝ)*Real.log (n : ℝ)-n)

theorem remainder_identity (n : ℕ) (hn : n≠0) :
    remainder n=Real.log (Stirling.stirlingSeq n)+(Real.log 2+Real.log (n : ℝ))/2 := by
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div hnR (ne_of_gt (Real.exp_pos 1)),Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ)≠0) hnR] at h
  unfold remainder
  linarith

end KroneckerLogFactorialRemainder
