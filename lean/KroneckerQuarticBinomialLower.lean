import KroneckerNormalizedBinomialIdentity

/- Original module: KroneckerQuarticBinomialLog -/
section
set_option autoImplicit false
namespace KroneckerQuarticBinomialLog
open KroneckerNormalizedBinomialIdentity KroneckerLogFactorialRemainder

theorem log_quartic_growth_base :
    Real.log (256/27 : ℝ)=4*Real.log 4-3*Real.log 3 := by
  rw [show (256/27:ℝ)=4^4/3^3 by norm_num,Real.log_div (by norm_num) (by norm_num),
    Real.log_pow,Real.log_pow]
  norm_num

/-- Exact cancellation leaves the square-root scale and a bounded Stirling remainder. -/
theorem quartic_binomial_log_identity (n : ℕ) (hn : 0<n) :
    Real.log ((4*n).choose n : ℝ)=
      n*Real.log (256/27 : ℝ)-Real.log (n:ℝ)/2+
      (Real.log (Stirling.stirlingSeq (4*n))-Real.log (Stirling.stirlingSeq n)-
        Real.log (Stirling.stirlingSeq (3*n))+(Real.log 2-Real.log 3)/2) := by
  have h := normalized_binomial_identity (4*n) n hn (by omega)
  have hnR : (n:ℝ)≠0 := by positivity
  rw [show 4*n-n=3*n by omega] at h
  simp only [Nat.cast_mul,Nat.cast_ofNat,mul_div_cancel_right₀ _ hnR] at h
  have h' := (div_eq_iff hnR).mp h
  rw [remainder_identity (4*n) (by omega),remainder_identity n (by omega),
    remainder_identity (3*n) (by omega)] at h'
  simp only [Nat.cast_mul,Nat.cast_ofNat] at h'
  rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hnR,
    Real.log_mul (by norm_num : (3:ℝ)≠0) hnR] at h'
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [log_quartic_growth_base]
  field_simp at h'
  linear_combination (1/2:ℝ)*h'+(1/2:ℝ)*h4

end KroneckerQuarticBinomialLog
end

/- Original module: KroneckerQuarticBinomialLower -/
section
set_option autoImplicit false
namespace KroneckerQuarticBinomialLower
open KroneckerQuarticBinomialLog

noncomputable def binomialLowerConstant : ℝ := Real.exp
  (Real.log (Real.sqrt Real.pi)-2*Real.log (Stirling.stirlingSeq 1)+
    (Real.log 2-Real.log 3)/2)

theorem binomial_lower_constant_pos : 0<binomialLowerConstant := Real.exp_pos _

theorem positive_stirling_upper (n : ℕ) (hn : 0<n) :
    Stirling.stirlingSeq n≤Stirling.stirlingSeq 1 := by
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (n-1))
  simpa only [Function.comp_apply,Nat.succ_eq_add_one,Nat.sub_add_cancel hn] using h

/-- A uniform square-root binomial lower bound, proved for every positive index. -/
theorem quartic_binomial_lower (n : ℕ) (hn : 0<n) :
    binomialLowerConstant*(256/27:ℝ)^n/Real.sqrt n≤((4*n).choose n : ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hc : (0:ℝ)<(4*n).choose n := by exact_mod_cast Nat.choose_pos (by omega : n≤4*n)
  have hs (k : ℕ) (hk : 0<k) : 0<Stirling.stirlingSeq k := by
    exact lt_of_lt_of_le (by positivity : (0:ℝ)<Real.sqrt Real.pi)
      (Stirling.sqrt_pi_le_stirlingSeq (by omega))
  have hlow := Real.log_le_log (by positivity : (0:ℝ)<Real.sqrt Real.pi)
    (Stirling.sqrt_pi_le_stirlingSeq (n:=4*n) (by omega))
  have hu := Real.log_le_log (hs n hn) (positive_stirling_upper n hn)
  have hv := Real.log_le_log (hs (3*n) (by omega)) (positive_stirling_upper (3*n) (by omega))
  apply (Real.log_le_log_iff (by dsimp [binomialLowerConstant]; positivity) hc).mp
  rw [Real.log_div (by dsimp [binomialLowerConstant]; positivity) (by positivity),
    Real.log_mul (ne_of_gt binomial_lower_constant_pos) (by positivity),
    Real.log_pow,Real.log_sqrt hnR.le,binomialLowerConstant,Real.log_exp,
    quartic_binomial_log_identity n hn]
  linarith

end KroneckerQuarticBinomialLower
end
