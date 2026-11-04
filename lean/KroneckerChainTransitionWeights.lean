import Mathlib.Analysis.SpecialFunctions.Pow.Real
import KroneckerChainBinFamily

/- Original module: KroneckerChainBinSizeEstimates -/
section
set_option autoImplicit false
namespace KroneckerChainBinSizeEstimates
open KroneckerChainPositiveBins

/-- The transition-specific middle-block upper size, sharper than size<x. -/
theorem middle_bin_size_upper (x l r : ℝ) (i h : ℕ)
    (hl : InBin x i l) (hr : InBin x h r) :
    l+r-1<((i : ℝ)+(h : ℝ)+2)*(x/256) := by
  dsimp [InBin] at hl hr
  linarith [hl.2,hr.2]

/-- The adjacent internal-block upper size from the two lower bin endpoints. -/
theorem internal_bin_size_upper (x l r : ℝ) (j h : ℕ)
    (hl : InBin x j l) (hr : InBin x h r) :
    x-r-l≤(256-(h : ℝ)-(j : ℝ))*(x/256) := by
  dsimp [InBin] at hl hr
  linarith [hl.1,hr.1]

theorem transition_size_factors_positive (i j h : ℕ) (hb : j+h≤253) :
    (0 : ℝ)<(i : ℝ)+(h : ℝ)+2 ∧ 0<(256-(h : ℝ)-(j : ℝ)) := by
  have hbR : (j : ℝ)+(h : ℝ)≤253 := by exact_mod_cast hb
  constructor
  · positivity
  · linarith

end KroneckerChainBinSizeEstimates
end

/- Original module: KroneckerTransitionInversePowers -/
section
set_option autoImplicit false
namespace KroneckerTransitionInversePowers

theorem inverse_power_kernel (u v : ℝ) (hu : 0<u) (hv : 0<v) :
    u^(-3/2 : ℝ)*v^(-1/2 : ℝ)=1/Real.sqrt (u^3*v) := by
  have hpow : (u^3 : ℝ)^(-1/2 : ℝ)=u^(-3/2 : ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hu.le]
    norm_num
  rw [Real.sqrt_eq_rpow,one_div,←Real.rpow_neg (mul_nonneg (pow_nonneg hu.le _) hv.le)]
  simp only [neg_div] at hpow ⊢
  rw [Real.mul_rpow (pow_nonneg hu.le _) hv.le,hpow]

theorem scaled_inverse_kernel (s u v : ℝ) (hs : 0<s) (hu : 0<u) (hv : 0<v) :
    (s*u)^(-3/2 : ℝ)*(s*v)^(-1/2 : ℝ)=s^(-2 : ℝ)/Real.sqrt (u^3*v) := by
  have he : s^(-3/2 : ℝ)*s^(-1/2 : ℝ)=s^(-2 : ℝ) := by
    rw [←Real.rpow_add hs]
    norm_num
  rw [Real.mul_rpow hs.le hu.le,Real.mul_rpow hs.le hv.le]
  calc
    s^(-3/2 : ℝ)*u^(-3/2 : ℝ)*(s^(-1/2 : ℝ)*v^(-1/2 : ℝ))=
      (s^(-3/2 : ℝ)*s^(-1/2 : ℝ))*(u^(-3/2 : ℝ)*v^(-1/2 : ℝ)) := by ring
    _=s^(-2 : ℝ)/Real.sqrt (u^3*v) := by rw [he,inverse_power_kernel u v hu hv]; ring

theorem transition_inverse_lower (s u v m b : ℝ) (hs : 0<s) (hu : 0<u) (hv : 0<v)
    (hm : 0<m) (hb : 0<b) (hmu : m≤s*u) (hbv : b≤s*v) :
    s^(-2 : ℝ)/Real.sqrt (u^3*v)≤m^(-3/2 : ℝ)*b^(-1/2 : ℝ) := by
  rw [←scaled_inverse_kernel s u v hs hu hv]
  exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hm hmu (by norm_num))
    (Real.rpow_le_rpow_of_nonpos hb hbv (by norm_num))
    (Real.rpow_nonneg (mul_nonneg hs.le hv.le) _) (Real.rpow_nonneg hm.le _)

end KroneckerTransitionInversePowers
end

/- Original module: KroneckerChainTransitionWeights -/
section
set_option autoImplicit false
namespace KroneckerChainTransitionWeights
open KroneckerTransitionInversePowers KroneckerChainBinSizeEstimates KroneckerChainBinFamily
open KroneckerChainFlowRecovery
open KroneckerChainBlockSizes KroneckerChainBlockNeighbors KroneckerChainIncidence

noncomputable def transitionWeight (i j h : ℕ) : ℝ :=
  1/Real.sqrt (((i : ℝ)+(h : ℝ)+2)^3*(256-(h : ℝ)-(j : ℝ)))

theorem bin_scale_inverse (x : ℝ) (hx : 0<x) :
    (x/256)^(-2 : ℝ)=(256 : ℝ)^2*x^(-2 : ℝ) := by
  rw [Real.div_rpow hx.le (by norm_num)]
  norm_num [Real.rpow_neg,Real.rpow_two]
  ring

/-- The manuscript transition weight for the actual middle and adjacent internal sizes. -/
theorem chain_transition_weight_lower (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ)
    (hx : 100000≤x) (D : BinData n x l r i h) (t : Fin n) :
    (256 : ℝ)^2*x^(-2 : ℝ)*transitionWeight (i t) (i (t+1)) (h t)≤
      (blockSize n x l r (middleBlock t.castSucc))^(-3/2 : ℝ)*
      (blockSize n x l r (internalBlock t))^(-1/2 : ℝ) := by
  have hb := bin_block_size_bounds n x l r i h hx D
  have hp := transition_size_factors_positive (i t) (i (t+1)) (h t) (D.next_bound t t.isLt)
  have hm := middle_bin_size_upper x (l t) (r t) (i t) (h t)
    (D.left_bin t (by omega)) (D.right_bin t (by omega))
  have hi := internal_bin_size_upper x (l (t+1)) (r t) (i (t+1)) (h t)
    (D.left_bin (t+1) (by omega)) (D.right_bin t (by omega))
  rw [size_middle,size_internal]
  have hmpos : 0<l t+r t-1 := by
    have he := (hb (middleBlock t.castSucc)).1
    rw [size_middle] at he
    simp only [middleSize,Fin.val_castSucc] at he
    linarith
  have hipos : 0<x-r t-l (t+1) := by
    have he := (hb (internalBlock t)).1
    rw [size_internal] at he
    dsimp only [internalSize] at he
    linarith
  have he := transition_inverse_lower (x/256) ((i t : ℝ)+(h t : ℝ)+2)
    (256-(h t : ℝ)-(i (t+1) : ℝ)) (l t+r t-1) (x-r t-l (t+1))
    (by linarith) hp.1 hp.2 hmpos hipos (by nlinarith [hm]) (by nlinarith [hi])
  rw [bin_scale_inverse x (by linarith)] at he
  simpa only [transitionWeight,div_eq_mul_inv,one_mul,middleSize,internalSize,Fin.val_castSucc] using he

end KroneckerChainTransitionWeights
end
