import KroneckerAsymptotics
import KroneckerNormalizedBinomialIdentity

section

/- Original module: KroneckerAdjacentParameters -/
section
/-! Exact integer parameters of the cited adjacent-dimension binomial formula. -/
set_option autoImplicit false
namespace KroneckerAdjacentParameters

def binomialSlope (m : ℕ) : ℕ := (m-1)^2
def binomialOffset (m : ℕ) : ℕ := (m-1)*m

theorem adjacent_parameter_bounds (m : ℕ) (hm : 3 ≤ m) :
    2 ≤ binomialSlope m ∧ 0 < m-1 := by
  have h : 2 ≤ m-1 := by omega
  unfold binomialSlope
  constructor
  · nlinarith
  · omega

theorem adjacent_parameter_difference (m : ℕ) (hm : 3 ≤ m) :
    binomialSlope m-1=m*(m-2) := by
  have h1 : m-1+1=m := Nat.sub_add_cancel (by omega)
  have h2 : m-2+2=m := Nat.sub_add_cancel (by omega)
  have h : (m-1)^2=m*(m-2)+1 := by nlinarith
  unfold binomialSlope
  omega

end KroneckerAdjacentParameters
end

/- Original module: KroneckerAdjacentFormulaValue -/
section
/-! The explicit numerical adjacent formula, with positivity proved internally. -/
set_option autoImplicit false
namespace KroneckerAdjacentFormulaValue
open KroneckerAdjacentParameters

noncomputable def adjacentValue (m a : ℕ) : ℝ :=
  (m : ℝ)/(((a : ℝ)+1)*(((m-1 : ℕ) : ℝ)*a+m))*
    ((binomialSlope m*a+binomialOffset m).choose a : ℝ)

noncomputable def centralValue (m : ℕ) : ℝ :=
  (binomialSlope m : ℝ)*Real.log (binomialSlope m : ℝ)-
    ((m*(m-2) : ℕ) : ℝ)*Real.log ((m*(m-2) : ℕ) : ℝ)

theorem adjacent_value_pos (m a : ℕ) (hm : 3 ≤ m) : 0 < adjacentValue m a := by
  have hC := (adjacent_parameter_bounds m hm).1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have ha : a ≤ binomialSlope m*a+binomialOffset m := by
    have := Nat.mul_le_mul_right a hC
    omega
  have hc : 0 < ((binomialSlope m*a+binomialOffset m).choose a : ℝ) := by
    exact_mod_cast Nat.choose_pos ha
  unfold adjacentValue
  positivity

end KroneckerAdjacentFormulaValue
end
end

section

/- Original module: KroneckerAdjacentLogIdentity -/
section
/-! Separate the adjacent formula's polynomial prefactor from its binomial logarithm. -/
set_option autoImplicit false
namespace KroneckerAdjacentLogIdentity
open KroneckerAdjacentParameters KroneckerAdjacentFormulaValue

theorem adjacent_log_identity (m a : ℕ) (hm : 3 ≤ m) :
    Real.log (adjacentValue m a)=Real.log (m : ℝ)-Real.log ((a+1 : ℕ) : ℝ)-
      Real.log (((m-1)*a+m : ℕ) : ℝ)+
      Real.log ((binomialSlope m*a+binomialOffset m).choose a : ℝ) := by
  have hC := (adjacent_parameter_bounds m hm).1
  have hma : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have ha : a ≤ binomialSlope m*a+binomialOffset m := by
    have := Nat.mul_le_mul_right a hC
    omega
  have hc : 0 < ((binomialSlope m*a+binomialOffset m).choose a : ℝ) := by
    exact_mod_cast Nat.choose_pos ha
  unfold adjacentValue
  rw [Real.log_mul (by positivity) (ne_of_gt hc),Real.log_div (ne_of_gt hma) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul]
  ring

end KroneckerAdjacentLogIdentity
end

/- Original module: KroneckerAffineNaturalLimits -/
section
/-! Affine natural arguments have the expected divergence and normalization. -/
set_option autoImplicit false
namespace KroneckerAffineNaturalLimits
open Filter
open scoped Topology

theorem affine_nat_atTop (C D : ℕ) (hC : 0 < C) :
    Tendsto (fun n : ℕ => C*n+D) atTop atTop := by
  apply tendsto_atTop_mono (fun n : ℕ => ?_) tendsto_id
  change n ≤ C*n+D
  have h := Nat.mul_le_mul_right n (show 1 ≤ C by omega)
  omega

theorem affine_nat_ratio (C D : ℕ) :
    Tendsto (fun n : ℕ => ((C*n+D : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 (C : ℝ)) := by
  have h : Tendsto (fun n : ℕ => (C : ℝ)+(D : ℝ)/(n : ℝ)) atTop (𝓝 (C : ℝ)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (C : ℝ)) atTop (𝓝 (C : ℝ))).add
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn
  push_cast
  field_simp

end KroneckerAffineNaturalLimits
end

/- Original module: KroneckerAffineBinomialComplement -/
section
/-! Exact natural subtraction for the affine binomial's complementary factorial. -/
set_option autoImplicit false
namespace KroneckerAffineBinomialComplement

theorem affine_binomial_complement (C D n : ℕ) (hC : 1 ≤ C) :
    C*n+D-n=(C-1)*n+D := by
  have hsum : C*n+D=((C-1)*n+D)+n := by
    calc
      C*n+D=(C-1+1)*n+D := by rw [Nat.sub_add_cancel hC]
      _ = ((C-1)*n+D)+n := by ring
  omega

theorem affine_binomial_strict (C D n : ℕ) (hC : 2 ≤ C) (hn : 0 < n) :
    n < C*n+D := by
  have h := Nat.mul_le_mul_right n hC
  omega

end KroneckerAffineBinomialComplement
end

/- Original module: KroneckerLogFactorialError -/
section
/-! The logarithmic factorial remainder is sublinear, proved from pinned Stirling. -/
set_option autoImplicit false
namespace KroneckerLogFactorialError
open Filter KroneckerLogFactorialRemainder
open scoped Topology

theorem factorial_remainder_sublinear :
    Tendsto (fun n : ℕ => remainder n/(n : ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hs0 := hs.div_atTop tendsto_natCast_atTop_atTop
  have hc0 : Tendsto (fun n : ℕ => Real.log 2/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl0 : Tendsto (fun n : ℕ => Real.log (n : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)/(n : ℝ)+
      (Real.log 2/(n : ℝ)+Real.log (n : ℝ)/(n : ℝ))/2) atTop (𝓝 0) := by
    simpa using hs0.add ((hc0.add hl0).div_const 2)
  apply ht.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  rw [remainder_identity n hn]
  ring

end KroneckerLogFactorialError
end

/- Original module: KroneckerSublinearAffine -/
section
/-! Sublinear errors remain negligible after a fixed positive affine index change. -/
set_option autoImplicit false
namespace KroneckerSublinearAffine
open Filter KroneckerAffineNaturalLimits
open scoped Topology

theorem sublinear_affine (f : ℕ → ℝ)
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)) atTop (𝓝 0))
    (C D : ℕ) (hC : 0 < C) :
    Tendsto (fun n : ℕ => f (C*n+D)/(n : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ =>
      (f (C*n+D)/((C*n+D : ℕ) : ℝ))*(((C*n+D : ℕ) : ℝ)/(n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (hf.comp (affine_nat_atTop C D hC)).mul (affine_nat_ratio C D)
  apply ht.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  have hN : C*n+D≠0 := by have := Nat.mul_pos hC (Nat.pos_of_ne_zero hn); omega
  have hNR : ((C*n+D : ℕ) : ℝ)≠0 := by exact_mod_cast hN
  field_simp

end KroneckerSublinearAffine
end

/- Original module: KroneckerAffineBinomialLimit -/
section
/-! Exponential rate of binomial coefficients with any fixed affine upper argument. -/
set_option autoImplicit false
namespace KroneckerAffineBinomialLimit
open Filter KroneckerLogFactorialRemainder KroneckerLogFactorialError
open KroneckerSublinearAffine KroneckerAffineNaturalLimits KroneckerAffineBinomialComplement
open KroneckerNormalizedBinomialIdentity
open scoped Topology

theorem affine_binomial_limit (C D : ℕ) (hC : 2 ≤ C) :
    Tendsto (fun n : ℕ => Real.log ((C*n+D).choose n : ℝ)/(n : ℝ)) atTop
      (𝓝 ((C : ℝ)*Real.log (C : ℝ)-((C-1 : ℕ) : ℝ)*Real.log ((C-1 : ℕ) : ℝ))) := by
  have hCp : 0 < C := by omega
  have hCm : 0 < C-1 := by omega
  have hR := affine_nat_ratio C D
  have hS := affine_nat_ratio (C-1) D
  have hlogR := (Real.continuousAt_log (by positivity : (C : ℝ)≠0)).tendsto.comp hR
  have hlogS := (Real.continuousAt_log (by positivity : ((C-1 : ℕ) : ℝ)≠0)).tendsto.comp hS
  have heR := sublinear_affine remainder factorial_remainder_sublinear C D hCp
  have heS := sublinear_affine remainder factorial_remainder_sublinear (C-1) D hCm
  have ht := ((hR.mul hlogR).sub (hS.mul hlogS)).add
    ((heR.sub factorial_remainder_sublinear).sub heS)
  simp only [sub_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hi := normalized_binomial_identity (C*n+D) n hn (affine_binomial_strict C D n hC hn)
  rw [affine_binomial_complement C D n (by omega),sub_div,sub_div] at hi
  exact hi.symm

end KroneckerAffineBinomialLimit
end

/- Original module: KroneckerLogAffineSublinear -/
section
/-! Every fixed positive affine polynomial factor has zero normalized logarithmic cost. -/
set_option autoImplicit false
namespace KroneckerLogAffineSublinear
open Filter KroneckerSublinearAffine
open scoped Topology

theorem log_affine_sublinear (C D : ℕ) (hC : 0 < C) :
    Tendsto (fun n : ℕ => Real.log ((C*n+D : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
  sublinear_affine (fun n => Real.log (n : ℝ))
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop) C D hC

end KroneckerLogAffineSublinear
end

/- Original module: KroneckerAdjacentLogLimit -/
section
/-! The numerical adjacent-dimension formula has exactly the stated central rate. -/
set_option autoImplicit false
namespace KroneckerAdjacentLogLimit
open Filter KroneckerAdjacentParameters KroneckerAdjacentFormulaValue KroneckerAdjacentLogIdentity
open KroneckerAffineBinomialLimit KroneckerLogAffineSublinear
open scoped Topology

theorem adjacent_log_limit (m : ℕ) (hm : 3 ≤ m) :
    Tendsto (fun a : ℕ => Real.log (adjacentValue m a)/(a : ℝ)) atTop (𝓝 (centralValue m)) := by
  have hc : Tendsto (fun a : ℕ => Real.log (m : ℝ)/(a : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun a : ℕ => Real.log ((a+1 : ℕ) : ℝ)/(a : ℝ)) atTop (𝓝 0) := by
    simpa using log_affine_sublinear 1 1 (by omega)
  have h2 := log_affine_sublinear (m-1) m (adjacent_parameter_bounds m hm).2
  have hb := affine_binomial_limit (binomialSlope m) (binomialOffset m)
    (adjacent_parameter_bounds m hm).1
  have ht := ((hc.sub h1).sub h2).add hb
  rw [adjacent_parameter_difference m hm] at ht
  simp only [sub_self,zero_add] at ht
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun a => by
    dsimp only
    rw [adjacent_log_identity m a hm,add_div,sub_div,sub_div])

end KroneckerAdjacentLogLimit
end
end

