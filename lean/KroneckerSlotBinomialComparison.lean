import KroneckerFrameIdentity
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Polynomial.Basic
import KroneckerTwoMarkRationalSeries

section

/-! A power-series coefficient depends only on finitely many input coefficients. -/
set_option autoImplicit false
namespace KroneckerSeriesCoefficientAgreement
open PowerSeries
variable {R : Type*} [Semiring R]

def Agree (n : ℕ) (f g : PowerSeries R) : Prop := ∀ k, k ≤ n → coeff k f=coeff k g

theorem agree_add {n : ℕ} {f g F G : PowerSeries R} (hf : Agree n f F) (hg : Agree n g G) :
    Agree n (f+g) (F+G) := by
  intro k hk
  simp only [map_add,hf k hk,hg k hk]

theorem agree_mul {n : ℕ} {f g F G : PowerSeries R} (hf : Agree n f F) (hg : Agree n g G) :
    Agree n (f*g) (F*G) := by
  intro k hk
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hsum := Finset.mem_antidiagonal.mp hx
  rw [hf x.1 (by omega),hg x.2 (by omega)]

theorem agree_pow {n : ℕ} {f F : PowerSeries R} (hf : Agree n f F) (k : ℕ) :
    Agree n (f^k) (F^k) := by
  induction k with
  | zero => intro j _; rfl
  | succ k ih =>
    rw [pow_succ,pow_succ]
    exact agree_mul ih hf

end KroneckerSeriesCoefficientAgreement
end

section

/- Original module: KroneckerSeriesPowerVanishing -/
section
/-! Zero constant term makes the geometric coefficient sum finite in every degree. -/
set_option autoImplicit false
namespace KroneckerSeriesPowerVanishing
open PowerSeries

theorem coefficient_power_vanishes {R : Type*} [CommSemiring R] (H : PowerSeries R)
    (h0 : constantCoeff H=0) (n k : ℕ) (hk : k<n) : coeff k (H^n)=0 := by
  have hdiv : (X : PowerSeries R) ∣ H := X_dvd_iff.mpr h0
  exact (X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hdiv n)) k hk

end KroneckerSeriesPowerVanishing
end

/- Original module: KroneckerFiniteSubstitutionCoefficients -/
section
set_option autoImplicit false
namespace KroneckerFiniteSubstitutionCoefficients
open PowerSeries KroneckerSeriesPowerVanishing KroneckerSeriesCoefficientAgreement
variable {R : Type*} [CommRing R]

/-- Substitution at a zero-constant series is finite in every specified degree. -/
theorem coeff_subst_range (b f : PowerSeries R) (hb : constantCoeff b=0)
    (n N : ℕ) (hn : n≤N) :
    coeff n (subst b f)=∑ k ∈ Finset.range (N+1),coeff k f * coeff n (b^k) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hb)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra h
  have hv := coefficient_power_vanishes b hb k n (by omega)
  exact hk (by simp [hv])

/-- One finite polynomial in the inner series recovers all coefficients through N. -/
theorem subst_agree_finite (b f : PowerSeries R) (hb : constantCoeff b=0) (N : ℕ) :
    Agree N (subst b f) (∑ k ∈ Finset.range (N+1),C (coeff k f)*b^k) := by
  intro n hn
  rw [coeff_subst_range b f hb n N hn]
  simp only [map_sum,coeff_C_mul]

end KroneckerFiniteSubstitutionCoefficients
end

/- Original module: KroneckerUnitParameterInverse -/
section
set_option autoImplicit false
namespace KroneckerUnitParameterInverse
open PowerSeries
variable {R : Type*} [CommRing R]

noncomputable def inverseParameter (φ : PowerSeries R) : PowerSeries R := X*invOfUnit φ 1

theorem inverse_parameter_constant (φ : PowerSeries R) :
    constantCoeff (inverseParameter φ)=0 := by simp [inverseParameter]

theorem inverse_parameter_cancels (φ : PowerSeries R) (hφ : constantCoeff φ=1) :
    inverseParameter φ*φ=X := by
  rw [inverseParameter,mul_assoc,invOfUnit_mul φ 1 hφ,mul_one]

/-- Cancellation with unequal powers retains the exact remaining exponent. -/
theorem inverse_parameter_power_cancel (φ : PowerSeries R) (hφ : constantCoeff φ=1)
    (k m : ℕ) (hkm : k≤m) :
    inverseParameter φ^k*φ^m=X^k*φ^(m-k) := by
  calc
    _ = (inverseParameter φ*φ)^k*φ^(m-k) := by
      rw [mul_pow,mul_assoc,← pow_add,Nat.add_sub_of_le hkm]
    _ = _ := by rw [inverse_parameter_cancels φ hφ]

theorem inverse_parameter_power_divisible (φ : PowerSeries R) (k : ℕ) :
    (X : PowerSeries R)^k ∣ inverseParameter φ^k := by
  exact pow_dvd_pow_of_dvd ⟨invOfUnit φ 1,rfl⟩ k

end KroneckerUnitParameterInverse
end

/- Original module: KroneckerJacobianCoefficient -/
section
set_option autoImplicit false
namespace KroneckerJacobianCoefficient
open PowerSeries KroneckerSeriesCoefficientAgreement

/-- The positive-degree formal change-of-parameter coefficient functional. -/
noncomputable def jacobianCoeff (φ : PowerSeries ℚ) (n : ℕ) (f : PowerSeries ℚ) : ℚ :=
  coeff (n+1) (f*φ^(n+1))-coeff n (f*derivative (R := ℚ) φ*φ^n)

theorem jacobian_coeff_sum {ι : Type*} (φ : PowerSeries ℚ) (n : ℕ)
    (s : Finset ι) (f : ι → PowerSeries ℚ) :
    jacobianCoeff φ n (∑ i ∈ s,f i)=∑ i ∈ s,jacobianCoeff φ n (f i) := by
  simp only [jacobianCoeff,Finset.sum_mul,map_sum,Finset.sum_sub_distrib]

theorem jacobian_coeff_C_mul (φ f : PowerSeries ℚ) (n : ℕ) (c : ℚ) :
    jacobianCoeff φ n (C c*f)=c*jacobianCoeff φ n f := by
  simp only [jacobianCoeff,mul_assoc,coeff_C_mul,mul_sub]

theorem jacobian_coeff_agree (φ f g : PowerSeries ℚ) (n : ℕ) (h : Agree (n+1) f g) :
    jacobianCoeff φ n f=jacobianCoeff φ n g := by
  have h1 := agree_mul h (g:=φ^(n+1)) (G:=φ^(n+1)) (fun _ _ => rfl)
  have h2 := agree_mul (agree_mul h (g:=derivative (R := ℚ) φ) (G:=derivative (R := ℚ) φ)
    (fun _ _ => rfl)) (g:=φ^n) (G:=φ^n) (fun _ _ => rfl)
  exact congrArg₂ (·-·) (h1 (n+1) le_rfl) (h2 n (by omega))

/-- Formal integration by parts, with no analytic convergence assumption. -/
theorem jacobian_coeff_derivative (φ f : PowerSeries ℚ) (n : ℕ) :
    (n+1:ℚ)*jacobianCoeff φ n f=coeff n (derivative (R := ℚ) f*φ^(n+1)) := by
  have hd : derivative (R := ℚ) (f*φ^(n+1))=
      derivative (R := ℚ) f*φ^(n+1)+((n+1 : ℕ)) • (f*derivative (R := ℚ) φ*φ^n) := by
    simp only [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  have hc := congrArg (coeff n) hd
  rw [coeff_derivative] at hc
  simp only [map_add,map_nsmul] at hc
  simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hc
  dsimp only [jacobianCoeff]
  linear_combination hc

end KroneckerJacobianCoefficient
end

/- Original module: KroneckerJacobianPowerOrthogonality -/
section
set_option autoImplicit false
namespace KroneckerJacobianPowerOrthogonality
open PowerSeries KroneckerUnitParameterInverse KroneckerJacobianCoefficient

theorem coeff_power_derivative (φ : PowerSeries ℚ) (m : ℕ) :
    coeff (m+1) (φ^(m+1))=coeff m (φ^m*derivative (R := ℚ) φ) := by
  have hd : derivative (R := ℚ) (φ^(m+1))=((m+1 : ℕ)) • (φ^m*derivative (R := ℚ) φ) := by
    simp only [Derivation.leibniz_pow,Nat.add_sub_cancel,smul_eq_mul,nsmul_eq_mul]
  have h := congrArg (coeff m) hd
  simp only [coeff_derivative,map_nsmul] at h
  simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at h
  have hm : (m+1:ℚ)≠0 := by positivity
  apply mul_left_cancel₀ hm
  linear_combination h

/-- The Jacobian functional is the Kronecker delta on powers of the inverse parameter. -/
theorem jacobian_inverse_power (φ : PowerSeries ℚ) (hφ : constantCoeff φ=1)
    (n k : ℕ) : jacobianCoeff φ n (inverseParameter φ^k)=if k=n+1 then 1 else 0 := by
  have vanish (j : ℕ) (hj : j<k) (p : PowerSeries ℚ) :
      coeff j (inverseParameter φ^k*p)=0 :=
    (X_pow_dvd_iff.mp (dvd_mul_of_dvd_left (inverse_parameter_power_divisible φ k) p)) j hj
  by_cases hk : k≤n
  · have hk1 : k≤n+1 := by omega
    have he : k≠n+1 := by omega
    rw [ite_eq_right he,jacobianCoeff,inverse_parameter_power_cancel φ hφ k (n+1) hk1]
    rw [show inverseParameter φ^k*derivative (R := ℚ) φ*φ^n=
      (inverseParameter φ^k*φ^n)*derivative (R := ℚ) φ by ring]
    rw [inverse_parameter_power_cancel φ hφ k n hk,mul_assoc,coeff_X_pow_mul',coeff_X_pow_mul']
    simp only [ite_eq_left hk1,ite_eq_left hk]
    rw [show n+1-k=(n-k)+1 by omega,coeff_power_derivative]
    exact sub_self _
  · by_cases he : k=n+1
    · subst k
      rw [ite_eq_left rfl,jacobianCoeff,inverse_parameter_power_cancel φ hφ (n+1) (n+1) le_rfl]
      simp only [Nat.sub_self,pow_zero,mul_one]
      rw [show inverseParameter φ^(n+1)*derivative (R := ℚ) φ*φ^n=
        inverseParameter φ^(n+1)*(derivative (R := ℚ) φ*φ^n) by ring,
        vanish n (by omega),coeff_X_pow]
      simp
    · rw [ite_eq_right he,jacobianCoeff,
        vanish (n+1) (by omega),
        show inverseParameter φ^k*derivative (R := ℚ) φ*φ^n=
          inverseParameter φ^k*(derivative (R := ℚ) φ*φ^n) by ring,
        vanish n (by omega),sub_self]

end KroneckerJacobianPowerOrthogonality
end

/- Original module: KroneckerFormalChangeOfVariable -/
section
set_option autoImplicit false
namespace KroneckerFormalChangeOfVariable
open PowerSeries KroneckerUnitParameterInverse KroneckerJacobianCoefficient
open KroneckerJacobianPowerOrthogonality KroneckerFiniteSubstitutionCoefficients

/-- Formal change of variable follows from finite truncation and power orthogonality. -/
theorem coefficient_change_of_variable (φ F : PowerSeries ℚ) (hφ : constantCoeff φ=1)
    (n : ℕ) : jacobianCoeff φ n (subst (inverseParameter φ) F)=coeff (n+1) F := by
  rw [jacobian_coeff_agree φ _ _ n
    (subst_agree_finite (inverseParameter φ) F (inverse_parameter_constant φ) (n+1))]
  rw [jacobian_coeff_sum]
  simp_rw [jacobian_coeff_C_mul,jacobian_inverse_power φ hφ]
  simp

end KroneckerFormalChangeOfVariable
end

/- Original module: KroneckerZeroConstantFixedPoint -/
section
set_option autoImplicit false
namespace KroneckerZeroConstantFixedPoint
open PowerSeries KroneckerSeriesCoefficientAgreement

/-- Multiplication by a zero-constant parameter makes the recursive grammar unique. -/
theorem zero_constant_fixed_point_unique {R : Type*} [Semiring R]
    (U f g : PowerSeries R) (k : ℕ) (hU : constantCoeff U=0)
    (hf : f=U*(1+f)^k) (hg : g=U*(1+g)^k) : f=g := by
  obtain ⟨u,hu⟩ := X_dvd_iff.mpr hU
  have hf' : f=X*(u*(1+f)^k) := hf.trans (by rw [hu,mul_assoc])
  have hg' : g=X*(u*(1+g)^k) := hg.trans (by rw [hu,mul_assoc])
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      conv_lhs => rw [hf']
      conv_rhs => rw [hg']
      simp
    | succ n =>
      conv_lhs => rw [hf']
      conv_rhs => rw [hg']
      rw [coeff_succ_X_mul,coeff_succ_X_mul]
      apply agree_mul (fun _ _ => rfl)
        (agree_pow (agree_add (fun _ _ => rfl) (fun j hj => ih j (by omega))) k) n le_rfl

end KroneckerZeroConstantFixedPoint
end

/- Original module: KroneckerQuarticReversion -/
section
set_option autoImplicit false
namespace KroneckerQuarticReversion
open PowerSeries KroneckerUnitParameterInverse KroneckerZeroConstantFixedPoint
open KroneckerActualBranchLinearization KroneckerActualQuarticCounts KroneckerActualBranchSeries

noncomputable def quarticKernel : PowerSeries ℚ := (1+X)^4
noncomputable def quarticParameter : PowerSeries ℚ := inverseParameter quarticKernel

theorem quartic_kernel_constant : constantCoeff quarticKernel=1 := by simp [quarticKernel]

theorem quartic_parameter_constant : constantCoeff quarticParameter=0 :=
  inverse_parameter_constant _

/-- The actual class-count series, not a binomially defined replacement, reverses the parameter. -/
theorem actual_quartic_reversion : subst quarticParameter branchT=X := by
  have hS := HasSubst.of_constantCoeff_zero' quartic_parameter_constant
  have hq : branchT=X*(1+branchT)^4 := actual_source_quartic 0
  have hs := congrArg (substAlgHom hS) hq
  simp only [map_mul,map_pow,map_add,map_one,substAlgHom_X,coe_substAlgHom] at hs
  apply zero_constant_fixed_point_unique quarticParameter _ X 4 quartic_parameter_constant hs
  exact (inverse_parameter_cancels quarticKernel quartic_kernel_constant).symm

end KroneckerQuarticReversion
end

/- Original module: KroneckerQuarticLagrangeFormula -/
section
set_option autoImplicit false
namespace KroneckerQuarticLagrangeFormula
open PowerSeries KroneckerQuarticReversion KroneckerJacobianCoefficient
open KroneckerFormalChangeOfVariable KroneckerActualBranchLinearization KroneckerActualBranchSeries

/-- The full coefficient substitution formula for an arbitrary outer formal series. -/
theorem actual_quartic_jacobian (F : PowerSeries ℚ) (n : ℕ) :
    coeff (n+1) (subst branchT F)=jacobianCoeff quarticKernel n F := by
  have hT : HasSubst branchT := HasSubst.of_constantCoeff_zero'
    (source_series_constant (fun _ => (1:ℚ)) 0)
  have hS := HasSubst.of_constantCoeff_zero' quartic_parameter_constant
  have h := coefficient_change_of_variable quarticKernel (subst branchT F)
    quartic_kernel_constant n
  rw [show KroneckerUnitParameterInverse.inverseParameter quarticKernel=quarticParameter from rfl,
    subst_comp_subst_apply hT hS,actual_quartic_reversion] at h
  have hx : subst (X : PowerSeries ℚ) F=F := by
    simpa using (map_algebraMap_eq_subst_X (R:=ℚ) (S:=ℚ) F).symm
  rw [hx] at h
  exact h.symm

/-- Lagrange extraction is proved internally from finite coefficients and formal derivatives. -/
theorem actual_quartic_lagrange (F : PowerSeries ℚ) (n : ℕ) :
    (n+1:ℚ)*coeff (n+1) (subst branchT F)=
      coeff n (derivative (R := ℚ) F*(1+X)^(4*(n+1))) := by
  rw [actual_quartic_jacobian,jacobian_coeff_derivative]
  simp only [quarticKernel,pow_mul]

end KroneckerQuarticLagrangeFormula
end

/- Original module: KroneckerQuarticPowerCoefficients -/
section
set_option autoImplicit false
namespace KroneckerQuarticPowerCoefficients
open PowerSeries KroneckerQuarticLagrangeFormula KroneckerActualBranchLinearization
open KroneckerActualBranchSeries

theorem coeff_one_add_X_pow (m n : ℕ) :
    coeff n ((1+(X : PowerSeries ℚ))^m)=(m.choose n : ℚ) := by
  have hp : (1+(X : PowerSeries ℚ))^m=
      (((1+(Polynomial.X : Polynomial ℚ))^m : Polynomial ℚ) : PowerSeries ℚ) := by simp
  rw [hp,Polynomial.coeff_coe,Polynomial.coeff_one_add_X_pow]

/-- All positive powers of the actual quartic source series have Raney coefficients. -/
theorem actual_source_power_coeff (n k : ℕ) :
    (n+k+1:ℚ)*coeff (n+k+1) (branchT^(k+1))=
      (k+1:ℚ)*((4*(n+k+1)).choose n : ℚ) := by
  have hT : HasSubst branchT := HasSubst.of_constantCoeff_zero'
    (source_series_constant (fun _ => (1:ℚ)) 0)
  have h := actual_quartic_lagrange ((X : PowerSeries ℚ)^(k+1)) (n+k)
  rw [←coe_substAlgHom hT,map_pow,substAlgHom_X] at h
  have hd : derivative (R := ℚ) ((X : PowerSeries ℚ)^(k+1))=
      (k+1:ℕ) • ((X : PowerSeries ℚ)^k) := by
    simp only [Derivation.leibniz_pow,Nat.add_sub_cancel,derivative_X,smul_eq_mul,mul_one]
  rw [hd,smul_mul_assoc,map_nsmul,coeff_X_pow_mul,coeff_one_add_X_pow] at h
  simpa only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using h


end KroneckerQuarticPowerCoefficients
end

/- Original module: KroneckerQuarticRationalExtraction -/
section
set_option autoImplicit false
namespace KroneckerQuarticRationalExtraction
open PowerSeries KroneckerQuarticReversion KroneckerJacobianCoefficient
open KroneckerFormalChangeOfVariable

/-- The quartic Jacobian cancels the characteristic response denominator exactly. -/
theorem quartic_jacobian_factor (F : PowerSeries ℚ) (n : ℕ) :
    jacobianCoeff quarticKernel n F=
      coeff (n+1) (F*((1+X)*(1-3*X))*(1+X)^(4*n+2)) := by
  have hd : derivative (R := ℚ) quarticKernel=4*(1+X)^3 := by
    simp only [quarticKernel,Derivation.leibniz_pow,map_add,Derivation.map_one_eq_zero,
      derivative_X,zero_add,smul_eq_mul,nsmul_eq_mul]
    norm_num
  have hp : quarticKernel^(n+1)=(1+(X : PowerSeries ℚ))^(4*n+2)*(1+X)^2 := by
    rw [quarticKernel,←pow_mul,←pow_add]
    congr 1
  have hq : (1+(X : PowerSeries ℚ))^3*quarticKernel^n=(1+X)^(4*n+2)*(1+X) := by
    rw [quarticKernel,←pow_mul,←pow_add,←pow_succ]
    congr 1
    omega
  rw [jacobianCoeff,←coeff_succ_X_mul n (F*derivative (R := ℚ) quarticKernel*quarticKernel^n),
    ←map_sub,hd,hp]
  apply congrArg (coeff (n+1))
  linear_combination -4*X*F*hq

/-- Extract a series once its substituted denominator has been cleared. -/
theorem quartic_cleared_coefficient (F N : PowerSeries ℚ)
    (h : subst quarticParameter F*((1+X)*(1-3*X))=N) (n : ℕ) :
    coeff (n+1) F=coeff (n+1) (N*(1+X)^(4*n+2)) := by
  rw [←coefficient_change_of_variable quarticKernel F quartic_kernel_constant n,
    quartic_jacobian_factor]
  change coeff (n+1) ((subst quarticParameter F*((1+X)*(1-3*X)))*(1+X)^(4*n+2))=_
  rw [h]

end KroneckerQuarticRationalExtraction
end

/- Original module: KroneckerActualPairClosedCounts -/
section
set_option autoImplicit false
namespace KroneckerActualPairClosedCounts
open PowerSeries KroneckerQuarticReversion KroneckerQuarticRationalExtraction
open KroneckerQuarticPowerCoefficients KroneckerTwoMarkRationalSeries KroneckerTwoMarkResponseSystem
open KroneckerActualPairCountSeries KroneckerPairTreeClassCount
attribute [local instance] Classical.propDecidable

theorem substituted_pair_cleared :
    subst quarticParameter sameMark*((1+X)*(1-3*X))=2*X^2 ∧
    subst quarticParameter differentMark*((1+X)*(1-3*X))=X*(1-X) := by
  have hS := HasSubst.of_constantCoeff_zero' quartic_parameter_constant
  constructor
  · have h := congrArg (substAlgHom hS) two_mark_cleared_formulas.1
    simpa only [responseDenominator,map_mul,map_add,map_sub,map_one,map_ofNat,map_pow,
      coe_substAlgHom,actual_quartic_reversion] using h
  · have h := congrArg (substAlgHom hS) two_mark_cleared_formulas.2
    simpa only [responseDenominator,map_mul,map_add,map_sub,map_one,map_ofNat,
      coe_substAlgHom,actual_quartic_reversion] using h

theorem same_mark_closed_coefficient (n : ℕ) :
    coeff (n+2) sameMark=2*((4*n+6).choose n : ℚ) := by
  have h := quartic_cleared_coefficient sameMark _ substituted_pair_cleared.1 (n+1)
  have he : 4*(n+1)+2=4*n+6 := by omega
  rw [he] at h
  rw [show (2 : PowerSeries ℚ)=C (2:ℚ) by rw [map_ofNat],mul_assoc] at h
  change coeff (n+2) sameMark=coeff (n+2) (C (2:ℚ)*(X^2*(1+X)^(4*n+6))) at h
  rw [coeff_C_mul,coeff_X_pow_mul,coeff_one_add_X_pow] at h
  exact h


/-- Ordered distinct equal-color marks have the exact integer binomial count. -/
theorem actual_same_pair_count (n : ℕ) (d : Fin 3) :
    Fintype.card (PairClass (Fin (n+2)) (Fin (2*(n+2)+1)) d d)=2*(4*n+6).choose n := by
  have h := same_mark_closed_coefficient n
  change coeff (n+2) (KroneckerActualBranchLinearization.sourceMark 0 0)=_ at h
  rw [←source_mark_diagonal_uniform d 0,source_mark_pair_count] at h
  exact_mod_cast h


end KroneckerActualPairClosedCounts
end

/- Original module: KroneckerActualSourceClosedCounts -/
section
set_option autoImplicit false
namespace KroneckerActualSourceClosedCounts
open PowerSeries KroneckerQuarticPowerCoefficients KroneckerActualBranchLinearization
open KroneckerActualQuarticCounts KroneckerActualBranchSeries KroneckerFiniteBranchClasses
open KroneckerGradedMarkedBranchCounts KroneckerMarkedTreeClassCount
attribute [local instance] Classical.propDecidable

/-- The actual branch coefficient is the Fuss-Catalan number. -/
theorem actual_source_closed_coefficient (n : ℕ) :
    coeff (n+1) branchT=((4*(n+1)).choose (n+1) : ℚ)/(3*(n+1)+1) := by
  have h := actual_source_power_coeff n 0
  simp only [Nat.add_zero,zero_add,pow_one] at h
  have hc := Nat.choose_succ_right_eq (4*(n+1)) n
  rw [show 4*(n+1)-n=3*(n+1)+1 by omega] at hc
  have hcQ : ((4*(n+1)).choose (n+1) : ℚ)*(n+1)=
      ((4*(n+1)).choose n : ℚ)*(3*(n+1)+1) := by exact_mod_cast hc
  apply (eq_div_iff (by positivity : (3*((n:ℚ)+1)+1)≠0)).mpr
  have hn : (n+1:ℚ)≠0 := by positivity
  apply mul_left_cancel₀ hn
  linear_combination (3*((n:ℚ)+1)+1)*h-hcQ

theorem actual_source_closed_count (n : ℕ) (d : Fin 3) :
    (Fintype.card (SourceDegreeClass (n+1) d) : ℚ)=
      ((4*(n+1)).choose (n+1) : ℚ)/(3*(n+1)+1) := by
  rw [←source_series_counts d (n+1),source_series_at_one_uniform d 0]
  exact actual_source_closed_coefficient n

/-- Single marked saturated-tree classes have the manuscript's P_j count. -/
theorem actual_single_marked_count (j : ℕ) (d : Fin 3) :
    (Fintype.card (MarkedClass (Fin (j+1)) (Fin (2*(j+1)+1)) d) : ℚ)=
      ((4*j+4).choose (j+1) : ℚ)/(3*j+4) := by
  rw [←source_degree_marked_count]
  convert actual_source_closed_count j d using 1
  congr 1
  ring

end KroneckerActualSourceClosedCounts
end

/- Original module: KroneckerSlotBinomialComparison -/
section
set_option autoImplicit false
namespace KroneckerSlotBinomialComparison

/-- The shifted binomial in the pair count has the exact rational prefactor. -/
theorem shifted_pair_binomial_identity (n : ℕ) :
    (3*n+6:ℝ)*(3*n+5)*(3*n+4)*((4*n+6).choose n : ℝ)=
      (4*n+6)*(4*n+5)*(n+1)*((4*n+4).choose (n+1) : ℝ) := by
  have h0 := Nat.choose_succ_right_eq (4*n+4) n
  have h1 := Nat.choose_mul_succ_eq (4*n+4) n
  have h2 := Nat.choose_mul_succ_eq (4*n+5) n
  rw [show 4*n+4-n=3*n+4 by omega] at h0
  rw [show 4*n+4+1=4*n+5 by omega,show 4*n+5-n=3*n+5 by omega] at h1
  rw [show 4*n+5+1=4*n+6 by omega,show 4*n+6-n=3*n+6 by omega] at h2
  have a : ((4*n+4).choose (n+1) : ℝ)*(n+1)=((4*n+4).choose n : ℝ)*(3*n+4) := by exact_mod_cast h0
  have b : ((4*n+4).choose n : ℝ)*(4*n+5)=((4*n+5).choose n : ℝ)*(3*n+5) := by exact_mod_cast h1
  have c : ((4*n+5).choose n : ℝ)*(4*n+6)=((4*n+6).choose n : ℝ)*(3*n+6) := by exact_mod_cast h2
  linear_combination -(4*(n:ℝ)+6)*(4*n+5)*a-(4*n+6)*(3*n+4)*b-(3*n+5)*(3*n+4)*c

/-- A uniform positive comparison, including the smallest admissible block. -/
theorem shifted_pair_binomial_lower (n : ℕ) :
    ((4*n+4).choose (n+1) : ℝ)≤4*((4*n+6).choose n : ℝ) := by
  have h := shifted_pair_binomial_identity n
  have hd : 0<(3*n+6:ℝ)*(3*n+5)*(3*n+4) := by positivity
  have hp : (3*n+6:ℝ)*(3*n+5)*(3*n+4)≤4*((4*n+6)*(4*n+5)*(n+1)) := by
    nlinarith [sq_nonneg (n:ℝ),mul_nonneg (sq_nonneg (n:ℝ)) (Nat.cast_nonneg n)]
  have hc : 0≤((4*n+4).choose (n+1) : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right hp hc
  nlinarith

theorem single_mark_binomial_comparison (j : ℕ) :
    (4*j).choose j≤(4*j+4).choose (j+1) := by
  have h : (4*j).choose j≤(4*j+1).choose (j+1) := by
    rw [Nat.choose_succ_succ']
    omega
  exact h.trans (Nat.choose_le_choose _ (by omega))

end KroneckerSlotBinomialComparison
end
end

