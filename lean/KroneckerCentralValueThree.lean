import KroneckerAdjacentLogLimit

/- Original module: KroneckerCentralValueDictionary -/
section
set_option autoImplicit false
namespace KroneckerCentralValueDictionary
open KroneckerAdjacentParameters KroneckerAdjacentFormulaValue


theorem central_value_log_ratio (m : ℕ) (hm : 3 ≤ m) :
    centralValue m = Real.log (binomialSlope m : ℝ)+
      ((m*(m-2) : ℕ) : ℝ)*Real.log ((binomialSlope m : ℝ)/((m*(m-2) : ℕ) : ℝ)) := by
  have hA := (adjacent_parameter_bounds m hm).1
  have hB : 0 < m*(m-2) := Nat.mul_pos (by omega) (by omega)
  have hAB : binomialSlope m=m*(m-2)+1 := by
    have := adjacent_parameter_difference m hm
    omega
  have hABR : (binomialSlope m : ℝ)=((m*(m-2) : ℕ) : ℝ)+1 := by exact_mod_cast hAB
  rw [Real.log_div (by exact_mod_cast (show binomialSlope m≠0 by omega))
    (by exact_mod_cast (show m*(m-2)≠0 by omega))]
  unfold centralValue
  rw [hABR]
  ring

end KroneckerCentralValueDictionary
end

/- Original module: KroneckerCentralValueThree -/
section
set_option autoImplicit false
namespace KroneckerCentralValueThree
open KroneckerAdjacentFormulaValue KroneckerAdjacentParameters

theorem central_value_three : centralValue 3=Real.log (256/27 : ℝ) := by
  have h4 : (4 : ℝ)^4=256 := by norm_num
  have h3 : (3 : ℝ)^3=27 := by norm_num
  rw [←h4,←h3,Real.log_div (by norm_num) (by norm_num),Real.log_pow,Real.log_pow]
  norm_num [centralValue,binomialSlope]

end KroneckerCentralValueThree
end
