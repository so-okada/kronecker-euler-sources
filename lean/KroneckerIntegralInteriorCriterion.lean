import KroneckerIntegralEndpointExclusion
import KroneckerExteriorEntropyZero

/-! For integral positive-source dimensions, the strict root interval is
exactly the negative Tits region. The boundary is excluded internally. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerIntegralInteriorCriterion
open KroneckerEndpointRoots

theorem criterion (m : ℕ) (hm : 3≤m) (a b : ℕ) (ha : 0<a) :
    (b : ℝ)/a∈Set.Ioo (lowerRoot m) (upperRoot m) ↔
      (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b<0 := by
  have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
  have ha' : (0 : ℝ)<a := by exact_mod_cast ha
  constructor
  · intro h
    have hf := quadratic_factorization (m:=(m : ℝ)) (r:=(b : ℝ)/a) hm'.le
    have hp := mul_pos (sub_pos.mpr h.2) (sub_pos.mpr h.1)
    have hq : 1+((b : ℝ)/a)^2-(m : ℝ)*((b : ℝ)/a)<0 := by nlinarith
    have hx := mul_neg_of_pos_of_neg (sq_pos_of_pos ha') hq
    have he : (a : ℝ)^2*(1+((b : ℝ)/a)^2-(m : ℝ)*((b : ℝ)/a))=
      (a : ℝ)^2+(b : ℝ)^2-(m : ℝ)*a*b := by field_simp <;> ring
    rw [he] at hx
    exact_mod_cast hx
  · intro hq
    have hi : (b : ℝ)/a∈Set.Icc (lowerRoot m) (upperRoot m) := by
      by_contra he
      have hp := KroneckerExteriorTitsSign.tits_positive m a b hm ha he
      omega
    have hn := KroneckerIntegralEndpointExclusion.endpoints m hm a b ha
    exact ⟨lt_of_le_of_ne hi.1 hn.1.symm,lt_of_le_of_ne hi.2 hn.2⟩
end KroneckerIntegralInteriorCriterion
