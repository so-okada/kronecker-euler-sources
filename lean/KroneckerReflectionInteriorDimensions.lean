import KroneckerIntegralInteriorCriterion

/-! Interior integral dimensions remain positive and interior after global
sink reflection, with the exact Tits value preserved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionInteriorDimensions
open KroneckerEndpointRoots

theorem tits_preserved (m a b : ℕ) (hb : b≤m*a) :
    ((m*a-b : ℕ) : ℤ)^2+(a : ℤ)^2-(m : ℤ)*(m*a-b : ℕ)*a=
      (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b := by
  rw [Nat.cast_sub hb,Nat.cast_mul]
  ring

theorem positive (m a b : ℕ) (ha : 0<a)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b<0) : b<m*a := by
  have hb := KroneckerRealRootDescent.bound m a b ha (by omega)
  by_contra hh
  have he : b=m*a := by omega
  subst b
  push_cast at ht
  nlinarith [sq_nonneg (a : ℤ)]

theorem interior (m : ℕ) (hm : 3≤m) (a b : ℕ) (ha : 0<a)
    (hi : (b : ℝ)/a∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    0<m*a-b ∧ (a : ℝ)/(m*a-b : ℕ)∈Set.Ioo (lowerRoot m) (upperRoot m) := by
  have ht := (KroneckerIntegralInteriorCriterion.criterion m hm a b ha).mp hi
  have hb := positive m a b ha ht
  have hc : 0<m*a-b := Nat.sub_pos_of_lt hb
  exact ⟨hc,(KroneckerIntegralInteriorCriterion.criterion m hm (m*a-b) a hc).mpr
    (by rw [tits_preserved m a b hb.le];exact ht)⟩
end KroneckerReflectionInteriorDimensions
