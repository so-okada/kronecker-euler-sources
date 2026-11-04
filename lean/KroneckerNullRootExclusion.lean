import KroneckerRealRootRealization

/-! For m≥3 the integral Tits form has no nonzero isotropic vector in the
nonnegative quadrant. This rules out exact endpoint slopes in the dimension domain. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerNullRootExclusion

theorem sorted_zero (m : ℕ) (hm : 3≤m) (a b : ℕ) (hab : a≤b)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=0) : a=0 ∧ b=0 := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases ha : a=0
    · subst a
      have hb : (b : ℤ)=0 := eq_zero_of_pow_eq_zero (by simpa using ht : (b : ℤ)^2=0)
      exact ⟨rfl,by exact_mod_cast hb⟩
    · have hap : 0<a := by omega
      have ht' : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b≤1 := by omega
      have hc := KroneckerRealRootDescent.decrease m a b hm hap hab ht' (by omega)
      have hbound := KroneckerRealRootDescent.bound m a b hap ht'
      have hq : ((m*a-b : ℕ) : ℤ)^2+(a : ℤ)^2-(m : ℤ)*(m*a-b : ℕ)*a=0 := by
        rw [Nat.cast_sub hbound,Nat.cast_mul]
        nlinarith
      have hz := ih (m*a-b) hc a (Nat.le_of_lt hc) hq
      exact False.elim (ha hz.2)

theorem zero (m : ℕ) (hm : 3≤m) (a b : ℕ)
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=0) : a=0 ∧ b=0 := by
  rcases le_total a b with hab | hba
  · exact sorted_zero m hm a b hab ht
  · exact (sorted_zero m hm b a hba (by nlinarith)).symm
end KroneckerNullRootExclusion
