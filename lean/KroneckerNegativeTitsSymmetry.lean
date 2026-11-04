import KroneckerReflectionInteriorDimensions

/-! Negative Tits dimensions are positive in both coordinates and remain
negative under exchange; these arithmetic facts do not assume moduli nonemptiness. -/
set_option autoImplicit false
namespace KroneckerNegativeTitsSymmetry
def tits (m a b : ℕ) : ℤ := (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b
theorem exchange (m a b : ℕ) : tits m b a=tits m a b := by unfold tits;ring
theorem positive (m a b : ℕ) (h : tits m a b<0) : 0<a ∧ 0<b := by
  constructor
  · by_contra ha
    have he : a=0 := by omega
    subst a;simp [tits] at h;nlinarith [sq_nonneg (b : ℤ)]
  · by_contra hb
    have he : b=0 := by omega
    subst b;simp [tits] at h;nlinarith [sq_nonneg (a : ℤ)]
theorem reflection (m a b : ℕ) (h : tits m a b<0) :
    0<m*a-b ∧ tits m (m*a-b) a=tits m a b := by
  have hb := KroneckerReflectionInteriorDimensions.positive m a b (positive m a b h).1 h
  exact ⟨Nat.sub_pos_of_lt hb,KroneckerReflectionInteriorDimensions.tits_preserved m a b hb.le⟩
end KroneckerNegativeTitsSymmetry
