import KroneckerCanonicalTitsOneEuler

/-! A dimension pair of Tits value one is primitive for every arrow count.
This supplies the missing coprimality condition for actual real-root moduli. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTitsOnePrimitive

theorem coprime (m a b : ℕ) (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1) :
    Nat.Coprime a b := by
  let d := Nat.gcd a b
  have ha : (d : ℤ)∣(a : ℤ) := by exact_mod_cast Nat.gcd_dvd_left a b
  have hb : (d : ℤ)∣(b : ℤ) := by exact_mod_cast Nat.gcd_dvd_right a b
  have hd : (d : ℤ)∣(a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b :=
    dvd_sub (dvd_add (dvd_pow ha (by omega)) (dvd_pow hb (by omega))) (dvd_mul_of_dvd_right hb _)
  rw [ht] at hd
  have hdn : d∣1 := by exact_mod_cast hd
  exact Nat.dvd_one.mp hdn
end KroneckerTitsOnePrimitive
