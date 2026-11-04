import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace KroneckerCoprimeKingNumerator

/-- With coprime totals, equality of slopes inside the dimension rectangle
occurs only at its zero and full corners. Zero source/sink totals are included. -/
theorem equality_zero_or_full {a b u v : ℕ} (hc : a.Coprime b)
    (hu : u ≤ a) (hv : v ≤ b) (he : b * u = a * v) :
    (u = 0 ∧ v = 0) ∨ (u = a ∧ v = b) := by
  by_cases ha : a = 0
  · have hb : b = 1 := by simpa [ha] using hc
    have hu0 : u = 0 := by omega
    by_cases hv0 : v = 0
    · exact Or.inl ⟨hu0,hv0⟩
    · exact Or.inr ⟨by omega,by omega⟩
  · have hap : 0 < a := Nat.pos_of_ne_zero ha
    have hadiv : a ∣ u := hc.dvd_of_dvd_mul_left (by rw [he]; exact dvd_mul_right a v)
    by_cases hu0 : u = 0
    · have hv0 : v = 0 := by
        rw [hu0, mul_zero] at he
        exact (Nat.mul_eq_zero.mp he.symm).resolve_left ha
      exact Or.inl ⟨hu0,hv0⟩
    · have hau : a ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hu0) hadiv
      have hua : u = a := Nat.le_antisymm hu hau
      right
      refine ⟨hua, ?_⟩
      subst u
      apply Nat.eq_of_mul_eq_mul_left hap
      simpa [Nat.mul_comm] using he.symm



end KroneckerCoprimeKingNumerator
