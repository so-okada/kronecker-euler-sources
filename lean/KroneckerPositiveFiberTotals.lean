import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

/-! For nonnegative integral dimensions, collapsing vertices cannot hide a
strict increase. This supplies the zero/full cases in source-cover indivisibility. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPositiveFiberTotals
attribute [local instance] Classical.decEq Classical.propDecidable

variable {V W : Type} (f : V → W)

theorem comparable_equal (e d : V →₀ ℕ) (hle : e≤d)
    (he : e.mapDomain f=d.mapDomain f) : e=d := by
  ext v
  apply Nat.le_antisymm (hle v)
  by_contra hn
  have hv : e v<d v := by omega
  have hb : e+Finsupp.single v 1≤d := by
    intro w
    by_cases hw : w=v
    · subst w
      simpa using hv
    · simpa [Finsupp.single_apply,hw,eq_comm] using hle w
  have ht := (Finsupp.mapDomain_mono (f:=f) hb) (f v)
  rw [Finsupp.mapDomain_add,Finsupp.mapDomain_single,Finsupp.add_apply,
    Finsupp.single_eq_same,he] at ht
  omega

theorem zero_iff (d : V →₀ ℕ) : d.mapDomain f=0 ↔ d=0 := by
  constructor
  · intro h
    exact (comparable_equal f 0 d (by intro v;exact Nat.zero_le _) (by simpa using h.symm)).symm
  · rintro rfl
    exact Finsupp.mapDomain_zero

end KroneckerPositiveFiberTotals
