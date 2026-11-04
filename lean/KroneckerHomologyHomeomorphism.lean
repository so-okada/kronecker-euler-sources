import KroneckerOrdinarySingularEuler

/-! Homeomorphic spaces have equivalent homological finiteness hypotheses and
identical ordinary rational singular Euler characteristics. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerHomologyHomeomorphism
open KroneckerOrdinarySingularEuler
variable {X Y : TopCat.{0}} (e : X ≃ₜ Y)
include e

theorem admissible_transfer (h : Admissible Y) : Admissible X := by
  constructor
  · intro n
    let := h.1 n
    exact FiniteDimensional.of_injective
      (homologyIso (TopCat.isoOfHomeo e) n).toLinearEquiv.toLinearMap
      (homologyIso (TopCat.isoOfHomeo e) n).toLinearEquiv.injective
  · have hb : betti X=betti Y := funext (betti_iso (TopCat.isoOfHomeo e))
    rw [hb]
    exact h.2

theorem admissible_iff : Admissible X ↔ Admissible Y :=
  ⟨admissible_transfer e.symm,admissible_transfer e⟩

theorem euler_eq (hx : Admissible X) (hy : Admissible Y) :
    ordinaryEuler X hx=ordinaryEuler Y hy :=
  ordinaryEuler_iso (TopCat.isoOfHomeo e) hx hy

end KroneckerHomologyHomeomorphism
