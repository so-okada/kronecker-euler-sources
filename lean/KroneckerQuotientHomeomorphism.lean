import Mathlib.Topology.Homeomorph.Lemmas

/-! Descent of a homeomorphism through matching equivalence relations uses
quotient topology in both directions, not an arbitrary topology on orbit sets. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerQuotientHomeomorphism
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (s : Setoid X) (t : Setoid Y) (e : X ≃ₜ Y)
  (h : ∀ x y, s.r x y ↔ t.r (e x) (e y))

def descend : Quotient s ≃ₜ Quotient t where
  toEquiv := Quotient.congr e.toEquiv h
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_quotient_mk'.comp e.continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_quotient_mk'.comp e.symm.continuous


end KroneckerQuotientHomeomorphism
