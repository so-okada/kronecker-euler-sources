import KroneckerCanonicalClosedApproximableFromFundamental

/-! Existence of a strictly positive actual joint entropy limit is invariant
under source/sink exchange, with nonzero normalization checked explicitly. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPositiveLimitExchange
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
def PositiveLimit (m : ℕ) (r : ℝ) : Prop :=
  ∃ L : ℝ,0<L ∧ JointLimit (height (M:=family H) (m:=m)) slope value r L
theorem forward (m : ℕ) (r : ℝ) (hr : 0<r) (h : PositiveLimit H m r) : PositiveLimit H m r⁻¹ := by
  obtain ⟨L,hL,hl⟩ := h
  exact ⟨L/r,div_pos hL hr,KroneckerExchangeJointLimit.joint_exchange H hr hl⟩
theorem iff (m : ℕ) (r : ℝ) (hr : 0<r) : PositiveLimit H m r ↔ PositiveLimit H m r⁻¹ := by
  refine ⟨forward H m r hr,?_⟩
  intro h
  simpa only [inv_inv] using forward H m r⁻¹ (inv_pos.mpr hr) h
end KroneckerPositiveLimitExchange
