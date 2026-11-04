import Mathlib.Tactic

/-! Exact total-character identities for determinant-one extension endpoints. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFareyWeightIdentity
def weight (a b u w : ℤ) : ℤ := b*u-a*w
theorem left (a b c d u w : ℤ) (h : a*d-c*b=1) :
 a*weight (a+c) (b+d) u w=(a+c)*weight a b u w+u := by
 dsimp [weight]; nlinarith [congrArg (fun z : ℤ => z*u) h]
theorem right (a b c d u w : ℤ) (h : a*d-c*b=1) :
 c*weight (a+c) (b+d) u w=(a+c)*weight c d u w-u := by
 dsimp [weight]; nlinarith [congrArg (fun z : ℤ => z*u) h]
theorem endpoints (a b c d : ℤ) (h : a*d-c*b=1) :
 weight (a+c) (b+d) a b=1 ∧ weight (a+c) (b+d) c d= -1 := by
 dsimp [weight]; constructor <;> nlinarith
end KroneckerFareyWeightIdentity
