import KroneckerDirectSumAbelianCover
import KroneckerLabeledWalkTransport

/-! Girth growth and finite-support forest bounds for the iterated DIRECT-SUM
abelian covers. This transfers the checked walk estimates through an injective
arrow inclusion at every stage, with no product/direct-sum identification. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumIteratedGirth
open KroneckerAbelianCover LabeledWalk KroneckerDirectSumAbelianCover
attribute [local instance] Classical.decEq Classical.propDecidable

theorem direct_girth_of_product (Q : TypedQuiver) (g : ℕ)
    (h : ReducedGirthBound Q.abelian.source Q.abelian.target g) :
    ReducedGirthBound (directCover Q).source (directCover Q).target g := by
  intro u p hr hp
  let q := transport (vertexInclusion Q) (arrowInclusion Q) (inclusion_source Q) (inclusion_target Q) p
  have hq : Reduced q := (transport_reduced_iff _ _ (arrowInclusion_injective Q) _ _ p).2 hr
  have hl : (labels q).length = (labels p).length := by rw [transport_labels,List.length_map]
  have hh := h (vertexInclusion Q u) q hq (by rwa [hl])
  rwa [hl] at hh

theorem direct_girth_growth (Q : TypedQuiver) (g : ℕ)
    (h : ReducedGirthBound Q.source Q.target g) :
    ReducedGirthBound (directCover Q).source (directCover Q).target (2*g-2) :=
  direct_girth_of_product Q _ (abelian_girth_bound g h)

def iterate (Q : TypedQuiver) : ℕ → TypedQuiver
  | 0 => Q
  | n+1 => directCover (iterate Q n)

theorem iterate_girth (Q : TypedQuiver) (n : ℕ) :
    ReducedGirthBound (iterate Q (n+1)).source (iterate Q (n+1)).target (2^n+2) := by
  induction n with
  | zero => exact direct_girth_of_product Q 3 first_abelian_girth
  | succ n ih =>
    have h := direct_girth_growth (iterate Q (n+1)) (2^n+2) ih
    have he : 2*(2^n+2)-2 = 2^(n+1)+2 := by rw [Nat.pow_succ]; omega
    rwa [he] at h


end KroneckerDirectSumIteratedGirth
