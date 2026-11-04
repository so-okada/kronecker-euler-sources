import KroneckerAbelianIteratedGirth

set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

/-- Below the actual girth bound, every reduced closed walk is empty. -/
theorem reduced_closed_empty_below_girth {g : ℕ} (hg : ReducedGirthBound s t g)
    {u : V} (p : LabeledWalk s t u u) (hr : Reduced p)
    (hshort : (labels p).length < g) : labels p = [] := by
  apply List.length_eq_zero_iff.mp
  by_contra hn
  have hp : 0 < (labels p).length := Nat.pos_of_ne_zero hn
  have hb := hg u p hr hp
  omega


/-- A sufficiently small FINITE ARROW SUPPORT has no nonempty reduced closed
walk of ANY length. The shortest witness bounds length by support-cardinality+1. -/
theorem finite_support_no_reduced_closed {g : ℕ} (hg : ReducedGirthBound s t g)
    (F : Finset A) (hF : F.card + 1 < g) {u : V}
    (p : LabeledWalk s t u u) (hr : Reduced p) (hs : arrowSupport p ⊆ F) : labels p = [] := by
  apply List.length_eq_zero_iff.mp
  by_contra hn
  have hp : 0 < (labels p).length := Nat.pos_of_ne_zero hn
  obtain ⟨w,q,hq,hpos,_hsub,hlen⟩ := closed_support_bounded_witness p hr hp
  have hb := hg w q hq hpos
  have hc := Finset.card_le_card hs
  omega

end LabeledWalk
namespace TypedQuiver
open LabeledWalk




end TypedQuiver
end KroneckerAbelianCover
