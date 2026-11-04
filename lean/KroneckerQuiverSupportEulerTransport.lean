import KroneckerColoredCoverStableUniqueness

/-! Reindex actual induced-support arrows and preserve the self Euler form.
No moduli-space or Euler-characteristic identity is involved. -/
set_option autoImplicit false
namespace KroneckerQuiverSupportEulerTransport
open KroneckerAbelianCover KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackStability KroneckerColoredCoverStableUniqueness
open scoped BigOperators

noncomputable local instance supportFintype {V : Type} [DecidableEq V]
    (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

def reindexSupportArrows {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) :
    SupportArrow Q.source Q.target (pullDimension f d) ≃ SupportArrow R.source R.target d where
  toFun a := ⟨f.arrowEquiv a.val, by
    constructor
    · rw [f.map_source]
      simpa only [Finsupp.mem_support_iff, pullDimension_apply] using a.property.1
    · rw [f.map_target]
      simpa only [Finsupp.mem_support_iff, pullDimension_apply] using a.property.2⟩
  invFun a := ⟨f.arrowEquiv.symm a.val, by
    constructor
    · simp only [Finsupp.mem_support_iff, pullDimension_apply]
      rw [← f.map_source, Equiv.apply_symm_apply]
      exact Finsupp.mem_support_iff.mp a.property.1
    · simp only [Finsupp.mem_support_iff, pullDimension_apply]
      rw [← f.map_target, Equiv.apply_symm_apply]
      exact Finsupp.mem_support_iff.mp a.property.2⟩
  left_inv a := Subtype.ext (f.arrowEquiv.symm_apply_apply a.val)
  right_inv a := Subtype.ext (f.arrowEquiv.apply_symm_apply a.val)

/-- The full induced-support quivers correspond, including all arrows with
zero representation maps. -/
def supportQuiverIso {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) :
    TypedQuiverIso (supportQuiver Q (pullDimension f d)) (supportQuiver R d) where
  vertexEquiv := pullSupportEquiv f d
  arrowEquiv := reindexSupportArrows f d
  map_source a := Subtype.ext (f.map_source a.val)
  map_target a := Subtype.ext (f.map_target a.val)

theorem pull_vertex_square_sum {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) :
    (∑ v : SupportVertex (pullDimension f d),
      (pullDimension f d v.val : ℤ) * pullDimension f d v.val) =
      ∑ v : SupportVertex d, (d v.val : ℤ) * d v.val :=
  (pullSupportEquiv f d).sum_comp (fun v => (d v.val : ℤ) * d v.val)

theorem pull_arrow_product_sum {Q R : TypedQuiver} [DecidableEq Q.V] [DecidableEq R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ)
    [Fintype (SupportArrow Q.source Q.target (pullDimension f d))]
    [Fintype (SupportArrow R.source R.target d)] :
    (∑ a : SupportArrow Q.source Q.target (pullDimension f d),
      (pullDimension f d (Q.source a.val) : ℤ) * pullDimension f d (Q.target a.val)) =
      ∑ a : SupportArrow R.source R.target d,
        (d (R.source a.val) : ℤ) * d (R.target a.val) := by
  have h := (reindexSupportArrows f d).sum_comp
    (fun a => (d (R.source a.val) : ℤ) * d (R.target a.val))
  simpa [reindexSupportArrows, f.map_source, f.map_target, pullDimension_apply] using h

open KroneckerReducedColorWords KroneckerCoverDeckTranslations
local instance : DecidableEq coloredCoverQuiver.V := inferInstanceAs (DecidableEq Word)

theorem deck_cover_euler (g : Deck) (d : Word →₀ ℕ) :
    coverEuler (deckPullDimension g d) = coverEuler d := by
  let : Fintype (SupportArrow coloredCoverQuiver.source coloredCoverQuiver.target
      (pullDimension (deckQuiverAuto g) d)) := coverSupportArrowFintype (deckPullDimension g d)
  unfold coverEuler deckPullDimension
  exact congrArg₂ (fun x y : ℤ => x - y)
    (pull_vertex_square_sum (deckQuiverAuto g) d)
    (pull_arrow_product_sum (deckQuiverAuto g) d)

end KroneckerQuiverSupportEulerTransport
