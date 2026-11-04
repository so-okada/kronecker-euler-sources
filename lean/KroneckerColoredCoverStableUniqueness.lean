import KroneckerFiniteSupportIsomorphisms
import KroneckerQuiverPullbackStability

/-! The oriented three-color cover has finitely many induced-support arrows.
The positive Euler uniqueness theorem therefore applies without any finiteness
assumption on its infinite vertex or arrow set. -/
set_option autoImplicit false
namespace KroneckerColoredCoverStableUniqueness
open KroneckerFiniteQuiverHom KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportStability KroneckerFiniteSupportIsomorphisms
open KroneckerReducedColorWords
open scoped BigOperators

noncomputable local instance supportFintype (d : Word →₀ ℕ) :
    Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

abbrev CoverSupportArrow (d : Word →₀ ℕ) :=
  SupportArrow coloredCoverQuiver.source coloredCoverQuiver.target d

/-- The color and the supported source recover the actual oriented arrow. -/
def colorSource (d : Word →₀ ℕ) (a : CoverSupportArrow d) :
    Color × SupportVertex d := (a.val.1, ⟨a.val.2.val, a.property.1⟩)

theorem colorSource_injective (d : Word →₀ ℕ) : Function.Injective (colorSource d) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p : Color × SupportVertex d => p.1) h
  · apply Subtype.ext
    exact congrArg (fun p : Color × SupportVertex d => p.2.val) h

noncomputable instance coverSupportArrowFintype (d : Word →₀ ℕ) :
    Fintype (CoverSupportArrow d) := Fintype.ofInjective (colorSource d) (colorSource_injective d)

theorem support_arrow_card_le (d : Word →₀ ℕ) :
    Fintype.card (CoverSupportArrow d) ≤ 3 * d.support.card := by
  have h := Fintype.card_le_of_injective (colorSource d) (colorSource_injective d)
  simpa [Fintype.card_prod, Color, SupportVertex] using h

/-- The integer self Euler form of the actual induced support quiver. -/
noncomputable def coverEuler (d : Word →₀ ℕ) : ℤ :=
  (∑ v : SupportVertex d, (d v.val : ℤ) * d v.val) -
    ∑ a : CoverSupportArrow d,
      (d (coloredCoverQuiver.source a.val) : ℤ) * d (coloredCoverQuiver.target a.val)

theorem positive_cover_euler_iso (d : Word →₀ ℕ) (θ : Word → ℤ)
    (R S : Representation coloredCoverQuiver.source coloredCoverQuiver.target
      (fun w => d w))
    (hR : FiniteSupportStable d θ R) (hS : FiniteSupportStable d θ S)
    (he : 0 < coverEuler d) : Nonempty (Iso R S) := by
  let : DecidableEq coloredCoverQuiver.V := inferInstanceAs (DecidableEq Word)
  apply positive_support_euler_iso coloredCoverQuiver d θ R S hR hS
  have hi : (∑ a : CoverSupportArrow d,
      (d (coloredCoverQuiver.source a.val) : ℤ) * d (coloredCoverQuiver.target a.val)) <
      ∑ v : SupportVertex d, (d v.val : ℤ) * d v.val := by
    simpa only [coverEuler, sub_pos] using he
  exact_mod_cast hi

/-- Tits form one gives uniqueness of the stable class on the infinite cover.
This is an isomorphism statement, not a geometric moduli/Euler computation. -/
theorem tits_one_cover_iso (d : Word →₀ ℕ) (θ : Word → ℤ)
    (R S : Representation coloredCoverQuiver.source coloredCoverQuiver.target
      (fun w => d w))
    (hR : FiniteSupportStable d θ R) (hS : FiniteSupportStable d θ S)
    (he : coverEuler d = 1) : Nonempty (Iso R S) := by
  apply positive_cover_euler_iso d θ R S hR hS
  rw [he]
  norm_num

end KroneckerColoredCoverStableUniqueness
