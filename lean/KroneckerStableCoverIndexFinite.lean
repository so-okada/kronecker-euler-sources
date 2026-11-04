import KroneckerConnectedDeckNormalization
import KroneckerStablePositiveSupportConnected

/- Original module: KroneckerFiniteConnectedDeckClasses -/
section
set_option autoImplicit false
namespace KroneckerFiniteConnectedDeckClasses
open KroneckerReducedColorWords KroneckerDeckDimensionClasses
open KroneckerCoverSupportRadius KroneckerConnectedDeckNormalization
open KroneckerBoundedCoverDimensions



end KroneckerFiniteConnectedDeckClasses
end

/- Original module: KroneckerStableCoverIndexFinite -/
section
set_option autoImplicit false
namespace KroneckerStableCoverIndexFinite
open KroneckerReducedColorWords KroneckerWordParity KroneckerColorWordCover
open KroneckerCoverSupportRadius KroneckerDeckDimensionClasses
open KroneckerFiniteConnectedDeckClasses KroneckerFiniteQuiverHom

/-- All actual colored-cover arrows between positive-dimensional vertices,
including arrows whose representation map is zero. -/
abbrev CoverArrow (d : Word →₀ ℕ) :=
  {p : SupportVertex d × SupportVertex d //
    parity p.1.val = 0 ∧ cover.Adj p.1.val p.2.val}

abbrev CoverRepresentation (d : Word →₀ ℕ) :=
  Representation (fun a : CoverArrow d => a.val.1) (fun a : CoverArrow d => a.val.2)
    (fun v : SupportVertex d => d v.val)

/-- Negative King convention: sink total on sources, minus source total on sinks. -/
def coverKingWeight (d : Word →₀ ℕ) (v : SupportVertex d) : ℤ :=
  if parity v.val = 0 then (d.sum (fun w n => if parity w = 1 then n else 0) : ℤ)
  else -(d.sum (fun w n => if parity w = 0 then n else 0) : ℤ)

/-- King stability on the exact finite positive-support cover quiver forces
connectivity; no graph connectivity or nonzero-arrow assumption is supplied. -/
theorem stable_cover_support_preconnected (d : Word →₀ ℕ)
    (R : CoverRepresentation d) (θ : SupportVertex d → ℤ) (hR : Stable θ R) :
    (supportGraph d).Preconnected := by
  classical
  apply stable_positive_support_preconnected R θ hR
  · intro v
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp v.property)
  · intro a _
    exact (show (supportGraph d).Adj a.val.1 a.val.2 from a.property.2).reachable



end KroneckerStableCoverIndexFinite
end
