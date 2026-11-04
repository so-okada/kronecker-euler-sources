import KroneckerQuiverPullbackIsomorphisms
import KroneckerColoredCoverStableUniqueness

/-! Isomorphisms between dimensioned representations, without assuming equal
dimension vectors in the data; equality follows from the actual linear maps. -/
set_option autoImplicit false
namespace KroneckerDimensionedCoverIsomorphisms
open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerQuiverPullbackSubrepresentations
open KroneckerFiniteSupportStability KroneckerColoredCoverStableUniqueness

structure AcrossIso {Q : TypedQuiver} (S T : SupportedRepresentation Q) where
  map : ∀ v, Space (S.1 v) ≃ₗ[ℂ] Space (T.1 v)
  commutes : ∀ a x, map (Q.target a) (S.2.arrow a x) = T.2.arrow a (map (Q.source a) x)

noncomputable def AcrossIso.refl {Q : TypedQuiver} (S : SupportedRepresentation Q) : AcrossIso S S where
  map _ := LinearEquiv.refl ℂ _
  commutes _ _ := rfl

noncomputable def AcrossIso.symm {Q : TypedQuiver} {S T : SupportedRepresentation Q}
    (e : AcrossIso S T) : AcrossIso T S where
  map v := (e.map v).symm
  commutes := by
    intro a x
    apply (e.map (Q.target a)).injective
    simpa using (e.commutes a ((e.map (Q.source a)).symm x)).symm

noncomputable def AcrossIso.trans {Q : TypedQuiver} {S T U : SupportedRepresentation Q}
    (e : AcrossIso S T) (f : AcrossIso T U) : AcrossIso S U where
  map v := (e.map v).trans (f.map v)
  commutes := by
    intro a x
    change f.map (Q.target a) (e.map (Q.target a) (S.2.arrow a x)) =
      U.2.arrow a (f.map (Q.source a) (e.map (Q.source a) x))
    rw [e.commutes, f.commutes]

theorem AcrossIso.dimension_eq {Q : TypedQuiver} {S T : SupportedRepresentation Q}
    (e : AcrossIso S T) : S.1 = T.1 := by
  ext v
  simpa [Space] using (e.map v).finrank_eq

theorem transport_cross_commutes_iff {V : Type} (d e : V → ℕ)
    (E : ∀ v, Space (d v) → Space (e v)) {u v u' v' : V}
    (hu : u = u') (hv : v = v')
    (L : Space (d u) →ₗ[ℂ] Space (d v)) (M : Space (e u) →ₗ[ℂ] Space (e v)) :
    (∀ x, E v' (transportArrow d hu hv L x) = transportArrow e hu hv M (E u' x)) ↔
      (∀ x, E v (L x) = M (E u x)) := by
  cases hu
  cases hv
  rfl

noncomputable def pullAcrossIso {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    {S T : SupportedRepresentation R} (e : AcrossIso S T) :
    AcrossIso (pullSupported f S) (pullSupported f T) where
  map v := e.map (f.vertexEquiv v)
  commutes a := (transport_cross_commutes_iff (fun v => S.1 v) (fun v => T.1 v)
    (fun v => e.map v) (f.map_source a) (f.map_target a)
    (S.2.arrow (f.arrowEquiv a)) (T.2.arrow (f.arrowEquiv a))).mpr (e.commutes (f.arrowEquiv a))

noncomputable def AcrossIso.ofIso {Q : TypedQuiver} {d : Q.V →₀ ℕ}
    {S T : Representation Q.source Q.target (fun v => d v)} (e : Iso S T) :
    AcrossIso (⟨d, S⟩ : SupportedRepresentation Q) ⟨d, T⟩ where
  map := e.map
  commutes := e.commutes

open KroneckerReducedColorWords
local instance : DecidableEq coloredCoverQuiver.V := inferInstanceAs (DecidableEq Word)


end KroneckerDimensionedCoverIsomorphisms
