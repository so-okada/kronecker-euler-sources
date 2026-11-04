import KroneckerFiniteSupportStability

/-! Restriction and extension of actual representation isomorphisms on finite
positive-dimensional support. Unsupported coordinate spaces have only zero. -/
set_option autoImplicit false
namespace KroneckerFiniteSupportIsomorphisms
open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver

noncomputable def restrictIso (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R S : Representation Q.source Q.target (fun v => d v))
    (e : Iso R S) : Iso (restrictToSupport Q d R) (restrictToSupport Q d S) where
  map v := e.map v.val
  commutes a x := e.commutes a.val x

set_option backward.isDefEq.respectTransparency false in
/-- The inverse construction extends by the identity on the zero coordinate
spaces. Arrows crossing the support boundary are checked explicitly. -/
noncomputable def extendIso (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R S : Representation Q.source Q.target (fun v => d v))
    (e : Iso (restrictToSupport Q d R) (restrictToSupport Q d S)) : Iso R S where
  map v := if h : v ∈ d.support then e.map ⟨v, h⟩ else LinearEquiv.refl ℂ _
  commutes := by
    intro a x
    by_cases hs : Q.source a ∈ d.support
    · by_cases ht : Q.target a ∈ d.support
      · simpa only [dite_eq_left hs, dite_eq_left ht, restrictToSupport, supportDimension] using
          e.commutes (⟨a, hs, ht⟩ : SupportArrow Q.source Q.target d) x
      · have hd : d (Q.target a) = 0 := by simpa using ht
        funext i
        exact Fin.elim0 (hd ▸ i)
    · have hd : d (Q.source a) = 0 := by simpa using hs
      have hx : x = 0 := by
        funext i
        exact Fin.elim0 (hd ▸ i)
      simp only [hx, map_zero]

theorem nonempty_iso_iff_restrict (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R S : Representation Q.source Q.target (fun v => d v)) :
    Nonempty (Iso R S) ↔ Nonempty (Iso (restrictToSupport Q d R) (restrictToSupport Q d S)) :=
  ⟨fun ⟨e⟩ => ⟨restrictIso Q d R S e⟩, fun ⟨e⟩ => ⟨extendIso Q d R S e⟩⟩

theorem iso_ext {V A : Type} {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} {e f : Iso R S} (h : e.map = f.map) : e = f := by
  cases e
  cases f
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrict_extend_iso (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R S : Representation Q.source Q.target (fun v => d v))
    (e : Iso (restrictToSupport Q d R) (restrictToSupport Q d S)) :
    restrictIso Q d R S (extendIso Q d R S e) = e := by
  apply iso_ext
  funext v
  simp only [restrictIso, extendIso, dite_eq_left v.property]

theorem extend_restrict_iso (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R S : Representation Q.source Q.target (fun v => d v))
    (e : Iso R S) : extendIso Q d R S (restrictIso Q d R S e) = e := by
  apply iso_ext
  funext v
  by_cases h : v ∈ d.support
  · simp only [extendIso, restrictIso, dite_eq_left h]
  · simp only [extendIso]
    apply LinearEquiv.ext
    intro x
    have hd : d v = 0 := by simpa using h
    funext i
    exact Fin.elim0 (hd ▸ i)

/-- Full faithfulness at the isomorphism level, not just existence transport. -/
noncomputable def isoEquiv (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R S : Representation Q.source Q.target (fun v => d v)) :
    Iso R S ≃ Iso (restrictToSupport Q d R) (restrictToSupport Q d S) where
  toFun := restrictIso Q d R S
  invFun := extendIso Q d R S
  left_inv := extend_restrict_iso Q d R S
  right_inv := restrict_extend_iso Q d R S

open KroneckerFiniteSupportStability
open scoped BigOperators

noncomputable local instance supportFintype {V : Type} [DecidableEq V]
    (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

/-- Positive Euler form on a finite induced support forces uniqueness of the
stable representation on the WHOLE ambient quiver. Finiteness is required only
of the induced support arrows, not of the ambient quiver. -/
theorem positive_support_euler_iso (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) [Fintype (SupportArrow Q.source Q.target d)] (θ : Q.V → ℤ)
    (R S : Representation Q.source Q.target (fun v => d v))
    (hR : FiniteSupportStable d θ R) (hS : FiniteSupportStable d θ S)
    (he : (∑ a : SupportArrow Q.source Q.target d,
        d (Q.source a.val) * d (Q.target a.val)) <
      ∑ v : SupportVertex d, d v.val * d v.val) : Nonempty (Iso R S) := by
  let : Fintype (supportQuiver Q d).V := supportFintype d
  let : Fintype (supportQuiver Q d).A :=
    inferInstanceAs (Fintype (SupportArrow Q.source Q.target d))
  have hr := (finiteSupportStable_iff_restrict Q d θ R).mp hR
  have hs := (finiteSupportStable_iff_restrict Q d θ S).mp hS
  have hi := positive_euler_stable_iso (restrictToSupport Q d R)
    (restrictToSupport Q d S) hr hs he
  exact (nonempty_iso_iff_restrict Q d R S).mpr hi

end KroneckerFiniteSupportIsomorphisms
