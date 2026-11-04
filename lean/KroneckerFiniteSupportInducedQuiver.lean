import KroneckerAbelianIteratedGirth
import KroneckerFiniteQuiverStableIso

/-!
# Finite-support induced quivers and extension by zero

For a finitely supported dimension vector on an arbitrary typed quiver, this
module constructs the finite vertex support and the arrows whose two endpoints
lie in that support.  Coordinate representations restrict to this induced
quiver and extend by zero back to the full quiver.  The two operations are
inverse on the nose.  No `Fintype` instance on the ambient vertex or arrow type
is used.
-/

set_option autoImplicit false

namespace KroneckerFiniteSupportInducedQuiver

open KroneckerAbelianCover KroneckerFiniteQuiverHom

variable {V A : Type} [DecidableEq V]

theorem representation_ext {V A : Type} {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (h : R.arrow = S.arrow) : R = S := by
  cases R
  cases S
  cases h
  rfl

/-- The vertices on which a finitely supported dimension vector is nonzero. -/
abbrev SupportVertex (d : V →₀ ℕ) := {v : V // v ∈ d.support}

/-- Arrows with both endpoints in the finite dimension support. -/
abbrev SupportArrow (s t : A → V) (d : V →₀ ℕ) :=
  {a : A // s a ∈ d.support ∧ t a ∈ d.support}

/-- The full subquiver induced by the support of `d`. -/
@[reducible] def supportQuiver (Q : TypedQuiver) [DecidableEq Q.V] (d : Q.V →₀ ℕ) : TypedQuiver where
  V := SupportVertex d
  A := SupportArrow Q.source Q.target d
  source a := ⟨Q.source a.val, a.property.1⟩
  target a := ⟨Q.target a.val, a.property.2⟩

/-- Restriction of the ambient dimension vector to its nonzero support. -/
def supportDimension (d : V →₀ ℕ) : SupportVertex d → ℕ := fun v => d v.val

/-- Restrict an actual coordinate representation to the induced support quiver. -/
noncomputable def restrictToSupport (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ)
    (R : Representation Q.source Q.target (fun v => d v)) :
    Representation (supportQuiver Q d).source (supportQuiver Q d).target
      (supportDimension d) where
  arrow a := R.arrow a.val

/-- Extend a representation of the induced support quiver by zero.  On an
ambient arrow whose two endpoints lie in the support we use the given arrow
map; every other arrow gets the zero map. -/
noncomputable def extendByZero (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ)
    (S : Representation (supportQuiver Q d).source (supportQuiver Q d).target
      (supportDimension d)) :
    Representation Q.source Q.target (fun v => d v) where
  arrow a := if h : Q.source a ∈ d.support ∧ Q.target a ∈ d.support then
      S.arrow ⟨a, h⟩
    else 0

set_option backward.isDefEq.respectTransparency false in
/-- Restriction after extension by zero recovers every representation of the
quiver induced on the finite vertex support literally.  The arrow type itself
need not be finite when the ambient quiver has infinitely many parallel arrows. -/
theorem restrict_extend (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ)
    (S : Representation (supportQuiver Q d).source (supportQuiver Q d).target
      (supportDimension d)) :
    restrictToSupport Q d (extendByZero Q d S) = S := by
  apply representation_ext
  funext a
  change (extendByZero Q d S).arrow a.val = S.arrow a
  simp only [extendByZero]
  rw [dite_eq_left a.property]

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero after restriction recovers the original ambient
representation.  The only nontrivial case is an arrow with an endpoint outside
the dimension support; then its source or target vector space has dimension
zero, so its original linear map is already zero. -/
theorem extend_restrict (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ)
    (R : Representation Q.source Q.target (fun v => d v)) :
    extendByZero Q d (restrictToSupport Q d R) = R := by
  apply representation_ext
  funext a
  apply LinearMap.ext
  intro x
  by_cases h : d (Q.source a) ≠ 0 ∧ d (Q.target a) ≠ 0
  · have hm : Q.source a ∈ d.support ∧ Q.target a ∈ d.support := by
      simpa using h
    simp only [extendByZero]
    rw [dite_eq_left hm]
    rfl
  · have hm : ¬(Q.source a ∈ d.support ∧ Q.target a ∈ d.support) := by
      simpa using h
    simp only [extendByZero]
    rw [dite_eq_right hm]
    change 0 = (R.arrow a) x
    by_cases hs : d (Q.source a) = 0
    · have hx : x = 0 := by
        funext i
        exact Fin.elim0 (hs ▸ i)
      simp [hx]
    · have htd : d (Q.target a) = 0 := by
        by_contra ht
        exact h ⟨hs, ht⟩
      symm
      funext i
      exact Fin.elim0 (htd ▸ i)

/-- Restriction and extension by zero give an equivalence of the two actual
coordinate-representation types. -/
noncomputable def representationEquiv (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) :
    Representation Q.source Q.target (fun v => d v) ≃
      Representation (supportQuiver Q d).source (supportQuiver Q d).target
        (supportDimension d) where
  toFun := restrictToSupport Q d
  invFun := extendByZero Q d
  left_inv := extend_restrict Q d
  right_inv := restrict_extend Q d

end KroneckerFiniteSupportInducedQuiver
