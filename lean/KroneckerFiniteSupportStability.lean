import KroneckerFiniteSupportInducedQuiver

section

/-!
# All subrepresentations and finite vertex support

Restriction and extension by zero identify *all* subrepresentations of an
ambient coordinate representation whose dimension vector is a `Finsupp` with
all subrepresentations of its restriction to the quiver induced on the finite
vertex support.  Outside the support, every ambient coordinate space has
dimension zero, so every vertex submodule is forced to be bottom.
-/

set_option autoImplicit false

namespace KroneckerFiniteSupportSubrepresentations

open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver

theorem subrep_ext {V A : Type} {s t : A → V} {d : V → ℕ}
    {R : Representation s t d} {U W : Subrep R}
    (h : U.space = W.space) : U = W := by
  cases U
  cases W
  cases h
  rfl

/-- Restrict every invariant vertex-submodule family to the support. -/
noncomputable def restrictSubrep (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R : Representation Q.source Q.target (fun v => d v))
    (U : Subrep R) : Subrep (restrictToSupport Q d R) where
  space v := U.space v.val
  invariant a x hx := U.invariant a.val x hx

set_option backward.isDefEq.respectTransparency false in
/-- Extend every subrepresentation of the induced-support representation by
bottom outside the support.  Invariance is proved directly across every ambient
arrow; no finiteness of the ambient quiver is used. -/
noncomputable def extendSubrep (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R : Representation Q.source Q.target (fun v => d v))
    (U : Subrep (restrictToSupport Q d R)) : Subrep R where
  space v := if h : v ∈ d.support then U.space ⟨v, h⟩ else ⊥
  invariant := by
    intro a x hx
    by_cases hs : Q.source a ∈ d.support
    · by_cases ht : Q.target a ∈ d.support
      · have hi := U.invariant (⟨a, hs, ht⟩ : SupportArrow Q.source Q.target d) x
          (by simpa [hs] using hx)
        simpa [ht, restrictToSupport, supportDimension] using hi
      · have htd : d (Q.target a) = 0 := by simpa using ht
        have hy : R.arrow a x = 0 := by
          funext i
          exact Fin.elim0 (htd ▸ i)
        rw [hy]
        exact Submodule.zero_mem _
    · have hxbot : x ∈ (⊥ : Submodule ℂ (Space (d (Q.source a)))) := by
        simpa [hs] using hx
      have hxzero : x = 0 := by simpa using hxbot
      rw [hxzero, map_zero]
      exact Submodule.zero_mem _

/-- Restricting an extended subrepresentation recovers it exactly. -/
theorem restrict_extend_subrep (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R : Representation Q.source Q.target (fun v => d v))
    (U : Subrep (restrictToSupport Q d R)) :
    restrictSubrep Q d R (extendSubrep Q d R U) = U := by
  apply subrep_ext
  funext v
  change (if h : v.val ∈ d.support then U.space ⟨v.val, h⟩ else ⊥) = U.space v
  rw [dite_eq_left v.property]

set_option backward.isDefEq.respectTransparency false in
/-- Extending a restricted ambient subrepresentation recovers it exactly.
At an unsupported vertex its ambient space is zero-dimensional, hence the
original vertex submodule is already bottom. -/
theorem extend_restrict_subrep (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R : Representation Q.source Q.target (fun v => d v))
    (U : Subrep R) :
    extendSubrep Q d R (restrictSubrep Q d R U) = U := by
  apply subrep_ext
  funext v
  by_cases h : v ∈ d.support
  · simp only [extendSubrep]
    rw [dite_eq_left h]
    rfl
  · simp only [extendSubrep]
    rw [dite_eq_right h]
    apply le_antisymm
    · exact bot_le
    · intro x hx
      have hd : d v = 0 := by simpa using h
      have hxzero : x = 0 := by
        funext i
        exact Fin.elim0 (hd ▸ i)
      simpa [hxzero]

/-- ALL subrepresentations correspond, not merely subrepresentations already
presented with support witnesses. -/
noncomputable def subrepEquiv (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R : Representation Q.source Q.target (fun v => d v)) :
    Subrep R ≃ Subrep (restrictToSupport Q d R) where
  toFun := restrictSubrep Q d R
  invFun := extendSubrep Q d R
  left_inv := extend_restrict_subrep Q d R
  right_inv := restrict_extend_subrep Q d R

end KroneckerFiniteSupportSubrepresentations
end

section

/-!
# King statistics and stability on finite support

This module defines the size, character weight, total dimension, and King
balance of an ambient representation with a `Finsupp` dimension vector by
summing only over its finite vertex support.  The ALL-subrepresentation
equivalence identifies these statistics with the ordinary finite-vertex
statistics on the induced-support representation, and yields a two-way King
stability theorem without a `Fintype` instance on the ambient vertex type.
-/

set_option autoImplicit false

namespace KroneckerFiniteSupportStability

open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportSubrepresentations
open Module
open scoped BigOperators

noncomputable local instance supportVertexFintype {V : Type} [DecidableEq V]
    (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

noncomputable local instance supportQuiverVertexFintype
    (Q : TypedQuiver) [DecidableEq Q.V] (d : Q.V →₀ ℕ) :
    Fintype (supportQuiver Q d).V := supportVertexFintype d

/-- Character restricted to the finite vertex support. -/
def supportCharacter {V : Type} [DecidableEq V] (d : V →₀ ℕ) (θ : V → ℤ) :
    SupportVertex d → ℤ := fun v => θ v.val

/-- Total dimension, summed over the finite support. -/
noncomputable def supportTotalDimension {V : Type} [DecidableEq V] (d : V →₀ ℕ) : ℕ :=
  ∑ v : SupportVertex d, d v.val

/-- Character balance of the full dimension vector, summed over its support. -/
noncomputable def supportBalance {V : Type} [DecidableEq V]
    (d : V →₀ ℕ) (θ : V → ℤ) : ℤ :=
  ∑ v : SupportVertex d, θ v.val * (d v.val : ℤ)

/-- Dimension of an ambient subrepresentation, summed over the finite support. -/
noncomputable def supportSize {V A : Type} [DecidableEq V] {s t : A → V}
    (d : V →₀ ℕ) {R : Representation s t (fun v => d v)} (U : Subrep R) : ℕ :=
  ∑ v : SupportVertex d, finrank ℂ (U.space v.val)

/-- King weight of an ambient subrepresentation, summed over finite support. -/
noncomputable def supportWeight {V A : Type} [DecidableEq V] {s t : A → V}
    (d : V →₀ ℕ) (θ : V → ℤ) {R : Representation s t (fun v => d v)}
    (U : Subrep R) : ℤ :=
  ∑ v : SupportVertex d, θ v.val * (finrank ℂ (U.space v.val) : ℤ)

/-- King stability for an ambient representation, quantified over ALL ambient
subrepresentations but with finite sums taken over the dimension support. -/
def FiniteSupportStable {V A : Type} [DecidableEq V] {s t : A → V}
    (d : V →₀ ℕ) (θ : V → ℤ) (R : Representation s t (fun v => d v)) : Prop :=
  supportBalance d θ = 0 ∧
    ∀ U : Subrep R, 0 < supportSize d U →
      supportSize d U < supportTotalDimension d → supportWeight d θ U < 0

theorem restrict_size {Q : TypedQuiver} [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (R : Representation Q.source Q.target (fun v => d v))
    (U : Subrep R) :
    size (restrictSubrep Q d R U) = supportSize d U := by
  rfl

theorem restrict_weight {Q : TypedQuiver} [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (θ : Q.V → ℤ)
    (R : Representation Q.source Q.target (fun v => d v)) (U : Subrep R) :
    weight (supportCharacter d θ) (restrictSubrep Q d R U) = supportWeight d θ U := by
  rfl

theorem support_total_dimension_eq {Q : TypedQuiver} [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) :
    (∑ v, supportDimension d v) = supportTotalDimension d := by
  rfl


/-- Stability on the full ambient quiver with finite-support sums is equivalent
to ordinary King stability of the restricted representation on the finite
vertex support.  Both directions quantify over all subrepresentations, using
the actual equivalence from `KroneckerFiniteSupportSubrepresentations`. -/
theorem finiteSupportStable_iff_restrict (Q : TypedQuiver) [DecidableEq Q.V]
    (d : Q.V →₀ ℕ) (θ : Q.V → ℤ)
    (R : Representation Q.source Q.target (fun v => d v)) :
    FiniteSupportStable d θ R ↔
      Stable (supportCharacter d θ) (restrictToSupport Q d R) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro U hn hp
    obtain ⟨W, rfl⟩ := (subrepEquiv Q d R).surjective U
    change weight (supportCharacter d θ) (restrictSubrep Q d R W) < 0
    rw [restrict_weight]
    apply h.2 W
    · rw [← restrict_size]
      exact hn
    · rw [← restrict_size, ← support_total_dimension_eq]
      exact hp
  · intro h
    refine ⟨h.1, ?_⟩
    intro U hn hp
    have hw := h.2 (restrictSubrep Q d R U)
      (by rw [restrict_size]; exact hn)
      (by rw [restrict_size, support_total_dimension_eq]; exact hp)
    rw [restrict_weight] at hw
    exact hw

end KroneckerFiniteSupportStability
end

