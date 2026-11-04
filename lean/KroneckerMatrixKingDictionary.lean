import KroneckerComplexFamilyBridge
import KroneckerArrowParameterAlgebra

/-! Exact all-subrepresentation and opposite-sign numerical dictionary for the
matrix parameter space in King's convention. No GIT construction is assumed here. -/
noncomputable section
namespace KroneckerMatrixKingDictionary
open KroneckerRingQuiverFamilies
open scoped BigOperators Matrix

variable {V A : Type} {s t : A → V} {d : V → ℕ}

structure MatrixSubrep (M : Family s t d ℂ) where
  space : ∀v, Submodule ℂ (Fin (d v) → ℂ)
  invariant : ∀a x, x ∈ space (s a) → M a *ᵥ x ∈ space (t a)

def toSubrep {M : Family s t d ℂ} (U : MatrixSubrep M) :
    KroneckerFiniteQuiverHom.Subrep (toRepresentation s t d M) where
  space := U.space
  invariant := U.invariant

def fromSubrep {M : Family s t d ℂ}
    (U : KroneckerFiniteQuiverHom.Subrep (toRepresentation s t d M)) : MatrixSubrep M where
  space := U.space
  invariant := U.invariant

/-- Every vertexwise invariant subspace family occurs on both sides with literally
the same spaces. No chosen collection of subrepresentations is substituted. -/
def allSubrepEquiv (M : Family s t d ℂ) :
    MatrixSubrep M ≃ KroneckerFiniteQuiverHom.Subrep (toRepresentation s t d M) where
  toFun := toSubrep
  invFun := fromSubrep
  left_inv U := by cases U; rfl
  right_inv U := by cases U; rfl

variable [Fintype V]

def subdimension {M : Family s t d ℂ} (U : MatrixSubrep M) (v : V) : ℕ :=
  Module.finrank ℂ (U.space v)

def size {M : Family s t d ℂ} (U : MatrixSubrep M) : ℕ := ∑v, subdimension U v

def weight (θ : V → ℤ) {M : Family s t d ℂ} (U : MatrixSubrep M) : ℤ :=
  ∑v, θ v * (subdimension U v : ℤ)

/-- King's numerical convention: every proper nonzero subrepresentation has
positive weight. Thus its character vector is the negative of the internal convention. -/
def KingStable (θ : V → ℤ) (M : Family s t d ℂ) : Prop :=
  (∑v, θ v * (d v : ℤ)) = 0 ∧
    ∀U : MatrixSubrep M, 0 < size U → size U < ∑v, d v → 0 < weight θ U


set_option backward.isDefEq.respectTransparency false in
theorem opposite_weight (θ : V → ℤ) {M : Family s t d ℂ} (U : MatrixSubrep M) :
    KroneckerFiniteQuiverHom.weight (fun v => -θ v) (toSubrep U) = -weight θ U := by
  simp [KroneckerFiniteQuiverHom.weight, weight, subdimension, toSubrep,
    neg_mul, Finset.sum_neg_distrib]

set_option backward.isDefEq.respectTransparency false in
/-- This dictionary uses all actual subrepresentations and keeps the sign change
explicit. It supplies the numerical hypothesis translation needed by King1994. -/
theorem kingStable_iff_internal (θ : V → ℤ) (M : Family s t d ℂ) :
    KingStable θ M ↔ KroneckerFiniteQuiverHom.Stable (fun v => -θ v)
      (toRepresentation s t d M) := by
  constructor
  · rintro ⟨ht,h⟩
    refine ⟨by simpa [neg_mul, Finset.sum_neg_distrib] using ht, ?_⟩
    intro U hn hp
    have hh := h (fromSubrep U) hn hp
    simpa [KroneckerFiniteQuiverHom.weight, weight, subdimension, fromSubrep,
      neg_mul, Finset.sum_neg_distrib] using neg_neg_of_pos hh
  · rintro ⟨ht,h⟩
    refine ⟨by simpa [neg_mul, Finset.sum_neg_distrib] using ht, ?_⟩
    intro U hn hp
    have hh := h (toSubrep U) hn hp
    rw [opposite_weight] at hh
    exact neg_neg_iff_pos.mp hh


end KroneckerMatrixKingDictionary
