import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import KroneckerOppositeArrowFamilies
import KroneckerMatrixKingDictionary

/- Original module: KroneckerCoordinateAnnihilator -/
section
/-! Algebraic annihilators in fixed coordinate spaces.  The pairing is bilinear;
there is no complex conjugation or Hermitian-orthogonal convention. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open Matrix
variable {K : Type} [Field K] {n : ℕ}

def coordinateAnnihilator (U : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) :=
  U.dualAnnihilator.comap (dotProductEquiv K (Fin n)).toLinearMap

theorem mem_coordinateAnnihilator (U : Submodule K (Fin n → K)) (y : Fin n → K) :
    y ∈ coordinateAnnihilator U ↔ ∀ x ∈ U, dotProduct y x = 0 :=
  Submodule.mem_dualAnnihilator ((dotProductEquiv K (Fin n)) y)


/-- Double algebraic annihilation recovers every subspace, including zero and
the whole coordinate space. -/
theorem coordinateAnnihilator_involutive (U : Submodule K (Fin n → K)) :
    coordinateAnnihilator (coordinateAnnihilator U) = U := by
  apply le_antisymm
  · intro x hx
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U x).mp
    intro f hf
    let y := (dotProductEquiv K (Fin n)).symm f
    have hy : y ∈ coordinateAnnihilator U := by
      change dotProductEquiv K (Fin n) y ∈ U.dualAnnihilator
      simpa only [y, LinearEquiv.apply_symm_apply] using hf
    have hxy := (mem_coordinateAnnihilator (coordinateAnnihilator U) x).mp hx y hy
    have he : dotProduct y x = f x := by
      change (dotProductEquiv K (Fin n) y) x = f x
      simp only [y, LinearEquiv.apply_symm_apply]
    rw [← he, dotProduct_comm]
    exact hxy
  · intro x hx
    apply (mem_coordinateAnnihilator (coordinateAnnihilator U) x).mpr
    intro y hy
    rw [dotProduct_comm]
    exact (mem_coordinateAnnihilator U y).mp hy x hx

end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerAnnihilatorArrowInvariance -/
section
/-! The annihilator of an invariant pair of subspaces is invariant under the
actual transpose arrow in the reverse direction. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open Matrix
variable {K : Type} [Field K] {m n : ℕ}

theorem transpose_preserves_annihilator
    (M : Matrix (Fin m) (Fin n) K)
    (U : Submodule K (Fin n → K)) (W : Submodule K (Fin m → K))
    (h : ∀ x ∈ U, M *ᵥ x ∈ W) :
    ∀ y ∈ coordinateAnnihilator W, M.transpose *ᵥ y ∈ coordinateAnnihilator U := by
  intro y hy
  apply (mem_coordinateAnnihilator U _).mpr
  intro x hx
  have hxy := (mem_coordinateAnnihilator W y).mp hy (M *ᵥ x) (h x hx)
  rw [dotProduct_comm]
  rw [dotProduct_mulVec]
  rw [vecMul_transpose]
  rw [dotProduct_comm]
  exact hxy


end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerAnnihilatorDimensions -/
section
/-! Exact complement dimensions for coordinate annihilators, with no
nonzero-dimension hypothesis. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
variable {K : Type} [Field K] {n : ℕ}

theorem coordinateAnnihilator_finrank (U : Submodule K (Fin n → K)) :
    Module.finrank K U + Module.finrank K (coordinateAnnihilator U) = n := by
  have he := ((dotProductEquiv K (Fin n)).ofSubmodule' U.dualAnnihilator).finrank_eq
  change Module.finrank K (coordinateAnnihilator U) = Module.finrank K U.dualAnnihilator at he
  rw [he]
  simpa using Subspace.finrank_add_finrank_dualAnnihilator_eq U


end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerOppositeMatrixSubrepresentations -/
section
/-! Duality carries every matrix subrepresentation to its vertexwise algebraic
annihilator, with no restriction to selected coordinate subspaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open KroneckerRingQuiverFamilies KroneckerMatrixKingDictionary
variable {V A : Type} {s t : A → V} {d : V → ℕ} {M : Family s t d ℂ}

def annihilatorSubrep (U : MatrixSubrep M) : MatrixSubrep (oppositeFamily M) where
  space v := coordinateAnnihilator (U.space v)
  invariant a := transpose_preserves_annihilator (M a) (U.space (s a))
    (U.space (t a)) (U.invariant a)

@[simp] theorem annihilatorSubrep_involutive (U : MatrixSubrep M) :
    annihilatorSubrep (annihilatorSubrep U) = U := by
  cases U with
  | mk space invariant =>
    have h : (fun v => coordinateAnnihilator (coordinateAnnihilator (space v))) = space := by
      funext v
      exact coordinateAnnihilator_involutive (space v)
    simp only [annihilatorSubrep, h]
    rfl

/-- This is the full subrepresentation correspondence on the opposite quiver. -/
def annihilatorSubrepEquiv (M : Family s t d ℂ) :
    MatrixSubrep M ≃ MatrixSubrep (oppositeFamily M) where
  toFun := annihilatorSubrep
  invFun := annihilatorSubrep
  left_inv := annihilatorSubrep_involutive
  right_inv := annihilatorSubrep_involutive

end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerOppositeSubrepresentationDimensions -/
section
/-! Complement dimensions and total sizes for all opposite-quiver
subrepresentations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open KroneckerRingQuiverFamilies KroneckerMatrixKingDictionary
open scoped BigOperators
variable {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
  {M : Family s t d ℂ}

theorem annihilatorSubrep_dimension (U : MatrixSubrep M) (v : V) :
    subdimension U v + subdimension (annihilatorSubrep U) v = d v :=
  coordinateAnnihilator_finrank (U.space v)

theorem annihilatorSubrep_size (U : MatrixSubrep M) :
    size U + size (annihilatorSubrep U) = ∑ v, d v := by
  rw [size, size, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => annihilatorSubrep_dimension U v)

/-- Proper nonzero subrepresentations correspond to proper nonzero ones. -/
theorem annihilatorSubrep_proper_nonzero_iff (U : MatrixSubrep M) :
    (0 < size (annihilatorSubrep U) ∧ size (annihilatorSubrep U) < ∑ v, d v) ↔
      (0 < size U ∧ size U < ∑ v, d v) := by
  have h := annihilatorSubrep_size U
  omega

end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerOppositeSubrepresentationWeights -/
section
/-! The precise weight-complement identity responsible for the sign reversal
in numerical King stability. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open KroneckerRingQuiverFamilies KroneckerMatrixKingDictionary
open scoped BigOperators
variable {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
  {M : Family s t d ℂ}

theorem annihilatorSubrep_weight_add (θ : V → ℤ) (U : MatrixSubrep M) :
    weight θ U + weight θ (annihilatorSubrep U) = ∑ v, θ v * (d v : ℤ) := by
  rw [weight, weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← mul_add, ← Nat.cast_add, annihilatorSubrep_dimension]

theorem annihilatorSubrep_opposite_weight (θ : V → ℤ)
    (hθ : (∑ v, θ v * (d v : ℤ)) = 0) (U : MatrixSubrep M) :
    weight (fun v => -θ v) (annihilatorSubrep U) = weight θ U := by
  have h := annihilatorSubrep_weight_add θ U
  rw [hθ] at h
  have he : weight (fun v => -θ v) (annihilatorSubrep U) =
      -weight θ (annihilatorSubrep U) := by
    simp [weight, neg_mul, Finset.sum_neg_distrib]
  rw [he]
  omega

end KroneckerOppositeArrowFamilies
end
end
