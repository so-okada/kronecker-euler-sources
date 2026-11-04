import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Matrix.Mul

/-! The affine coordinate algebra of actual arrow matrices, over arbitrary base algebras.
This is a representation parameter space; no orbit quotient or stable moduli is asserted. -/
noncomputable section

namespace KroneckerArrowParameterAlgebra

variable {V A : Type*} (s t : A → V) (d : V → ℕ)

abbrev Coordinate := Σ a : A, Fin (d (t a)) × Fin (d (s a))
abbrev Family (R : Type*) := ∀ a : A, Matrix (Fin (d (t a))) (Fin (d (s a))) R
abbrev CoordinateAlgebra (k : Type*) [CommRing k] := MvPolynomial (Coordinate s t d) k

variable {s t d} {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

def universal : Family s t d (CoordinateAlgebra s t d k) :=
  fun a i j => MvPolynomial.X ⟨a, i, j⟩

def specialize (f : CoordinateAlgebra s t d k →ₐ[k] R) : Family s t d R :=
  fun a i j => f (universal a i j)

def evaluation (M : Family s t d R) : CoordinateAlgebra s t d k →ₐ[k] R :=
  MvPolynomial.aeval fun c => M c.1 c.2.1 c.2.2

@[simp] theorem evaluation_universal (M : Family s t d R) (a i j) :
    evaluation M (universal (k := k) a i j) = M a i j := by
  simp [evaluation, universal]

/-- Every family of actual arrow matrices over any commutative base algebra is obtained
uniquely from the universal arrow family. This is an algebra-valued representability statement. -/
def parameterEquiv : (CoordinateAlgebra s t d k →ₐ[k] R) ≃ Family s t d R where
  toFun := specialize
  invFun := evaluation
  left_inv f := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, i, j⟩
    simp [evaluation, specialize, universal]
  right_inv M := by
    funext a i j
    exact evaluation_universal M a i j




end KroneckerArrowParameterAlgebra
