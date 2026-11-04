import KroneckerCanonicalKroneckerModuli

/-! A two-space presentation for arbitrary-m actual Kronecker representations,
using all invariant source/sink subspaces. This is the working linear-algebra
model for the pending global sink-reflection construction. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionPairModel
open Module KroneckerFiniteQuiverHom KroneckerCanonicalKroneckerModuli
open scoped BigOperators

abbrev PairRep (m a b : ℕ) := Fin m → Space a →ₗ[ℂ] Space b

def PairInvariant {m a b : ℕ} (R : PairRep m a b)
    (U : Submodule ℂ (Space a)) (W : Submodule ℂ (Space b)) : Prop :=
  ∀ i x,x∈U → R i x∈W

def PairStable {m a b : ℕ} (R : PairRep m a b) : Prop :=
  ∀ (U : Submodule ℂ (Space a)) (W : Submodule ℂ (Space b)),
    PairInvariant R U W → 0<finrank ℂ U+finrank ℂ W → finrank ℂ U+finrank ℂ W<a+b →
      (b : ℤ)*(finrank ℂ U : ℤ)-(a : ℤ)*(finrank ℂ W : ℤ)<0

def toRepresentation {m a b : ℕ} (R : PairRep m a b) :
    Representation (source m) (target m) (dimension a b) := ⟨R⟩

def fromRepresentation {m a b : ℕ}
    (R : Representation (source m) (target m) (dimension a b)) : PairRep m a b := R.arrow

def representationEquiv (m a b : ℕ) : PairRep m a b ≃
    Representation (source m) (target m) (dimension a b) where
  toFun := toRepresentation
  invFun := fromRepresentation
  left_inv _ := rfl
  right_inv R := by cases R;rfl
end KroneckerReflectionPairModel
