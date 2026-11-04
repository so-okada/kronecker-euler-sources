import KroneckerRingQuiverFamilies

/-! Reversing every actual arrow and transposing its matrix.  This construction
works over arbitrary commutative rings, including zero-dimensional vertices. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open KroneckerRingQuiverFamilies
variable {V A : Type} {s t : A → V} {d : V → ℕ}

def oppositeFamily {R : Type} (M : Family s t d R) : Family t s d R :=
  fun a => (M a).transpose

@[simp] theorem oppositeFamily_opposite {R : Type} (M : Family s t d R) :
    oppositeFamily (oppositeFamily M) = M := rfl

/-- A linear equivalence of the actual matrix parameter modules. -/
def oppositeFamilyEquiv (R : Type) [CommRing R] :
    Family s t d R ≃ₗ[R] Family t s d R where
  toFun := oppositeFamily
  invFun := oppositeFamily
  left_inv := oppositeFamily_opposite
  right_inv := oppositeFamily_opposite
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


end KroneckerOppositeArrowFamilies
