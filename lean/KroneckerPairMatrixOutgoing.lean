import KroneckerStablePairReflection
import Mathlib.Topology.Instances.Matrix
import KroneckerAbstractCokernelReflection

section

/-! Fixed rectangular arrow matrices provide continuous coordinates for the
actual canonical family. Their associated linear maps recover the pair model. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairMatrixCoordinates
open KroneckerCanonicalKroneckerModuli KroneckerReflectionPairModel
abbrev Matrices (m a b : ℕ) := Fin m → Matrix (Fin b) (Fin a) ℂ
def pair {m a b : ℕ} (M : Matrices m a b) : PairRep m a b := fun i => Matrix.toLin' (M i)
def matrices {m a b : ℕ} (R : PairRep m a b) : Matrices m a b := fun i => LinearMap.toMatrix' (R i)
theorem pair_matrices {m a b : ℕ} (R : PairRep m a b) : pair (matrices R)=R := by
  funext i
  exact Matrix.toLin'_toMatrix' (R i)
def canonical {m a b : ℕ} (M : Matrices m a b) :
    KroneckerRingQuiverFamilies.Family (source m) (target m) (dimension a b) ℂ := M
end KroneckerPairMatrixCoordinates
end
end

section

/-! The incoming map is a single rectangular block matrix. Flattening its
source product gives an explicit continuous matrix depending on all arrows. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerPairMatrixIncoming
open KroneckerPairMatrixCoordinates
variable {m a b : ℕ}
def incoming (M : Matrices m a b) : Matrix (Fin b) (Fin m × Fin a) ℂ :=
  fun j p => M p.1 j p.2
theorem continuous_incoming : Continuous (@incoming m a b) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro p
  exact (continuous_apply p.2).comp ((continuous_apply j).comp (continuous_apply p.1))
def flatten : (Fin m → Fin a → ℂ) ≃ₗ[ℂ] ((Fin m × Fin a) → ℂ) where
  toFun x p := x p.1 p.2
  invFun x i j := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem evaluate (M : Matrices m a b) (x : Fin m → Fin a → ℂ) :
    Matrix.toLin' (incoming M) (flatten x)=KroneckerAbstractIncomingNaturality.incoming (pair M) x := by
  ext j
  simp [incoming,flatten,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,
    KroneckerAbstractIncomingNaturality.incoming,pair,Fintype.sum_prod_type]
end KroneckerPairMatrixIncoming
end
end

section

/-! The outgoing map is a continuous stacked rectangular matrix, with an
exact flattening identity against the abstract representation map. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerPairMatrixOutgoing
open KroneckerPairMatrixCoordinates
variable {m a b : ℕ}
def outgoing (M : Matrices m a b) : Matrix (Fin m × Fin b) (Fin a) ℂ :=
  fun p j => M p.1 p.2 j
theorem continuous_outgoing : Continuous (@outgoing m a b) := by
  change Continuous (fun M : Matrices m a b => fun p : Fin m × Fin b => M p.1 p.2)
  apply continuous_pi
  intro p
  exact (continuous_apply p.2).comp (continuous_apply p.1)
theorem evaluate (M : Matrices m a b) (x : Fin a → ℂ) :
    Matrix.toLin' (outgoing M) x =
      KroneckerPairMatrixIncoming.flatten (KroneckerAbstractOutgoingNaturality.outgoing (pair M) x) := rfl
end KroneckerPairMatrixOutgoing
end
end

