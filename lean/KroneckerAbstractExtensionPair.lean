import Mathlib.LinearAlgebra.Prod
import KroneckerAbstractPairHom

/- Original module: KroneckerTriangularLinearMap -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerTriangularLinearAlgebra
variable {K U V U' V' : Type} [CommRing K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup U'] [Module K U'] [AddCommGroup V'] [Module K V']

def triangular (l : U →ₗ[K] U') (x : V →ₗ[K] U') (r : V →ₗ[K] V') : (U × V) →ₗ[K] (U' × V') where
  toFun p := (l p.1 + x p.2, r p.2)
  map_add' p q := by
    apply Prod.ext
    · simp only [map_add, Prod.fst_add, Prod.snd_add]; abel
    · exact map_add r _ _
  map_smul' c p := by apply Prod.ext <;> simp [map_smul, smul_add]

theorem triangular_apply (l : U →ₗ[K] U') (x : V →ₗ[K] U') (r : V →ₗ[K] V') (u : U) (v : V) :
    triangular l x r (u, v) = (l u + x v, r v) := rfl


theorem triangular_projection (l : U →ₗ[K] U') (x : V →ₗ[K] U') (r : V →ₗ[K] V') (p : U × V) :
    (triangular l x r p).2 = r p.2 := rfl
end KroneckerTriangularLinearAlgebra
end
end

/- Original module: KroneckerAbstractExtensionPair -/
section
/-! Triangular actual Kronecker extensions on arbitrary endpoint vector spaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractExtensionPair
open KroneckerAbstractPairHom KroneckerTriangularLinearAlgebra
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
def extension (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y) : Rep m (X×V) (Y×W) :=
 fun i => triangular (S i) (z i) (R i)
theorem apply (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y) (i : Fin m) (x : X) (v : V) :
 extension R S z i (x,v)=(S i x+z i v,R i v) := rfl
end KroneckerAbstractExtensionPair
end
end
