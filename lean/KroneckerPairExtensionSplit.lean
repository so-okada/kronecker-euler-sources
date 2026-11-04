import KroneckerAbstractExtensionPair

/-! Splitting a triangular pair extension is an explicit simultaneous graph equation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairExtensionSplit
open KroneckerAbstractPairHom
variable {m : ℕ} {V W X Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
def Split (R : Rep m V W) (S : Rep m X Y) (z : Fin m → V →ₗ[ℂ] Y) : Prop :=
 ∃ f : V →ₗ[ℂ] X,∃ g : W →ₗ[ℂ] Y,∀ i v,g (R i v)=S i (f v)+z i v
theorem zero (R : Rep m V W) (S : Rep m X Y) : Split R S 0 := by
 refine ⟨0,0,?_⟩;intro i v;simp
end KroneckerPairExtensionSplit
