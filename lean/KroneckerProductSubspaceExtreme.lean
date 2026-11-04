import KroneckerProductSubspaceDimension

/-! Zero and full subobjects are detected by both endpoint parts. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProductSubspaceExtreme
open Module KroneckerProductSubspaceParts
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
theorem bot (U : Submodule ℂ (V×W)) (hl : leftPart U=⊥) (hr : rightPart U=⊥) : U=⊥ := by
 apply Submodule.finrank_eq_zero.mp
 rw [KroneckerProductSubspaceDimension.dimension,hl,hr];simp
theorem top (U : Submodule ℂ (V×W)) (hl : leftPart U=⊤) (hr : rightPart U=⊤) : U=⊤ := by
 apply Submodule.eq_top_of_finrank_eq
 rw [KroneckerProductSubspaceDimension.dimension,hl,hr]
 simp [Module.finrank_prod]
end KroneckerProductSubspaceExtreme
