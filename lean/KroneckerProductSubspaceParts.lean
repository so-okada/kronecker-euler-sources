import KroneckerAbstractPairHom

/-! Intersection and projection parts of a subspace of a split extension. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProductSubspaceParts
open Module
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def leftPart (U : Submodule ℂ (V×W)) : Submodule ℂ V := U.comap (LinearMap.inl ℂ V W)
def rightPart (U : Submodule ℂ (V×W)) : Submodule ℂ W := U.map (LinearMap.snd ℂ V W)
theorem mem_right (U : Submodule ℂ (V×W)) (y : W) : y∈rightPart U ↔ ∃ x : V,(x,y)∈U := by
 constructor
 · rintro ⟨⟨x,z⟩,h,rfl⟩;exact ⟨x,h⟩
 · rintro ⟨x,h⟩;exact ⟨(x,y),h,rfl⟩
end KroneckerProductSubspaceParts
