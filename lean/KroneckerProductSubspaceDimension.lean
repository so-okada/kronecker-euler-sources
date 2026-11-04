import KroneckerProductSubspaceParts

/- Original module: KroneckerProductSubspaceProjection -/
section
/-! The restricted extension projection surjects onto its image part. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProductSubspaceProjection
open KroneckerProductSubspaceParts
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def project (U : Submodule ℂ (V×W)) : U →ₗ[ℂ] rightPart U :=
 { toFun := fun x => ⟨x.val.2,⟨x.val,x.property,rfl⟩⟩
   map_add' := fun _ _ => rfl
   map_smul' := fun _ _ => rfl }
theorem surjective (U : Submodule ℂ (V×W)) : Function.Surjective (project U) := by
 intro y; obtain ⟨x,hx⟩ := (mem_right U y.val).mp y.property
 exact ⟨⟨(x,y.val),hx⟩,rfl⟩
end KroneckerProductSubspaceProjection
end
end

/- Original module: KroneckerProductSubspaceKernel -/
section
/-! The restricted projection kernel is precisely the intersection part. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProductSubspaceKernel
open KroneckerProductSubspaceParts KroneckerProductSubspaceProjection
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def equivalence (U : Submodule ℂ (V×W)) : leftPart U ≃ₗ[ℂ] LinearMap.ker (project U) where
 toFun x := ⟨⟨(x.val,0),x.property⟩,rfl⟩
 invFun x := ⟨x.val.val.1,by
  have h : x.val.val.2=0 := congrArg Subtype.val x.property
  change (x.val.val.1,0)∈U
  rw [← h];exact x.val.property⟩
 left_inv _ := rfl
 right_inv x := by
  apply Subtype.ext;apply Subtype.ext
  have h : x.val.val.2=0 := congrArg Subtype.val x.property
  exact Prod.ext rfl h.symm
 map_add' x y := by apply Subtype.ext;apply Subtype.ext;exact Prod.ext rfl (zero_add 0).symm
 map_smul' c x := by apply Subtype.ext;apply Subtype.ext;exact Prod.ext rfl (smul_zero c).symm
end KroneckerProductSubspaceKernel
end
end

/- Original module: KroneckerProductSubspaceDimension -/
section
/-! Exact dimension additivity for arbitrary extension subobjects, not just coordinate subspaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProductSubspaceDimension
open Module KroneckerProductSubspaceParts KroneckerProductSubspaceProjection
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
theorem dimension (U : Submodule ℂ (V×W)) : finrank ℂ U=finrank ℂ (leftPart U)+finrank ℂ (rightPart U) := by
 have h := (project U).finrank_range_add_finrank_ker
 rw [LinearMap.range_eq_top.mpr (surjective U),finrank_top] at h
 rw [← (KroneckerProductSubspaceKernel.equivalence U).finrank_eq] at h
 omega
end KroneckerProductSubspaceDimension
end
end
