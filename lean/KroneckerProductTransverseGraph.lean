import KroneckerProductSubspaceParts

/- Original module: KroneckerProductTransverseProjection -/
section
/-! A transverse subspace projecting fully is linearly isomorphic to the quotient endpoint. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProductTransverseProjection
open KroneckerProductSubspaceParts
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def project (U : Submodule ℂ (V×W)) : U →ₗ[ℂ] W := (LinearMap.snd ℂ V W).comp U.subtype
theorem injective (U : Submodule ℂ (V×W)) (hl : leftPart U=⊥) : Function.Injective (project U) := by
 apply LinearMap.ker_eq_bot.mp
 apply le_antisymm _ bot_le
 intro x hx
 have hz : x.val.2=0 := hx
 have hmem : x.val.1∈leftPart U := by change (x.val.1,0)∈U;rw [← hz];exact x.property
 rw [hl] at hmem
 have hx0 : x.val.1=0 := hmem
 change x=0
 apply Subtype.ext;exact Prod.ext hx0 hz
theorem surjective (U : Submodule ℂ (V×W)) (hr : rightPart U=⊤) : Function.Surjective (project U) := by
 intro y
 have h : y∈rightPart U := by rw [hr];trivial
 obtain ⟨x,hx⟩ := (mem_right U y).mp h
 exact ⟨⟨(x,y),hx⟩,rfl⟩
def equivalence (U : Submodule ℂ (V×W)) (hl : leftPart U=⊥) (hr : rightPart U=⊤) : U ≃ₗ[ℂ] W :=
 LinearEquiv.ofBijective (project U) ⟨injective U hl,surjective U hr⟩
end KroneckerProductTransverseProjection
end
end

/- Original module: KroneckerProductTransverseGraph -/
section
/-! Every transverse full-projection subspace is a graph, with a canonical linear graph map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProductTransverseGraph
open KroneckerProductSubspaceParts KroneckerProductTransverseProjection
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
def graphMap (U : Submodule ℂ (V×W)) (hl : leftPart U=⊥) (hr : rightPart U=⊤) : W →ₗ[ℂ] V :=
 (LinearMap.fst ℂ V W).comp (U.subtype.comp (equivalence U hl hr).symm.toLinearMap)
theorem graph_mem (U : Submodule ℂ (V×W)) (hl : leftPart U=⊥) (hr : rightPart U=⊤) (y : W) :
 (graphMap U hl hr y,y)∈U := by
 have h := ((equivalence U hl hr).symm y).property
 have hy : ((equivalence U hl hr).symm y).val.2=y := (equivalence U hl hr).apply_symm_apply y
 change (((equivalence U hl hr).symm y).val.1,y)∈U
 have he : (((equivalence U hl hr).symm y).val.1,y)=((equivalence U hl hr).symm y).val := Prod.ext rfl hy.symm
 rw [he];exact h
theorem unique (U : Submodule ℂ (V×W)) (hl : leftPart U=⊥) (hr : rightPart U=⊤)
 (x : V) (y : W) (h : (x,y)∈U) : x=graphMap U hl hr y := by
 have he : (⟨(x,y),h⟩ : U)=(equivalence U hl hr).symm y := by
  apply (equivalence U hl hr).injective
  exact ((equivalence U hl hr).apply_symm_apply y).symm
 exact congrArg (fun q : U => q.val.1) he
end KroneckerProductTransverseGraph
end
end
