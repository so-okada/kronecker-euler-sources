import KroneckerAbstractKernelReflection

/- Original module: KroneckerKernelReflectionFunctorLaws -/
section
/-! Sink reflection respects identity and composition of actual morphisms,
so its behavior on isomorphism classes is functorial rather than choice-dependent. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerKernelReflectionFunctorLaws
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality KroneckerAbstractKernelReflection
variable {m : ℕ} {V W V' W' V'' W'' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
  [AddCommGroup V''] [Module ℂ V''] [AddCommGroup W''] [Module ℂ W'']

theorem identity_map (R : Rep m V W) : map (identity R)=identity (reflection R) := by
  apply hom_ext
  · ext x
    rfl
  · rfl

theorem composition_map {R : Rep m V W} {S : Rep m V' W'} {T : Rep m V'' W''}
    (g : Hom S T) (f : Hom R S) : map (comp g f)=comp (map g) (map f) := by
  apply hom_ext
  · ext x
    rfl
  · rfl
end KroneckerKernelReflectionFunctorLaws
end
end

/- Original module: KroneckerKernelReflectionIso -/
section
/-! Every actual representation isomorphism induces a linear isomorphism
between the reflection kernels and an isomorphism of the reflected representations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerKernelReflectionIso
open KroneckerAbstractPairHom KroneckerAbstractPairIso
open KroneckerAbstractIncomingNaturality KroneckerAbstractKernelReflection
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

def kernelEquiv {R : Rep m V W} {S : Rep m V' W'} (e : Iso R S) : Kernel R ≃ₗ[ℂ] Kernel S where
  toFun := kernelMap (toHom e)
  invFun := kernelMap (toHom (symm e))
  left_inv x := by
    apply Subtype.ext
    funext i
    exact e.source.symm_apply_apply (x.val i)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact e.source.apply_symm_apply (x.val i)
  map_add' := (kernelMap (toHom e)).map_add
  map_smul' := (kernelMap (toHom e)).map_smul

def reflectedIso {R : Rep m V W} {S : Rep m V' W'} (e : Iso R S) : Iso (reflection R) (reflection S) :=
  ⟨kernelEquiv e,e.source,fun _ _ => rfl⟩

end KroneckerKernelReflectionIso
end
end
