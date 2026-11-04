import KroneckerAbstractCokernelReflection
import KroneckerPairIsoOfInverse

/- Original module: KroneckerCokernelReflectionFunctorLaws -/
section
/-! The source-cokernel construction respects actual morphism identities and
composition. Quotient representatives are checked explicitly. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCokernelReflectionFunctorLaws
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality KroneckerAbstractOutgoingNaturality
open KroneckerAbstractCokernelReflection
variable {m : ℕ} {V W V' W' V'' W'' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
  [AddCommGroup V''] [Module ℂ V''] [AddCommGroup W''] [Module ℂ W'']

theorem identity_map (R : Rep m V W) : map (identity R)=identity (reflection R) := by
  apply hom_ext
  · rfl
  · apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (outgoing R)) y
    rfl

theorem composition_map {R : Rep m V W} {S : Rep m V' W'} {T : Rep m V'' W''}
    (g : Hom S T) (f : Hom R S) : map (comp g f)=comp (map g) (map f) := by
  apply hom_ext
  · rfl
  · apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (outgoing R)) y
    rfl
end KroneckerCokernelReflectionFunctorLaws
end
end

/- Original module: KroneckerCokernelReflectionIso -/
section
/-! The inverse source-cokernel reflection preserves actual representation
isomorphisms, by its verified functor laws and explicit inverse morphisms. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCokernelReflectionIso
open KroneckerAbstractPairHom KroneckerAbstractPairIso KroneckerAbstractCokernelReflection
open KroneckerCokernelReflectionFunctorLaws
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

def reflectedIso {R : Rep m V W} {S : Rep m V' W'} (e : Iso R S) : Iso (reflection R) (reflection S) := by
  apply KroneckerPairIsoOfInverse.ofInverse (map (toHom e)) (map (toHom (symm e)))
  · rw [←composition_map,hom_symm_left,identity_map]
  · rw [←composition_map,hom_symm_right,identity_map]
end KroneckerCokernelReflectionIso
end
end
