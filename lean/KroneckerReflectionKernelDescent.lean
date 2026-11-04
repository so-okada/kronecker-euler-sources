import KroneckerAbstractKernelReflection
import KroneckerSurjectiveLinearDescent

/-! A morphism between reflected representations preserves the original
incoming kernels, by equality of every coordinate projection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionKernelDescent
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality KroneckerAbstractKernelReflection
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

theorem coordinates {R : Rep m V W} {S : Rep m V' W'}
    (g : Hom (reflection R) (reflection S)) (x : Kernel R) :
    diagonal g.sink x.val=(g.source x).val := by
  funext i
  exact g.commutes i x

theorem kernel_preserved {R : Rep m V W} {S : Rep m V' W'}
    (g : Hom (reflection R) (reflection S)) :
    LinearMap.ker (incoming R)≤LinearMap.ker ((incoming S).comp (diagonal g.sink)) := by
  intro x hx
  change incoming S (diagonal g.sink x)=0
  rw [coordinates g ⟨x,hx⟩]
  exact (g.source ⟨x,hx⟩).property

theorem diagonal_single (f : V →ₗ[ℂ] V') (i : Fin m) (x : V) :
    diagonal f (Pi.single i x)=Pi.single i (f x) := by
  classical
  funext j
  by_cases h : i=j
  · subst j
    simp [diagonal]
  · simp [diagonal,h]
end KroneckerReflectionKernelDescent
