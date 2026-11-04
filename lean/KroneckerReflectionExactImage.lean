import KroneckerAbstractCokernelReflection

/-! Reflected representations land in the correct exactness classes:
kernel reflection has injective outgoing map, and cokernel reflection has surjective incoming map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionExactImage
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality KroneckerAbstractOutgoingNaturality
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem kernel_outgoing (R : Rep m V W) :
    outgoing (KroneckerAbstractKernelReflection.reflection R)=(KroneckerAbstractKernelReflection.Kernel R).subtype := rfl


theorem cokernel_incoming (R : Rep m V W) :
    incoming (KroneckerAbstractCokernelReflection.reflection R)=KroneckerAbstractCokernelReflection.quotient R := by
  apply LinearMap.ext
  intro x
  change (∑ i : Fin m,KroneckerAbstractCokernelReflection.quotient R (Pi.single i (x i)))=_
  rw [←map_sum]
  congr 1
  funext i
  simp [Pi.single_apply]

theorem cokernel_incoming_surjective (R : Rep m V W) :
    Function.Surjective (incoming (KroneckerAbstractCokernelReflection.reflection R)) := by
  rw [cokernel_incoming]
  exact Submodule.mkQ_surjective _
end KroneckerReflectionExactImage
