import KroneckerReflectionExactImage

/-! Applying sink-kernel reflection after source-cokernel reflection recovers
an outgoing-injective representation, via the actual image inside its coordinate space. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerKernelCokernelReconstruction
open KroneckerAbstractPairHom KroneckerAbstractPairIso
open KroneckerAbstractIncomingNaturality KroneckerAbstractOutgoingNaturality
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def sourceMap (R : Rep m V W) : V →ₗ[ℂ]
    KroneckerAbstractKernelReflection.Kernel (KroneckerAbstractCokernelReflection.reflection R) where
  toFun x := ⟨outgoing R x,by
    change incoming (KroneckerAbstractCokernelReflection.reflection R) (outgoing R x)=0
    rw [KroneckerReflectionExactImage.cokernel_incoming]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩⟩
  map_add' x y := Subtype.ext ((outgoing R).map_add x y)
  map_smul' c x := Subtype.ext ((outgoing R).map_smul c x)

theorem sourceMap_bijective (R : Rep m V W) (hR : Function.Injective (outgoing R)) :
    Function.Bijective (sourceMap R) := by
  constructor
  · intro x y h
    apply hR
    exact congrArg Subtype.val h
  · intro y
    have hy := y.property
    change incoming (KroneckerAbstractCokernelReflection.reflection R) y.val=0 at hy
    rw [KroneckerReflectionExactImage.cokernel_incoming] at hy
    obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
    exact ⟨x,Subtype.ext hx⟩

def sourceEquiv (R : Rep m V W) (hR : Function.Injective (outgoing R)) :
    V ≃ₗ[ℂ] KroneckerAbstractKernelReflection.Kernel (KroneckerAbstractCokernelReflection.reflection R) :=
  LinearEquiv.ofBijective (sourceMap R) (sourceMap_bijective R hR)

def reconstruction (R : Rep m V W) (hR : Function.Injective (outgoing R)) :
    Iso R (KroneckerAbstractKernelReflection.reflection (KroneckerAbstractCokernelReflection.reflection R)) where
  source := sourceEquiv R hR
  sink := LinearEquiv.refl ℂ W
  commutes _ _ := rfl
end KroneckerKernelCokernelReconstruction
