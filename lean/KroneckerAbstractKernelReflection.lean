import KroneckerAbstractIncomingNaturality

/-! Global sink reflection on actual morphisms: the induced map between
incoming kernels commutes with every reflected projection arrow. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractKernelReflection
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

abbrev Kernel (R : Rep m V W) := LinearMap.ker (incoming R)

def reflection (R : Rep m V W) : Rep m (Kernel R) V :=
  fun i => (LinearMap.proj i).comp (Kernel R).subtype

def kernelMap {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) : Kernel R →ₗ[ℂ] Kernel S where
  toFun x := ⟨diagonal f.source x.val,by
    change incoming S (diagonal f.source x.val)=0
    rw [←naturality f x.val,show incoming R x.val=0 from x.property,map_zero]⟩
  map_add' x y := Subtype.ext ((diagonal f.source).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((diagonal f.source).map_smul c x.val)

def map {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) : Hom (reflection R) (reflection S) :=
  ⟨kernelMap f,f.source,fun _ _ => rfl⟩

end KroneckerAbstractKernelReflection
