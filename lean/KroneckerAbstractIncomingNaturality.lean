import KroneckerAbstractPairIso

/-! Incoming sum maps commute with all actual representation morphisms.
This is the functorial identity needed to map reflection kernels. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractIncomingNaturality
open KroneckerAbstractPairHom
open scoped BigOperators
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

def incoming (R : Rep m V W) : (Fin m → V) →ₗ[ℂ] W where
  toFun x := ∑ i,R i (x i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum]

def diagonal (f : V →ₗ[ℂ] V') : (Fin m → V) →ₗ[ℂ] (Fin m → V') :=
  LinearMap.pi (fun i => f.comp (LinearMap.proj i))

theorem naturality {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) (x : Fin m → V) :
    f.sink (incoming R x)=incoming S (diagonal f.source x) := by
  simp only [incoming,LinearMap.coe_mk,AddHom.coe_mk,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact f.commutes i (x i)

theorem single (R : Rep m V W) (i : Fin m) (x : V) : incoming R (Pi.single i x)=R i x := by
  classical
  simp [incoming,Pi.single_apply,apply_ite]

theorem diagonal_identity : diagonal (m:=m) (LinearMap.id : V →ₗ[ℂ] V)=LinearMap.id := rfl
end KroneckerAbstractIncomingNaturality
