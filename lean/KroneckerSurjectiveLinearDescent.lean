import KroneckerAbstractPairHom
import Mathlib.LinearAlgebra.Isomorphisms

/-! Explicit descent of a linear map through a surjective map when it kills
the kernel, including the evaluation and uniqueness laws used by reflection fullness. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSurjectiveLinearDescent
variable {X Y Z : Type} [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]

def descend (p : X →ₗ[ℂ] Y) (hp : Function.Surjective p) (f : X →ₗ[ℂ] Z)
    (h : LinearMap.ker p≤LinearMap.ker f) : Y →ₗ[ℂ] Z :=
  ((LinearMap.ker p).liftQ f h).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap

theorem evaluate (p : X →ₗ[ℂ] Y) (hp : Function.Surjective p) (f : X →ₗ[ℂ] Z)
    (h : LinearMap.ker p≤LinearMap.ker f) (x : X) : descend p hp f h (p x)=f x := by
  unfold descend
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [←p.quotKerEquivOfSurjective_apply_mk hp x,LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]

theorem unique (p : X →ₗ[ℂ] Y) (hp : Function.Surjective p) (f : X →ₗ[ℂ] Z)
    (h : LinearMap.ker p≤LinearMap.ker f) (g : Y →ₗ[ℂ] Z) (hg : ∀ x,g (p x)=f x) :
    g=descend p hp f h := by
  ext y
  obtain ⟨x,rfl⟩ := hp y
  rw [hg,evaluate]
end KroneckerSurjectiveLinearDescent
