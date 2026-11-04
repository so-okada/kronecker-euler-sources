import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Pi

/- Original module: KroneckerFramedSlopeArithmetic -/
section
set_option autoImplicit false
namespace KroneckerFramedSlopeArithmetic


theorem framed_slope_criterion (c : ℤ) (n D : ℕ) (hn : 0<n) (hnD : n<D)
    (ε : ℝ) (he : 0<ε) (he1 : ε≤1) :
    ((c : ℝ)-ε)/(n : ℝ)< -ε/(D : ℝ) ↔ c≤0 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hDR : (0 : ℝ)<D := by exact_mod_cast (lt_trans hn hnD)
  have hnDR : (n : ℝ)<D := by exact_mod_cast hnD
  rw [div_lt_div_iff₀ hnR hDR]
  constructor
  · intro h
    by_contra hc
    have hcR : (1 : ℝ)≤c := by exact_mod_cast (show 1≤c by omega)
    have hnum : (0 : ℝ)≤(c : ℝ)-ε := by linarith
    nlinarith [mul_nonneg hnum hDR.le,mul_pos he hnR]
  · intro hc
    have hcR : (c : ℝ)≤0 := by exact_mod_cast hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hcR hDR.le,mul_pos he (sub_pos.mpr hnDR)]

end KroneckerFramedSlopeArithmetic
end

/- Original module: KroneckerFramedRepresentationStability -/
section
set_option autoImplicit false
namespace KroneckerFramedRepresentationStability
open Module

abbrev Space (n : ℕ) := Fin n → ℂ

structure Representation (a b : ℕ) where
  arrow : Fin 3 → Space a →ₗ[ℂ] Space b






end KroneckerFramedRepresentationStability
end

/- Original module: KroneckerReflectionKernel -/
section
set_option autoImplicit false
namespace KroneckerReflectionKernel
open Module
open scoped BigOperators

noncomputable def sumMap (ι : Type*) [Fintype ι] : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i,x i
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

noncomputable abbrev Kernel (ι : Type*) [Fintype ι] := LinearMap.ker (sumMap ι)

theorem sumMap_surjective (ι : Type*) [Fintype ι] [Nonempty ι] :
    Function.Surjective (sumMap ι) := by
  classical
  intro c
  let i : ι := Classical.arbitrary ι
  exact ⟨Pi.single i c,by simp [sumMap]⟩

theorem reflection_kernel_dimension (ι : Type*) [Fintype ι] [Nonempty ι] :
    finrank ℂ (Kernel ι)+1=Fintype.card ι := by
  have hr : LinearMap.range (sumMap ι)=⊤ := LinearMap.range_eq_top.mpr (sumMap_surjective ι)
  have h := (sumMap ι).finrank_range_add_finrank_ker
  rw [hr] at h
  simpa [Kernel,add_comm] using h

noncomputable def projection {ι : Type*} [Fintype ι] (i : ι) : Kernel ι →ₗ[ℂ] ℂ :=
  (LinearMap.proj i).comp (Kernel ι).subtype


theorem reflection_projection_surjective {ι : Type*} [Fintype ι]
    (i j : ι) (hij : i≠j) : Function.Surjective (projection i) := by
  classical
  intro c
  let x : ι → ℂ := Pi.single i c-Pi.single j c
  have hx : x∈Kernel ι := by
    change ∑ k,x k=0
    simp [x,Finset.sum_sub_distrib]
  refine ⟨⟨x,hx⟩,?_⟩
  simp [projection,x,hij]

end KroneckerReflectionKernel
end
