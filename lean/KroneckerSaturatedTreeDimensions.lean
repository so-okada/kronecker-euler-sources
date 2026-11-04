import KroneckerReflectionKernel
import KroneckerBipartiteIncidence

/- Original module: KroneckerSupportedReflectionKernel -/
section
set_option autoImplicit false
namespace KroneckerSupportedReflectionKernel
open Module KroneckerReflectionKernel
open scoped BigOperators

theorem kernel_dimension_all (ι : Type*) [Fintype ι] :
    finrank ℂ (Kernel ι)=Fintype.card ι-1 := by
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    let := hi
    have hs := (Kernel ι).finrank_le
    simp only [Module.finrank_pi, Fintype.card_eq_zero] at hs
    simpa using hs
  | inr hi =>
    let := hi
    have h := reflection_kernel_dimension ι
    omega

noncomputable def restrictKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (A : Submodule ℂ (Kernel ι))
    (hA : ∀ x : A,∀ i∉s,(x.1 : ι → ℂ) i=0) : A →ₗ[ℂ] Kernel ↥s where
  toFun x := ⟨fun i => (x.1 : ι → ℂ) i,by
    change ∑ i : s,(x.1 : ι → ℂ) i=0
    rw [Finset.sum_coe_sort]
    have hsum : ∑ i∈s,(x.1 : ι → ℂ) i=∑ i,(x.1 : ι → ℂ) i := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact hA x i hi
    rw [hsum]
    exact x.1.2⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem restrictKernel_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (A : Submodule ℂ (Kernel ι))
    (hA : ∀ x : A,∀ i∉s,(x.1 : ι → ℂ) i=0) :
    Function.Injective (restrictKernel s A hA) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  funext i
  by_cases hi : i∈s
  · exact congrArg (fun v : Kernel ↥s => (v : ↥s → ℂ) ⟨i,hi⟩) h
  · rw [hA x i hi,hA y i hi]

/-- An arbitrary subspace supported on q chosen coordinates has dimension at most q-1. -/
theorem supported_subspace_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (A : Submodule ℂ (Kernel ι))
    (hA : ∀ x : A,∀ i∉s,(x.1 : ι → ℂ) i=0) : finrank ℂ A≤s.card-1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (restrictKernel_injective s A hA)
  simpa [kernel_dimension_all] using h

end KroneckerSupportedReflectionKernel
end

/- Original module: KroneckerSaturatedTreeDimensions -/
section
set_option autoImplicit false
namespace KroneckerSaturatedTreeDimensions
open SimpleGraph Module KroneckerBipartiteIncidence KroneckerReflectionKernel
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem saturated_tree_sink_count {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) : Fintype.card J=2*Fintype.card I+1 := by
  classical
  have he := hT.card_edgeFinset
  have hd := (incidenceGraph R).sum_degrees_eq_twice_card_edges
  rw [incidence_degree_sum] at hd
  simp only [h3,Finset.sum_const,Finset.card_univ,smul_eq_mul,Fintype.card_sum] at he hd
  omega

theorem saturated_sink_degree_positive {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (j : J) : 0<Fintype.card {i // R i j} := by
  haveI : Nontrivial (I ⊕ J) := ⟨⟨.inl (Classical.arbitrary I),.inr j,by simp⟩⟩
  have h := hT.connected.preconnected.degree_pos_of_nontrivial (.inr j)
  simpa [right_degree] using h

/-- Total dimension of the actual reflected source kernels. -/
theorem reflected_source_dimension {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) :
    (∑ j,finrank ℂ (Kernel {i // R i j}))+1=Fintype.card I := by
  have hd : ∀ j,finrank ℂ (Kernel {i // R i j})+1=Fintype.card {i // R i j} := by
    intro j
    haveI : Nonempty {i // R i j} := Fintype.card_pos_iff.mp (saturated_sink_degree_positive R hT j)
    exact reflection_kernel_dimension _
  have hs := congrArg (fun f : J → ℕ => ∑ j,f j) (funext hd)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hs
  rw [←incidence_double_count] at hs
  simp only [h3,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  have hc := saturated_tree_sink_count R hT h3
  omega


end KroneckerSaturatedTreeDimensions
end
