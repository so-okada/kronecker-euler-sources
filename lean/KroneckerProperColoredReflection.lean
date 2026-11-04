import KroneckerReflectedSourceGeneration

set_option autoImplicit false
namespace KroneckerProperColoredReflection
open Module KroneckerReflectionKernel KroneckerSupportedReflectionKernel
attribute [local instance] Classical.propDecidable

structure ProperColoring {I J : Type*} (R : I → J → Prop) where
  color : ∀ i j,R i j → Fin 3
  at_source : ∀ i,Function.Injective (fun j : {j // R i j} => color i j j.2)
  at_sink : ∀ j,Function.Injective (fun i : {i // R i j} => color i j i.2)

theorem colored_sink_degree_le_three {I J : Type*} [Fintype I]
    {R : I → J → Prop} (C : ProperColoring R) (j : J) : Fintype.card {i // R i j}≤3 := by
  simpa using Fintype.card_le_of_injective _ (C.at_sink j)

theorem colored_reflection_dimensions {I J : Type*} [Fintype I]
    {R : I → J → Prop} (C : ProperColoring R) (j : J)
    (h : 0<finrank ℂ (Kernel {i // R i j})) :
    (finrank ℂ (Kernel {i // R i j})=1 ∧ Fintype.card {i // R i j}=2) ∨
      (finrank ℂ (Kernel {i // R i j})=2 ∧ Fintype.card {i // R i j}=3) := by
  have hd := colored_sink_degree_le_three C j
  have he := kernel_dimension_all {i // R i j}
  omega

theorem reflected_zero_iff_leaf {I J : Type*} [Fintype I]
    (R : I → J → Prop) (j : J) (hp : 0<Fintype.card {i // R i j}) :
    finrank ℂ (Kernel {i // R i j})=0 ↔ Fintype.card {i // R i j}=1 := by
  rw [kernel_dimension_all]
  omega

end KroneckerProperColoredReflection
