import KroneckerReflectedLinearBlock
import KroneckerGluedSubrepEquivalence

section

set_option autoImplicit false
namespace KroneckerRetainedReflectionKernels
open Module KroneckerReflectionKernel KroneckerSupportedReflectionKernel
open KroneckerLinearCoverBlocks
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Retained {I J : Type*} [Fintype I] (R : I → J → Prop) :=
  {j : J // 2≤Fintype.card {i // R i j}}

theorem retained_iff_kernel_positive {I J : Type*} [Fintype I]
    (R : I → J → Prop) (j : J) :
    2≤Fintype.card {i // R i j} ↔ 0<finrank ℂ (Kernel {i // R i j}) := by
  rw [kernel_dimension_all]
  omega

theorem omitted_kernel_zero {I J : Type*} [Fintype I]
    (R : I → J → Prop) (j : J) (h : ¬2≤Fintype.card {i // R i j}) :
    finrank ℂ (Kernel {i // R i j})=0 := by
  rw [kernel_dimension_all]
  omega

theorem omitted_subspace_zero {I J : Type*} [Fintype I]
    (R : I → J → Prop) (j : J) (h : ¬2≤Fintype.card {i // R i j})
    (U : Submodule ℂ (Kernel {i // R i j})) : U=⊥ := by
  have hu := U.finrank_le
  rw [omitted_kernel_zero R j h] at hu
  exact Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hu)

@[reducible] noncomputable def retainedBlock {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) : LinearCoverBlock where
  Source := Retained R
  Sink := I
  Space := fun j => Kernel {i // R i j.1}
  arrow := fun j i => if h : R i j.1 then projection ⟨i,h⟩ else 0

/-- Removing zero-dimensional reflected sources preserves their total dimension. -/
theorem retained_total_dimension {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) :
    sourceDimension (retainedBlock R)=
      sourceDimension (KroneckerReflectedLinearBlock.reflectedBlock R) := by
  classical
  change (∑ j : Retained R,finrank ℂ (Kernel {i // R i j.1}))=
    ∑ j,finrank ℂ (Kernel {i // R i j})
  rw [←Finset.sum_subtype (Finset.univ.filter (fun j => 2≤Fintype.card {i // R i j}))
    (p:=fun j : J => 2≤Fintype.card {i // R i j}) (F:=inferInstance) (by simp)
    (fun j : J => finrank ℂ (Kernel {i // R i j}))]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  exact omitted_kernel_zero R j (by simpa using hj)

end KroneckerRetainedReflectionKernels
end

section

set_option autoImplicit false
namespace KroneckerRetainedSubrepresentations
open Module KroneckerLinearCoverBlocks KroneckerReflectedLinearBlock
open KroneckerRetainedReflectionKernels KroneckerGluedSubrepEquivalence
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def restrictSubrep {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (S : BlockSubrep (reflectedBlock R)) : BlockSubrep (retainedBlock R) where
  source := fun j => S.source j.1
  sink := S.sink
  invariant := fun j i x hx => S.invariant j.1 i x hx

noncomputable def extendSubrep {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (S : BlockSubrep (retainedBlock R)) : BlockSubrep (reflectedBlock R) where
  source := fun j => if h : 2≤Fintype.card {i // R i j} then S.source ⟨j,h⟩ else ⊥
  sink := S.sink
  invariant := by
    intro j i x hx
    by_cases h : 2≤Fintype.card {i // R i j}
    · have hx' : x∈S.source ⟨j,h⟩ := by simpa [h] using hx
      exact S.invariant ⟨j,h⟩ i x hx'
    · have hx0 : x=0 := by simpa [h] using hx
      subst x
      simp

noncomputable def retainedSubrepEquiv {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) : BlockSubrep (reflectedBlock R) ≃ BlockSubrep (retainedBlock R) where
  toFun := restrictSubrep
  invFun := extendSubrep
  left_inv := by
    intro S
    apply block_subrep_ext
    · funext j
      by_cases h : 2≤Fintype.card {i // R i j}
      · simp [extendSubrep,restrictSubrep,h]
      · simp [extendSubrep,restrictSubrep,h,omitted_subspace_zero R j h (S.source j)]
    · rfl
  right_inv := by
    intro S
    apply block_subrep_ext
    · funext j
      simp only [restrictSubrep,extendSubrep,dite_eq_left j.2]
    · rfl

theorem restricted_source_size {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (S : BlockSubrep (reflectedBlock R)) :
    sourceSize (restrictSubrep S)=sourceSize S := by
  classical
  change (∑ j : Retained R,finrank ℂ (S.source j.1))=∑ j,finrank ℂ (S.source j)
  rw [←Finset.sum_subtype (Finset.univ.filter (fun j => 2≤Fintype.card {i // R i j}))
    (p:=fun j : J => 2≤Fintype.card {i // R i j}) (F:=inferInstance) (by simp)
    (fun j : J => finrank ℂ (S.source j))]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro j _ hj
  rw [omitted_subspace_zero R j (by simpa using hj) (S.source j)]
  simp

theorem restricted_sink_size {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (S : BlockSubrep (reflectedBlock R)) :
    sinkSize (restrictSubrep S)=sinkSize S := rfl


theorem retained_defect_iff {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) : PositiveDefect (retainedBlock R) ↔ PositiveDefect (reflectedBlock R) := by
  constructor
  · intro h S
    simpa only [restricted_source_size,restricted_sink_size] using h (restrictSubrep S)
  · intro h T
    obtain ⟨S,rfl⟩ := (retainedSubrepEquiv R).surjective T
    simpa only [retainedSubrepEquiv,Equiv.coe_fn_mk,restricted_source_size,restricted_sink_size]
      using h S

end KroneckerRetainedSubrepresentations
end

