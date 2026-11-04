import KroneckerLinearCoverBlocks

set_option autoImplicit false
namespace KroneckerReflectedLinearBlock
open SimpleGraph Module KroneckerBipartiteIncidence KroneckerReflectionKernel
open KroneckerLinearCoverBlocks KroneckerReflectedSubrepresentations
open KroneckerSaturatedTreeDimensions KroneckerReflectedBlockStability
open KroneckerReflectedSourceGeneration
attribute [local instance] Classical.propDecidable

@[reducible] noncomputable def reflectedBlock {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) : LinearCoverBlock where
  Source := J
  Sink := I
  Space := fun j => Kernel {i // R i j}
  arrow := fun j i => if h : R i j then projection ⟨i,h⟩ else 0

def toReflectedSubrep {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (S : BlockSubrep (reflectedBlock R)) : ReflectedSubrep R where
  source := S.source
  sink := S.sink
  invariant := by
    intro j i h x hx
    simpa [reflectedBlock,h] using S.invariant j i x hx

def fromReflectedSubrep {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (S : ReflectedSubrep R) : BlockSubrep (reflectedBlock R) where
  source := S.source
  sink := S.sink
  invariant := by
    intro j i x hx
    by_cases h : R i j
    · simpa [reflectedBlock,h] using S.invariant j i h x hx
    · simp [reflectedBlock,h]

def reflectedSubrepEquiv {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) : BlockSubrep (reflectedBlock R) ≃ ReflectedSubrep R where
  toFun := toReflectedSubrep
  invFun := fromReflectedSubrep
  left_inv := by intro S; cases S; rfl
  right_inv := by intro S; cases S; rfl

theorem reflected_positive_defect {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) : PositiveDefect (reflectedBlock R) := by
  intro S hS
  exact reflected_subrepresentation_defect hT h3 (toReflectedSubrep S) hS

theorem reflected_total_source {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) :
    sourceDimension (reflectedBlock R)=Fintype.card I-1 := by
  have h := reflected_source_dimension R hT h3
  change (∑ j,finrank ℂ (Kernel {i // R i j}))=Fintype.card I-1
  omega

theorem reflected_arrows_generate {I J : Type} [Fintype I] [Fintype J] [Nontrivial I]
    (R : I → J → Prop) (hc : (incidenceGraph R).Connected) (i : I) :
    ∃ j,Function.Surjective ((reflectedBlock R).arrow j i) := by
  obtain ⟨j,h,hp⟩ := full_sources_generate_sink R hc i
  exact ⟨j,by simpa [reflectedBlock,h] using hp⟩

end KroneckerReflectedLinearBlock
