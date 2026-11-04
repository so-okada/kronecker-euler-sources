import KroneckerReflectionFaithfulness

set_option autoImplicit false
noncomputable section
namespace KroneckerBipartiteQuiverBlock
open KroneckerReflectionKernel KroneckerReflectionReindexing
open KroneckerReflectedLinearBlock
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- A finite bipartite quiver. Parallel arrows are separate elements of Arrow. -/
structure Quiver where
  Source : Type
  Sink : Type
  Arrow : Source → Sink → Type
  [sourceFinite : Fintype Source]
  [sinkFinite : Fintype Sink]
  [outgoingFinite : ∀ s, Fintype (Σ t, Arrow s t)]

attribute [instance] Quiver.sourceFinite Quiver.sinkFinite Quiver.outgoingFinite

/-- A representation of Q whose sink spaces are C. -/
structure Representation (Q : Quiver) where
  Space : Q.Source → Type
  [sourceGroup : ∀ s, AddCommGroup (Space s)]
  [sourceModule : ∀ s, Module ℂ (Space s)]
  [sourceDimension : ∀ s, FiniteDimensional ℂ (Space s)]
  arrow : ∀ s t, Q.Arrow s t → (Space s →ₗ[ℂ] ℂ)

attribute [instance] Representation.sourceGroup Representation.sourceModule
attribute [instance] Representation.sourceDimension

/-- Definition 7.20: the zero-sum representation of a finite bipartite quiver. -/
@[reducible] def ZS (Q : Quiver) : Representation Q where
  Space := fun s => Kernel (Σ t, Q.Arrow s t)
  arrow := fun _ t a => projection ⟨t,a⟩

theorem ZS_arrow_apply (Q : Quiver) (s : Q.Source) (t : Q.Sink)
    (a : Q.Arrow s t) (x : (ZS Q).Space s) : (ZS Q).arrow s t a x = x.val ⟨t,a⟩ := rfl

theorem ZS_zero_sum (Q : Quiver) (s : Q.Source) (x : (ZS Q).Space s) :
    ∑ a : (Σ t, Q.Arrow s t), (ZS Q).arrow s a.1 a.2 x = 0 := x.property

theorem ZS_source_dimension (Q : Quiver) (s : Q.Source)
    [Nonempty (Σ t, Q.Arrow s t)] :
    Module.finrank ℂ ((ZS Q).Space s) + 1 = Fintype.card (Σ t, Q.Arrow s t) :=
  reflection_kernel_dimension _

/-- The quiver whose arrows reverse the incidence relation R. -/
@[reducible] def incidenceQuiver {I J : Type} [Fintype I] [Fintype J] (R : I → J → Prop) : Quiver where
  Source := J
  Sink := I
  Arrow := fun j i => PLift (R i j)
  outgoingFinite := fun _ => inferInstance

def outgoingEquiv {I J : Type} [Fintype I] [Fintype J] (R : I → J → Prop) (j : J) :
    (Σ i, (incidenceQuiver R).Arrow j i) ≃ {i // R i j} where
  toFun a := ⟨a.1,a.2.down⟩
  invFun i := ⟨i.val,⟨i.property⟩⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro i; cases i; rfl

def reflected_space_equiv {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) (j : J) :
    (ZS (incidenceQuiver R)).Space j ≃ₗ[ℂ] (reflectedBlock R).Space j :=
  kernelEquiv (outgoingEquiv R j)

theorem reflected_arrow_agrees {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) (j : J) (i : I) (h : R i j)
    (x : (ZS (incidenceQuiver R)).Space j) :
    (reflectedBlock R).arrow j i (reflected_space_equiv R j x) =
      (ZS (incidenceQuiver R)).arrow j i ⟨h⟩ x := by
  have he := kernel_equiv_projection (outgoingEquiv R j) ⟨i,⟨h⟩⟩ x
  simp only [reflectedBlock, h, reduceDIte]
  exact he

end KroneckerBipartiteQuiverBlock
