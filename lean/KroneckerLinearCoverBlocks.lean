import KroneckerReflectedSourceGeneration

set_option autoImplicit false
namespace KroneckerLinearCoverBlocks
open Module
open scoped BigOperators

/-- A finite bipartite linear representation with one-dimensional sink spaces.
Zero maps may be used away from the support. -/
structure LinearCoverBlock where
  Source : Type
  Sink : Type
  [sourceFinite : Fintype Source]
  [sinkFinite : Fintype Sink]
  Space : Source → Type
  [sourceGroup : ∀ s,AddCommGroup (Space s)]
  [sourceModule : ∀ s,Module ℂ (Space s)]
  [sourceDimension : ∀ s,FiniteDimensional ℂ (Space s)]
  arrow : ∀ s,Sink → (Space s →ₗ[ℂ] ℂ)

attribute [instance] LinearCoverBlock.sourceFinite LinearCoverBlock.sinkFinite
attribute [instance] LinearCoverBlock.sourceGroup LinearCoverBlock.sourceModule
attribute [instance] LinearCoverBlock.sourceDimension

structure BlockSubrep (B : LinearCoverBlock) where
  source : ∀ s,Submodule ℂ (B.Space s)
  sink : B.Sink → Submodule ℂ ℂ
  invariant : ∀ s t x,x∈source s → B.arrow s t x∈sink t

noncomputable def sourceDimension (B : LinearCoverBlock) : ℕ := ∑ s,finrank ℂ (B.Space s)
noncomputable def sourceSize {B : LinearCoverBlock} (S : BlockSubrep B) : ℕ :=
  ∑ s,finrank ℂ (S.source s)
noncomputable def sinkSize {B : LinearCoverBlock} (S : BlockSubrep B) : ℕ :=
  ∑ t,finrank ℂ (S.sink t)

def PositiveDefect (B : LinearCoverBlock) : Prop :=
  ∀ S : BlockSubrep B,0<sourceSize S+sinkSize S → sourceSize S<sinkSize S

def fullBlock (B : LinearCoverBlock) : BlockSubrep B where
  source := fun _ => ⊤
  sink := fun _ => ⊤
  invariant := by intros; trivial

def zeroBlock (B : LinearCoverBlock) : BlockSubrep B where
  source := fun _ => ⊥
  sink := fun _ => ⊥
  invariant := by intro s t x hx; simpa using congrArg (B.arrow s t) hx

theorem block_source_bound {B : LinearCoverBlock} (S : BlockSubrep B) :
    sourceSize S≤sourceDimension B := by
  exact Finset.sum_le_sum (fun s _ => (S.source s).finrank_le)


set_option backward.isDefEq.respectTransparency false in
theorem full_block_dimensions (B : LinearCoverBlock) :
    sourceSize (fullBlock B)=sourceDimension B ∧
      sinkSize (fullBlock B)=Fintype.card B.Sink := by
  simp [sourceSize,sinkSize,sourceDimension,fullBlock]

set_option backward.isDefEq.respectTransparency false in
theorem zero_block_dimensions (B : LinearCoverBlock) :
    sourceSize (zeroBlock B)=0 ∧ sinkSize (zeroBlock B)=0 := by
  simp [sourceSize,sinkSize,zeroBlock]

end KroneckerLinearCoverBlocks
