import KroneckerGluingKingWeight

/- Original module: KroneckerGluedLinearRepresentation -/
section
set_option autoImplicit false
namespace KroneckerGluedLinearRepresentation
open Module KroneckerLinearCoverBlocks KroneckerGluedSubrepresentations
open KroneckerGluingKingWeight
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[reducible] def gluedSpace {I J : Type} (B : J → LinearCoverBlock) : (I ⊕ (Σ j,(B j).Source)) → Type
  | .inl _ => ℂ
  | .inr p => (B p.1).Space p.2

instance gluedSpaceGroup {I J : Type} (B : J → LinearCoverBlock)
    (s : I ⊕ (Σ j,(B j).Source)) : AddCommGroup (gluedSpace B s) := by
  cases s with
  | inl i => exact inferInstanceAs (AddCommGroup ℂ)
  | inr p => exact inferInstanceAs (AddCommGroup ((B p.1).Space p.2))

instance gluedSpaceModule {I J : Type} (B : J → LinearCoverBlock)
    (s : I ⊕ (Σ j,(B j).Source)) : Module ℂ (gluedSpace B s) := by
  cases s with
  | inl i => exact inferInstanceAs (Module ℂ ℂ)
  | inr p => exact inferInstanceAs (Module ℂ ((B p.1).Space p.2))

instance gluedSpaceFinite {I J : Type} (B : J → LinearCoverBlock)
    (s : I ⊕ (Σ j,(B j).Source)) : FiniteDimensional ℂ (gluedSpace B s) := by
  cases s with
  | inl i => exact inferInstanceAs (FiniteDimensional ℂ ℂ)
  | inr p => exact inferInstanceAs (FiniteDimensional ℂ ((B p.1).Space p.2))

noncomputable def internalArrow {J : Type} (B : J → LinearCoverBlock)
    (p : Σ j,(B j).Source) (q : Σ j,(B j).Sink) : (B p.1).Space p.2 →ₗ[ℂ] ℂ :=
  if h : p.1=q.1 then by
    rcases p with ⟨j,s⟩
    rcases q with ⟨k,t⟩
    dsimp at h
    subst k
    exact (B j).arrow s t
  else 0

@[reducible] noncomputable def gluedBlock {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink) :
    LinearCoverBlock where
  Source := I ⊕ (Σ j,(B j).Source)
  Sink := Σ j,(B j).Sink
  Space := gluedSpace B
  arrow := fun s t => match s with
    | .inl i => if ∃ h : R i t.1,attach i t.1 h=t.2 then LinearMap.id else 0
    | .inr p => internalArrow B p t

theorem internal_arrow_same {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (j : J) (s : (B j).Source) (t : (B j).Sink) :
    (gluedBlock B R attach).arrow (.inr ⟨j,s⟩) ⟨j,t⟩=(B j).arrow s t := by
  simp [gluedBlock,internalArrow]

theorem internal_arrow_other {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    {j k : J} (h : j≠k) (s : (B j).Source) (t : (B k).Sink) :
    (gluedBlock B R attach).arrow (.inr ⟨j,s⟩) ⟨k,t⟩=0 := by
  simp [gluedBlock,internalArrow,h]

theorem connector_arrow {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (i : I) (j : J) (t : (B j).Sink) :
    (gluedBlock B R attach).arrow (.inl i) ⟨j,t⟩=
      if ∃ h : R i j,attach i j h=t then LinearMap.id else 0 := rfl

theorem connector_arrow_at_attachment {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (i : I) (j : J) (h : R i j) :
    (gluedBlock B R attach).arrow (.inl i) ⟨j,attach i j h⟩=LinearMap.id := by
  rw [connector_arrow,ite_eq_left ⟨h,rfl⟩]

theorem glued_representation_dimensions {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink) :
    sourceDimension (gluedBlock B R attach)=totalSource (I:=I) B ∧
      Fintype.card (gluedBlock B R attach).Sink=totalSink B := by
  simp [sourceDimension,gluedBlock,gluedSpace,totalSource,totalSink,Fintype.sum_sum_type,
    Fintype.sum_sigma,Fintype.card_sigma,add_comm]

end KroneckerGluedLinearRepresentation
end

/- Original module: KroneckerGluedSubrepEquivalence -/
section
set_option autoImplicit false
namespace KroneckerGluedSubrepEquivalence
open Module KroneckerLinearCoverBlocks KroneckerGluedSubrepresentations
open KroneckerGluedLinearRepresentation KroneckerPositiveGluedStability KroneckerGluingKingWeight
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def groupSubrep {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : BlockSubrep (gluedBlock B R attach)) : GluedSubrep B R attach where
  block := fun j => {
    source := fun s => S.source (.inr ⟨j,s⟩)
    sink := fun t => S.sink ⟨j,t⟩
    invariant := by
      intro s t x hx
      have hi := S.invariant (.inr ⟨j,s⟩) ⟨j,t⟩ x hx
      rw [internal_arrow_same] at hi
      exact hi }
  connector := fun i => S.source (.inl i)
  attachment := by
    intro i j h x hx
    have hi := S.invariant (.inl i) ⟨j,attach i j h⟩ x hx
    rw [connector_arrow_at_attachment] at hi
    exact hi

def flattenSubrep {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) : BlockSubrep (gluedBlock B R attach) where
  source := fun s => match s with
    | .inl i => S.connector i
    | .inr p => (S.block p.1).source p.2
  sink := fun t => (S.block t.1).sink t.2
  invariant := by
    intro s t x hx
    rcases t with ⟨j,t⟩
    cases s with
    | inl i =>
      rw [connector_arrow]
      split_ifs with h
      · obtain ⟨hR,ht⟩ := h
        subst t
        exact S.attachment i j hR x hx
      · exact Submodule.zero_mem _
    | inr p =>
      rcases p with ⟨k,s⟩
      by_cases h : k=j
      · subst k
        rw [internal_arrow_same]
        exact (S.block j).invariant s t x hx
      · rw [internal_arrow_other B R attach h]
        exact Submodule.zero_mem _

theorem block_subrep_ext {B : LinearCoverBlock} {S T : BlockSubrep B}
    (hu : S.source=T.source) (hv : S.sink=T.sink) : S=T := by
  cases S
  cases T
  cases hu
  cases hv
  rfl

theorem glued_subrep_ext {I J : Type}
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    {S T : GluedSubrep B R attach} (hb : S.block=T.block) (hc : S.connector=T.connector) : S=T := by
  cases S
  cases T
  cases hb
  cases hc
  rfl

def gluedSubrepEquiv {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink) :
    GluedSubrep B R attach ≃ BlockSubrep (gluedBlock B R attach) where
  toFun := flattenSubrep
  invFun := groupSubrep
  left_inv := by
    intro S
    apply glued_subrep_ext
    · funext j
      exact block_subrep_ext rfl rfl
    · rfl
  right_inv := by
    intro S
    apply block_subrep_ext
    · funext s
      cases s <;> rfl
    · rfl

theorem flattened_source_size {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) : sourceSize (flattenSubrep S)=gluedSourceSize S := by
  change (∑ s : I ⊕ (Σ j,(B j).Source),finrank ℂ ((flattenSubrep S).source s))=gluedSourceSize S
  rw [Fintype.sum_sum_type]
  change (∑ i,finrank ℂ (S.connector i))+
    (∑ p : Σ j,(B j).Source,finrank ℂ ((S.block p.1).source p.2))=gluedSourceSize S
  rw [connector_dimension_sum,Fintype.sum_sigma]
  simp [gluedSourceSize,sourceSize,add_comm]

theorem flattened_sink_size {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) : sinkSize (flattenSubrep S)=gluedSinkSize S := by
  change (∑ p : Σ j,(B j).Sink,finrank ℂ ((S.block p.1).sink p.2))=gluedSinkSize S
  rw [Fintype.sum_sigma]
  rfl

def BlockKingStable (B : LinearCoverBlock) : Prop := ∀ S : BlockSubrep B,
  0<sourceSize S+sinkSize S → sourceSize S+sinkSize S<sourceDimension B+Fintype.card B.Sink →
  Fintype.card B.Sink*sourceSize S<sourceDimension B*sinkSize S

theorem global_stability_iff {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink) :
    BlockKingStable (gluedBlock B R attach) ↔ KingStable B R attach := by
  have hd := glued_representation_dimensions B R attach
  constructor
  · intro h S
    simpa only [flattened_source_size,flattened_sink_size,hd.1,hd.2] using h (flattenSubrep S)
  · intro h T
    obtain ⟨S,rfl⟩ := (gluedSubrepEquiv B R attach).surjective T
    simpa only [gluedSubrepEquiv,Equiv.coe_fn_mk,flattened_source_size,flattened_sink_size,hd.1,hd.2]
      using h S

end KroneckerGluedSubrepEquivalence
end
