import KroneckerSlotIsoTransport

/- Original module: KroneckerReflectedReconstruction -/
section
set_option autoImplicit false
namespace KroneckerReflectedReconstruction
open KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport KroneckerRetainedReflectionKernels
open KroneckerProperColoredReflection KroneckerRetainedVacantSlots KroneckerSlotCompletion
open KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

noncomputable def recoverSink {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3) :
    CompletedSink (retainedBlock R) (retainedColoring C) → J
  | .inl j => j.1
  | .inr p => (actualSlotLeafEquiv C h3 p).1

theorem recover_sink_injective {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3) :
    Function.Injective (recoverSink C h3) := by
  intro a b h
  cases a with
  | inl j => cases b with
    | inl k => exact congrArg Sum.inl (Subtype.ext h)
    | inr p =>
      have hj := j.2
      have hp := (actualSlotLeafEquiv C h3 p).2
      change j.1=(actualSlotLeafEquiv C h3 p).1 at h
      rw [h] at hj
      omega
  | inr p => cases b with
    | inl j =>
      have hj := j.2
      have hp := (actualSlotLeafEquiv C h3 p).2
      change (actualSlotLeafEquiv C h3 p).1=j.1 at h
      rw [←h] at hj
      omega
    | inr q => exact congrArg Sum.inr ((actualSlotLeafEquiv C h3).injective (Subtype.ext h))

theorem recover_sink_surjective {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (hpos : ∀ j,0<Fintype.card {i // R i j}) : Function.Surjective (recoverSink C h3) := by
  intro j
  by_cases hj : 2≤Fintype.card {i // R i j}
  · exact ⟨.inl ⟨j,hj⟩,rfl⟩
  · have hl : Fintype.card {i // R i j}=1 := by have hp := hpos j; omega
    refine ⟨.inr ((actualSlotLeafEquiv C h3).symm ⟨j,hl⟩),?_⟩
    exact congrArg Subtype.val ((actualSlotLeafEquiv C h3).apply_symm_apply ⟨j,hl⟩)

theorem recovered_incidence {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (i : I) (j : CompletedSink (retainedBlock R) (retainedColoring C)) :
    R i (recoverSink C h3 j) ↔ completedIncidence (retainedBlock R) (retainedColoring C) i j := by
  cases j with
  | inl j => exact (retained_support_iff R j i).symm
  | inr p => exact actual_slot_leaf_incidence C h3 p i

/-- Completing the actual colored support at its vacant slots recovers the
entire original saturated tree, including the colors of removed leaf edges. -/
noncomputable def reconstructionIso {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (hpos : ∀ j,0<Fintype.card {i // R i j}) :
    ColoredIso (completedColoring (retainedBlock R) (retainedColoring C)) C where
  source := Equiv.refl I
  sink := Equiv.ofBijective _ ⟨recover_sink_injective C h3,recover_sink_surjective C h3 hpos⟩
  incidence := recovered_incidence C h3
  color := by
    intro i j h
    cases j with
    | inl j => rfl
    | inr p =>
      change i=p.1.1 at h
      subst i
      exact actual_slot_leaf_color C h3 p _

end KroneckerReflectedReconstruction
end

/- Original module: KroneckerReflectionReindexing -/
section
set_option autoImplicit false
namespace KroneckerReflectionReindexing
open KroneckerReflectionKernel
open scoped BigOperators

/-- Reindex the actual zero-sum kernel, with no choice of basis. -/
noncomputable def kernelEquiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    Kernel A ≃ₗ[ℂ] Kernel B where
  toFun x := ⟨fun b => x.1 (e.symm b),by
    change ∑ b,x.1 (e.symm b)=0
    rw [e.symm.sum_comp]
    exact x.2⟩
  invFun y := ⟨fun a => y.1 (e a),by
    change ∑ a,y.1 (e a)=0
    rw [e.sum_comp]
    exact y.2⟩
  left_inv := by intro x; apply Subtype.ext; funext a; simp
  right_inv := by intro y; apply Subtype.ext; funext b; simp
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

theorem kernel_equiv_projection {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (a : A) (x : Kernel A) : projection (e a) (kernelEquiv e x)=projection a x := by
  change x.1 (e.symm (e a))=x.1 a
  rw [e.symm_apply_apply]

theorem kernel_equiv_comp {A B D : Type*} [Fintype A] [Fintype B] [Fintype D]
    (e : A ≃ B) (f : B ≃ D) (x : Kernel A) :
    kernelEquiv f (kernelEquiv e x)=kernelEquiv (e.trans f) x := rfl

theorem projection_sum_zero {A : Type*} [Fintype A] (x : Kernel A) :
    ∑ a,projection a x=0 := x.2

/-- The family of arrows determines the kernel reindexing uniquely. -/
theorem kernel_equiv_unique {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (L : Kernel A →ₗ[ℂ] Kernel B)
    (h : ∀ a x,projection (e a) (L x)=projection a x) :
    L=(kernelEquiv e).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext b
  obtain ⟨a,rfl⟩ := e.surjective b
  exact (h a x).trans (kernel_equiv_projection e a x).symm

end KroneckerReflectionReindexing
end

/- Original module: KroneckerRetainedIsoTransport -/
section
set_option autoImplicit false
namespace KroneckerRetainedIsoTransport
open KroneckerColoredIncidenceIso KroneckerProperColoredReflection
open KroneckerRetainedReflectionKernels KroneckerRetainedBlockSupport
open KroneckerReflectionReindexing KroneckerReflectionKernel
attribute [local instance] Classical.propDecidable

variable {I J I' J' : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
  {R : I → J → Prop} {R' : I' → J' → Prop} {C : ProperColoring R} {C' : ProperColoring R'}

def retainedEquiv (e : ColoredIso C C') : Retained R ≃ Retained R' where
  toFun j := ⟨e.sink j,by rw [e.sink_degree]; exact j.2⟩
  invFun j := ⟨e.sink.symm j,by
    have hd := e.sink_degree (e.sink.symm j)
    rw [e.sink.apply_symm_apply] at hd
    rw [←hd]; exact j.2⟩
  left_inv := by intro j; apply Subtype.ext; exact e.sink.symm_apply_apply j
  right_inv := by intro j; apply Subtype.ext; exact e.sink.apply_symm_apply j

def retainedIso (e : ColoredIso C C') : ColoredIso (retainedColoring C) (retainedColoring C') where
  source := retainedEquiv e
  sink := e.source
  incidence := by
    intro j i
    rw [retained_support_iff,retained_support_iff]
    exact e.incidence i j.1
  color := by intro j i h; exact e.color i j.1 _

noncomputable def retainedSpaceEquiv (e : ColoredIso C C') (j : Retained R) :
    (retainedBlock R).Space j ≃ₗ[ℂ] (retainedBlock R').Space (retainedEquiv e j) :=
  kernelEquiv (e.sinkNeighbors j.1)

/-- Relabeling commutes with every reflected arrow, including absent edges. -/
theorem retained_arrow_intertwines (e : ColoredIso C C') (j : Retained R) (i : I)
    (x : (retainedBlock R).Space j) :
    (retainedBlock R').arrow (retainedEquiv e j) (e.source i) (retainedSpaceEquiv e j x)=
      (retainedBlock R).arrow j i x := by
  by_cases h : R i j.1
  · have h' := (e.incidence i j.1).mpr h
    change (if h : R' (e.source i) (e.sink j.1) then projection ⟨e.source i, h⟩ else 0)
      (retainedSpaceEquiv e j x) = (if h : R i j.1 then projection ⟨i, h⟩ else 0) x
    rw [dite_eq_left h, dite_eq_left h']
    exact kernel_equiv_projection (e.sinkNeighbors j.1) ⟨i,h⟩ x
  · have h' : ¬R' (e.source i) (e.sink j.1) := by simpa only [e.incidence] using h
    simp [retainedBlock,retainedEquiv,h,h']
    rfl

theorem retained_dimension_preserved (e : ColoredIso C C') (j : Retained R) :
    Module.finrank ℂ ((retainedBlock R').Space (retainedEquiv e j))=
      Module.finrank ℂ ((retainedBlock R).Space j) :=
  (retainedSpaceEquiv e j).finrank_eq.symm

end KroneckerRetainedIsoTransport
end

/- Original module: KroneckerReflectionFaithfulness -/
section
set_option autoImplicit false
namespace KroneckerReflectionFaithfulness
open KroneckerLinearCoverBlocks KroneckerProperColoredReflection KroneckerRetainedBlockSupport
open KroneckerRetainedVacantSlots KroneckerColoredIncidenceIso KroneckerSlotIsoTransport
open KroneckerSlotCompletion KroneckerReflectedReconstruction KroneckerRetainedIsoTransport
attribute [local instance] Classical.propDecidable

def completionIso {B B' : LinearCoverBlock} {C : ProperColoring (linearSupport B)}
    {C' : ProperColoring (linearSupport B')} (e : ColoredIso C C') :
    ColoredIso (completedColoring B C) (completedColoring B' C') where
  source := e.sink
  sink := Equiv.sumCongr e.source (slotEquiv e)
  incidence := by
    intro i j
    cases j with
    | inl s => exact e.incidence s i
    | inr p => exact e.sink.injective.eq_iff
  color := by
    intro i j h
    cases j with
    | inl s => exact e.color s i h
    | inr p => rfl

/-- An isomorphism of the actual retained colored supports reconstructs an
isomorphism of the original saturated colored incidence graphs. -/
noncomputable def recoverIso {I J I' J' : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    {R : I → J → Prop} {R' : I' → J' → Prop} {C : ProperColoring R} {C' : ProperColoring R'}
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (h3' : ∀ i,Fintype.card {j // R' i j}=3)
    (hp : ∀ j,0<Fintype.card {i // R i j}) (hp' : ∀ j,0<Fintype.card {i // R' i j})
    (e : ColoredIso (retainedColoring C) (retainedColoring C')) : ColoredIso C C' :=
  ((reconstructionIso C h3 hp).symm.trans (completionIso e)).trans (reconstructionIso C' h3' hp')

theorem reflection_isomorphism_iff {I J I' J' : Type}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    {R : I → J → Prop} {R' : I' → J' → Prop} {C : ProperColoring R} {C' : ProperColoring R'}
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (h3' : ∀ i,Fintype.card {j // R' i j}=3)
    (hp : ∀ j,0<Fintype.card {i // R i j}) (hp' : ∀ j,0<Fintype.card {i // R' i j}) :
    Nonempty (ColoredIso (retainedColoring C) (retainedColoring C')) ↔ Nonempty (ColoredIso C C') := by
  constructor
  · rintro ⟨e⟩; exact ⟨recoverIso h3 h3' hp hp' e⟩
  · rintro ⟨e⟩; exact ⟨retainedIso e⟩

end KroneckerReflectionFaithfulness
end
