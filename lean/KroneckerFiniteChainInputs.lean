import KroneckerChainSkeletonPermutations
import KroneckerChainRecoveryComposition

/- Original module: KroneckerChainLeafClassification -/
section
set_option autoImplicit false
namespace KroneckerChainLeafClassification
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainSkeletonPermutations
attribute [local instance] Classical.propDecidable

def LeafAt {n : ℕ} (i : Connector n) (j : Block n) : Prop :=
  incidence i j ∧ ∀ k,incidence k j → k=i

theorem leaf_at_iff {n : ℕ} (i : Connector n) (j : Block n) :
    LeafAt i j ↔ j=middleBlock i ∨ (i=0 ∧ j=leftBlock n) ∨ (i=Fin.last n ∧ j=rightBlock n) := by
  constructor
  · rintro ⟨hi,hu⟩
    rcases block_cases j with rfl | rfl | ⟨t,rfl⟩ | ⟨t,rfl⟩
    · exact Or.inr (Or.inl ⟨(left_incidence i).mp hi,rfl⟩)
    · exact Or.inr (Or.inr ⟨(right_incidence i).mp hi,rfl⟩)
    · have ht := (middle_incidence i t).mp hi
      subst t; exact Or.inl rfl
    · have h1 := hu t.castSucc ((internal_incidence _ _).mpr (Or.inl rfl))
      have h2 := hu t.succ ((internal_incidence _ _).mpr (Or.inr rfl))
      have hv := congrArg Fin.val (h1.trans h2.symm)
      simp only [Fin.val_castSucc,Fin.val_succ] at hv
      omega
  · rintro (rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨(middle_incidence _ _).mpr rfl,fun k hk => (middle_incidence _ _).mp hk⟩
    · exact ⟨(left_incidence _).mpr rfl,fun k hk => (left_incidence _).mp hk⟩
    · exact ⟨(right_incidence _).mpr rfl,fun k hk => (right_incidence _).mp hk⟩

theorem leaf_transport {n : ℕ} (p : SkeletonPerm n) (i : Connector n) (j : Block n) :
    LeafAt (p.1.1 i) (p.1.2 j) ↔ LeafAt i j := by
  constructor
  · rintro ⟨hi,hu⟩
    exact ⟨(p.2 _ _).mp hi,fun k hk => p.1.1.injective (hu _ ((p.2 _ _).mpr hk))⟩
  · rintro ⟨hi,hu⟩
    refine ⟨(p.2 _ _).mpr hi,?_⟩
    intro k hk
    obtain ⟨l,rfl⟩ := p.1.1.surjective k
    exact congrArg p.1.1 (hu l ((p.2 _ _).mp hk))

theorem endpoint_leaf_counts {n : ℕ} (hn : 0<n) :
    Fintype.card {j : Block n // LeafAt 0 j}=2 ∧
      Fintype.card {j : Block n // LeafAt (Fin.last n) j}=2 := by
  have hne : (0 : Connector n)≠Fin.last n := by
    intro h; have hv := congrArg Fin.val h; simp only [Fin.val_zero,Fin.val_last] at hv; omega
  constructor
  · have e := Equiv.subtypeEquivRight (fun j : Block n =>
      show LeafAt 0 j ↔ j=middleBlock 0 ∨ j=leftBlock n by simp [leaf_at_iff,hne])
    rw [Fintype.card_congr e]
    exact Fintype.card_subtype_eq_or_eq_of_ne (by intro h; cases h)
  · have e := Equiv.subtypeEquivRight (fun j : Block n =>
      show LeafAt (Fin.last n) j ↔ j=middleBlock (Fin.last n) ∨ j=rightBlock n by
        simp [leaf_at_iff,Ne.symm hne])
    rw [Fintype.card_congr e]
    exact Fintype.card_subtype_eq_or_eq_of_ne (by intro h; cases h)

end KroneckerChainLeafClassification
end

/- Original module: KroneckerChainBlockRigidity -/
section
set_option autoImplicit false
namespace KroneckerChainBlockRigidity
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainConnectorAdjacency
open KroneckerChainSkeletonPermutations KroneckerChainLeafClassification

noncomputable def inverse {n : ℕ} (p : SkeletonPerm n) : SkeletonPerm n :=
  ⟨(p.1.1.symm,p.1.2.symm),by intro i j; simpa using (p.2 (p.1.1.symm i) (p.1.2.symm j)).symm⟩

noncomputable def compose {n : ℕ} (p q : SkeletonPerm n) : SkeletonPerm n :=
  ⟨(p.1.1.trans q.1.1,p.1.2.trans q.1.2),fun i j => (q.2 _ _).trans (p.2 i j)⟩

/-- After fixing the connector path, the only remaining freedom exchanges
its two terminal leaves. Fixing one leaf at each end removes that freedom. -/
theorem block_fixed_by_terminals {n : ℕ} (p : SkeletonPerm n)
    (hi : ∀ i,p.1.1 i=i) (hl : p.1.2 (leftBlock n)=leftBlock n)
    (hr : p.1.2 (rightBlock n)=rightBlock n) : ∀ j,p.1.2 j=j := by
  intro j
  rcases block_cases j with rfl | rfl | ⟨i,rfl⟩ | ⟨t,rfl⟩
  · exact hl
  · exact hr
  · have hleaf := (leaf_transport p i (middleBlock i)).mpr ((leaf_at_iff _ _).mpr (Or.inl rfl))
    rw [hi i,leaf_at_iff] at hleaf
    rcases hleaf with h | ⟨_,h⟩ | ⟨_,h⟩
    · exact h
    · have he := p.1.2.injective (h.trans hl.symm)
      cases he
    · have he := p.1.2.injective (h.trans hr.symm)
      cases he
  · have h1 := (p.2 t.castSucc (internalBlock t)).mpr ((internal_incidence _ _).mpr (Or.inl rfl))
    have h2 := (p.2 t.succ (internalBlock t)).mpr ((internal_incidence _ _).mpr (Or.inr rfl))
    rw [hi] at h1 h2
    apply common_block_unique (i:=t.castSucc) (k:=t.succ) _ h1 h2
      ((internal_incidence _ _).mpr (Or.inl rfl)) ((internal_incidence _ _).mpr (Or.inr rfl))
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_succ] at hv
    omega

theorem skeleton_determined {n : ℕ} (p q : SkeletonPerm n)
    (hi : p.1.1=q.1.1) (hl : p.1.2 (leftBlock n)=q.1.2 (leftBlock n))
    (hr : p.1.2 (rightBlock n)=q.1.2 (rightBlock n)) : p=q := by
  have hc : ∀ i,(compose p (inverse q)).1.1 i=i := by
    intro i
    change q.1.1.symm (p.1.1 i)=i
    rw [hi,q.1.1.symm_apply_apply]
  have hleft : (compose p (inverse q)).1.2 (leftBlock n)=leftBlock n := by
    change q.1.2.symm (p.1.2 (leftBlock n))=leftBlock n
    rw [hl,q.1.2.symm_apply_apply]
  have hright : (compose p (inverse q)).1.2 (rightBlock n)=rightBlock n := by
    change q.1.2.symm (p.1.2 (rightBlock n))=rightBlock n
    rw [hr,q.1.2.symm_apply_apply]
  apply Subtype.ext
  apply Prod.ext hi
  apply Equiv.ext
  intro j
  have h := congrArg q.1.2 (block_fixed_by_terminals (compose p (inverse q)) hc hleft hright j)
  simpa [compose,inverse] using h

end KroneckerChainBlockRigidity
end

/- Original module: KroneckerChainFixedLabelRecovery -/
section
set_option autoImplicit false
namespace KroneckerChainFixedLabelRecovery
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainRecoveredSkeleton
open KroneckerChainRecoveredColors KroneckerChainRecoveredSlots KroneckerChainIntrinsicTransport
open KroneckerColoredIncidenceIso KroneckerAssignedSlotObjects KroneckerSlotIsoTransport

variable {n : ℕ} {d d' : Block n → ℕ} {σ τ : ColorChoices n}
  (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
  (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
  (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
  (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
    finrank ℂ ((gluedRepresentative M).block.Space s))
  (hi : ∀ i,recoveredConnectorEquiv M N hd hd' e he i=i)
  (hj : ∀ j,chainBlockEquiv M N hd hd' e he j=j)

include hj in
theorem fixed_label_dimensions : d'=d := by
  funext j
  simpa only [hj] using recovered_block_dimensions M N hd hd' e he j

include hi hj in
theorem fixed_label_colors : σ=τ := by
  apply port_colors_recover_permutations
  intro i j h
  have hc := attachment_color_transport M N hd hd' e he i j h
  simpa only [hi,hj,assignment_uses_prescribed_colors] using hc.symm

/-- Once the recovered skeleton labeling is fixed, no extra multiplicity
comes from the isomorphism classes of the independently chosen marked blocks. -/
theorem fixed_label_marked_classes
    {d : Block n → ℕ} {σ : ColorChoices n} (M N : RepresentativeFamily d σ)
    (hd : ∀ j,0<d j)
    (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
    (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
      finrank ℂ ((gluedRepresentative M).block.Space s))
    (hi : ∀ i,recoveredConnectorEquiv M N hd hd e he i=i)
    (hj : ∀ j,chainBlockEquiv M N hd hd e he j=j) : representedClass M=representedClass N := by
  funext j
  apply Quotient.sound
  have h : ∃ f : ColoredIso (familyColoring M j)
      (familyColoring N (chainBlockEquiv M N hd hd e he j)),
      ∀ i (hij : incidence i j)
        (hij' : incidence (recoveredConnectorEquiv M N hd hd e he i) (chainBlockEquiv M N hd hd e he j)),slotEquiv f ((familyAssignment M).slot i j hij)=
        (familyAssignment N).slot (recoveredConnectorEquiv M N hd hd e he i)
          (chainBlockEquiv M N hd hd e he j) hij' :=
    ⟨localColoredIso M N hd hd e he j,fun i hij _ => marked_slot_transport M N hd hd e he i j hij⟩
  rw [hj j] at h
  simp only [hi] at h
  obtain ⟨f,hf⟩ := h
  exact ⟨f,fun a => hf a.1 a.2 a.2⟩

end KroneckerChainFixedLabelRecovery
end

/- Original module: KroneckerChainLabelCollision -/
section
set_option autoImplicit false
namespace KroneckerChainLabelCollision
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainIntrinsicTransport
open KroneckerChainRecoveredSkeleton KroneckerColoredIncidenceIso KroneckerChainRecoveryComposition
open KroneckerChainSkeletonPermutations KroneckerChainFixedLabelRecovery

variable {n : ℕ} {d d' : Block n → ℕ} {σ τ : ColorChoices n}
  (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
  (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
  (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
  (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
    finrank ℂ ((gluedRepresentative M).block.Space s))

include he in
theorem reverse_dimensions (s : (gluedRepresentative N).block.Source) :
    finrank ℂ ((gluedRepresentative M).block.Space (e.symm.source s))=
      finrank ℂ ((gluedRepresentative N).block.Space s) :=
  (he (e.source.symm s)).symm.trans
    (congrArg (fun t => finrank ℂ ((gluedRepresentative N).block.Space t)) (e.source.apply_symm_apply s))

theorem recovered_connector_inverse (i : Connector n) :
    recoveredConnectorEquiv N M hd' hd e.symm (reverse_dimensions M N e he)
      (recoveredConnectorEquiv M N hd hd' e he i)=i := by
  rw [←connector_composition M N M hd hd' hd e e.symm he (reverse_dimensions M N e he)]
  apply connector_fixed_of_source_fixed
  intro k
  exact e.source.symm_apply_apply _

theorem recovered_block_inverse (j : Block n) :
    chainBlockEquiv N M hd' hd e.symm (reverse_dimensions M N e he)
      (chainBlockEquiv M N hd hd' e he j)=j := by
  rw [←block_composition M N M hd hd' hd e e.symm he (reverse_dimensions M N e he)]
  apply block_fixed_of_sink_fixed
  intro k t
  exact congrArg Sigma.fst (e.sink.symm_apply_apply ⟨k,t⟩)

/-- Two inputs sent to the same representative with the same recovered
skeleton labeling have identical marked block classes. -/
theorem equal_labels_recover_classes {d : Block n → ℕ} {σ : ColorChoices n}
    (M N : RepresentativeFamily d σ) (P : RepresentativeFamily d' τ)
    (hd : ∀ j,0<d j) (hp : ∀ j,0<d' j)
    (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative P).coloring)
    (f : ColoredIso (gluedRepresentative N).coloring (gluedRepresentative P).coloring)
    (he : ∀ s,finrank ℂ ((gluedRepresentative P).block.Space (e.source s))=
      finrank ℂ ((gluedRepresentative M).block.Space s))
    (hf : ∀ s,finrank ℂ ((gluedRepresentative P).block.Space (f.source s))=
      finrank ℂ ((gluedRepresentative N).block.Space s))
    (h : recoveredSkeletonPerm M P hd hp e he=recoveredSkeletonPerm N P hd hp f hf) :
    representedClass M=representedClass N := by
  let hg := fun s => ((reverse_dimensions N P f hf) (e.source s)).trans (he s)
  apply fixed_label_marked_classes M N hd (e.trans f.symm) hg
  · intro i
    rw [connector_composition M P N hd hp hd e f.symm he (reverse_dimensions N P f hf)]
    have hi := congrArg (fun p : SkeletonPerm n => p.1.1 i) h
    change recoveredConnectorEquiv M P hd hp e he i=recoveredConnectorEquiv N P hd hp f hf i at hi
    rw [hi]
    exact recovered_connector_inverse N P hd hp f hf i
  · intro j
    rw [block_composition M P N hd hp hd e f.symm he (reverse_dimensions N P f hf)]
    have hj := congrArg (fun p : SkeletonPerm n => p.1.2 j) h
    change chainBlockEquiv M P hd hp e he j=chainBlockEquiv N P hd hp f hf j at hj
    rw [hj]
    exact recovered_block_inverse N P hd hp f hf j

end KroneckerChainLabelCollision
end

/- Original module: KroneckerChainLabelingCount -/
section
set_option autoImplicit false
namespace KroneckerChainLabelingCount
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainSkeletonPermutations
open KroneckerChainLeafClassification KroneckerChainBlockRigidity KroneckerFinitePathCount
attribute [local instance] Classical.propDecidable

abbrev LabelCode (n : ℕ) := Σ p : PathPerm n,
  {j : Block n // LeafAt (p.1 0) j} × {j : Block n // LeafAt (p.1 (Fin.last n)) j}

noncomputable def labelCode {n : ℕ} (p : SkeletonPerm n) : LabelCode n :=
  ⟨connectorPath p,
    ⟨p.1.2 (leftBlock n),(leaf_transport p _ _).mpr ((leaf_at_iff _ _).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)))⟩,
    ⟨p.1.2 (rightBlock n),(leaf_transport p _ _).mpr ((leaf_at_iff _ _).mpr (Or.inr (Or.inr ⟨rfl,rfl⟩)))⟩⟩

theorem label_code_injective (n : ℕ) : Function.Injective (labelCode (n:=n)) := by
  intro p q h
  apply skeleton_determined p q
  · exact congrArg (fun z : LabelCode n => z.1.1) h
  · exact congrArg (fun z : LabelCode n => z.2.1.1) h
  · exact congrArg (fun z : LabelCode n => z.2.2.1) h

theorem leaf_count_le_two {n : ℕ} (hn : 0<n) (i : Connector n) :
    Fintype.card {j : Block n // LeafAt i j}≤2 := by
  by_cases h0 : i=0
  · subst i; exact (endpoint_leaf_counts hn).1.le
  by_cases hlast : i=Fin.last n
  · subst i; exact (endpoint_leaf_counts hn).2.le
  have e := Equiv.subtypeEquivRight (fun j : Block n =>
    show LeafAt i j ↔ j=middleBlock i by simp [leaf_at_iff,h0,hlast])
  rw [Fintype.card_congr e]
  simp

/-- The two path orientations and two choices of terminal leaf at each end
bound the actual skeleton relabelings by eight. -/
theorem chain_labelings_le_eight {n : ℕ} (hn : 0<n) : Fintype.card (SkeletonPerm n)≤8 := by
  classical
  calc
    Fintype.card (SkeletonPerm n) ≤ Fintype.card (LabelCode n) :=
      Fintype.card_le_of_injective labelCode (label_code_injective n)
    _ = ∑ p : PathPerm n,Fintype.card {j : Block n // LeafAt (p.1 0) j} *
        Fintype.card {j : Block n // LeafAt (p.1 (Fin.last n)) j} := by
      simp only [Fintype.card_sigma,Fintype.card_prod]
    _ ≤ ∑ _p : PathPerm n,(4 : ℕ) := by
      apply Finset.sum_le_sum
      intro p _
      have h0 := leaf_count_le_two hn (p.1 0)
      have h1 := leaf_count_le_two hn (p.1 (Fin.last n))
      exact (Nat.mul_le_mul h0 h1)
    _ = Fintype.card (PathPerm n)*4 := by simp
    _ ≤ 8 := Nat.mul_le_mul_right 4 (path_permutation_count n)

/-- For one connector the skeleton is the three-leaf star. -/
theorem star_labelings_le_six : Fintype.card (SkeletonPerm 0)≤6 := by
  have hinj : Function.Injective (fun p : SkeletonPerm 0 => p.1.2) := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext _ h
    apply Equiv.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  have hc := Fintype.card_le_of_injective _ hinj
  norm_num [Fintype.card_perm,Block] at hc
  exact hc

end KroneckerChainLabelingCount
end

/- Original module: KroneckerChainClassFibers -/
section
set_option autoImplicit false
namespace KroneckerChainClassFibers
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainLocalSlotClasses
open KroneckerChainSlotAssignments KroneckerChainRepresentativeIndependence
open KroneckerDimensionedChainGluing KroneckerDimensionedSupportClasses
open KroneckerChainLabelCollision KroneckerChainSkeletonPermutations KroneckerChainLabelingCount
open KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable


def labelingBound (n : ℕ) : ℕ := if n=0 then 6 else 8

theorem skeleton_count_bound (n : ℕ) : Fintype.card (SkeletonPerm n)≤labelingBound n := by
  by_cases hn : n=0
  · subst n; exact star_labelings_le_six
  · simpa [labelingBound,hn] using chain_labelings_le_eight (n:=n) (by omega)


end KroneckerChainClassFibers
end

/- Original module: KroneckerChainParameterLabelRecovery -/
section
set_option autoImplicit false
namespace KroneckerChainParameterLabelRecovery
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainIntrinsicTransport
open KroneckerChainRecoveredSkeleton KroneckerColoredIncidenceIso KroneckerChainRecoveryComposition
open KroneckerChainSkeletonPermutations KroneckerChainFixedLabelRecovery KroneckerChainLabelCollision

/-- Equal recovered labelings also recover variable block dimensions and
connector color choices; they do not introduce an extra parameter fiber. -/
theorem equal_labels_recover_parameters {n : ℕ} {d₁ d₂ d₃ : Block n → ℕ}
    {σ₁ σ₂ σ₃ : ColorChoices n}
    (M : RepresentativeFamily d₁ σ₁) (N : RepresentativeFamily d₂ σ₂) (P : RepresentativeFamily d₃ σ₃)
    (h₁ : ∀ j,0<d₁ j) (h₂ : ∀ j,0<d₂ j) (h₃ : ∀ j,0<d₃ j)
    (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative P).coloring)
    (f : ColoredIso (gluedRepresentative N).coloring (gluedRepresentative P).coloring)
    (he : ∀ s,finrank ℂ ((gluedRepresentative P).block.Space (e.source s))=
      finrank ℂ ((gluedRepresentative M).block.Space s))
    (hf : ∀ s,finrank ℂ ((gluedRepresentative P).block.Space (f.source s))=
      finrank ℂ ((gluedRepresentative N).block.Space s))
    (h : recoveredSkeletonPerm M P h₁ h₃ e he=recoveredSkeletonPerm N P h₂ h₃ f hf) :
    d₁=d₂ ∧ σ₁=σ₂ := by
  have hrev : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (f.symm.source s))=
      finrank ℂ ((gluedRepresentative P).block.Space s) := fun s =>
    (hf (f.source.symm s)).symm.trans
      (congrArg (fun t => finrank ℂ ((gluedRepresentative P).block.Space t)) (f.source.apply_symm_apply s))
  let hg := fun s => (hrev (e.source s)).trans (he s)
  have hi : ∀ i,recoveredConnectorEquiv M N h₁ h₂ (e.trans f.symm) hg i=i := by
    intro i
    rw [connector_composition M P N h₁ h₃ h₂ e f.symm he hrev]
    have hi := congrArg (fun p : SkeletonPerm n => p.1.1 i) h
    change recoveredConnectorEquiv M P h₁ h₃ e he i=recoveredConnectorEquiv N P h₂ h₃ f hf i at hi
    rw [hi]
    exact recovered_connector_inverse N P h₂ h₃ f hf i
  have hj : ∀ j,chainBlockEquiv M N h₁ h₂ (e.trans f.symm) hg j=j := by
    intro j
    rw [block_composition M P N h₁ h₃ h₂ e f.symm he hrev]
    have hj := congrArg (fun p : SkeletonPerm n => p.1.2 j) h
    change chainBlockEquiv M P h₁ h₃ e he j=chainBlockEquiv N P h₂ h₃ f hf j at hj
    rw [hj]
    exact recovered_block_inverse N P h₂ h₃ f hf j
  exact ⟨(fixed_label_dimensions M N h₁ h₂ (e.trans f.symm) hg hj).symm,
    fixed_label_colors M N h₁ h₂ (e.trans f.symm) hg hi hj⟩

end KroneckerChainParameterLabelRecovery
end

/- Original module: KroneckerFiniteChainInputs -/
section
set_option autoImplicit false
namespace KroneckerFiniteChainInputs
open KroneckerChainIncidence KroneckerChainPortColors KroneckerChainLocalSlotClasses
open KroneckerDimensionedChainGluing KroneckerDimensionedSupportClasses
attribute [local instance] Classical.propDecidable

/-- Actual positive block dimensions with the fixed total glued source size.
The bounded encoding is finite without postulating a finite set of real flows. -/
abbrev DimensionData (n a : ℕ) := {d : Block n → Fin (a+1) //
  (∀ j,0<(d j).val) ∧ (∑ j,(d j).val)+(n+1)=a}

def dimensions {n a : ℕ} (d : DimensionData n a) (j : Block n) : ℕ := (d.1 j).val

theorem dimensions_injective (n a : ℕ) : Function.Injective (dimensions (n:=n) (a:=a)) := by
  intro d e h
  apply Subtype.ext
  funext j
  exact Fin.ext (congrFun h j)

noncomputable def encodeDimensions {n a : ℕ} (d : Block n → ℕ)
    (hd : ∀ j,0<d j) (hs : (∑ j,d j)+(n+1)=a) : DimensionData n a :=
  ⟨fun j => ⟨d j,by
    have hj : d j≤∑ k,d k := Finset.single_le_sum (fun k _ => Nat.zero_le (d k)) (Finset.mem_univ j)
    omega⟩,hd,hs⟩


abbrev ChainInput (n a : ℕ) := Σ d : DimensionData n a,Σ σ : ColorChoices n,FamilyClass (dimensions d) σ

noncomputable instance (n a : ℕ) : Fintype (ChainInput n a) := Fintype.ofFinite _

noncomputable def forgetInput {n a : ℕ} (X : ChainInput n a) : Quotient dimensionedSetoid :=
  dimensionedGlueClasses X.2.2


end KroneckerFiniteChainInputs
end
