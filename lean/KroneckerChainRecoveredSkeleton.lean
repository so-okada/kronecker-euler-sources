import KroneckerChainRepresentativeStability
import KroneckerDimensionedSupportClasses
import KroneckerRecoveredBlockComponents

/- Original module: KroneckerDimensionedChainGluing -/
section
set_option autoImplicit false
namespace KroneckerDimensionedChainGluing
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainNeighborIndices
open KroneckerChainSlotAssignments KroneckerChainLocalSlotClasses KroneckerAssignedSlotObjects
open KroneckerChainRepresentativeIndependence KroneckerDimensionedSupportClasses
open KroneckerActualSlotGluing KroneckerActualGluedColorTransport KroneckerSlotGluingIsomorphism
open KroneckerFiniteColoredTables KroneckerGluedLinearRepresentation
attribute [local instance] Classical.propDecidable

theorem dimensioned_representative_independence {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M N : RepresentativeFamily d σ) (h : representedClass M=representedClass N) :
    dimensionedSetoid (gluedRepresentative M) (gluedRepresentative N) := by
  classical
  have hl : ∀ j,assignedSetoid _ _ _ (neighborColors σ j) (M j) (N j) :=
    fun j => Quotient.exact (congrFun h j)
  choose f hf using hl
  refine ⟨actualGluedIso (familyAssignment M) (familyAssignment N) f
    (fun i j hij => hf j ⟨i,hij⟩),?_⟩
  intro s
  cases s with
  | inl i => rfl
  | inr p =>
    rcases p with ⟨j,s⟩
    exact retained_iso_preserves_dimensions (coloring (M j).1.1) (coloring (N j).1.1) (f j) s

noncomputable def dimensionedGlueClasses {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (X : FamilyClass d σ) : Quotient dimensionedSetoid :=
  Quotient.mk dimensionedSetoid (gluedRepresentative (representatives X))

theorem dimensioned_glue_of_representative {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) :
    dimensionedGlueClasses (representedClass M)=
      Quotient.mk dimensionedSetoid (gluedRepresentative M) := by
  apply Quotient.sound
  exact dimensioned_representative_independence _ M (representatives_correct (representedClass M))

theorem forget_dimensions_gluing {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (X : FamilyClass d σ) : forgetDimensions (dimensionedGlueClasses X)=glueClasses X := rfl

end KroneckerDimensionedChainGluing
end

/- Original module: KroneckerIntrinsicConnectors -/
section
set_option autoImplicit false
namespace KroneckerIntrinsicConnectors
open Module KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedLinearRepresentation KroneckerGluedSupportGraph KroneckerGluedSupportTree
open KroneckerSaturatedBlockData KroneckerBipartiteIncidence
attribute [local instance] Classical.propDecidable

def IsConnector (B : LinearCoverBlock) (s : B.Source) : Prop :=
  finrank ℂ (B.Space s)=1 ∧ Fintype.card {t // linearSupport B s t}=3

theorem glued_connector_degree {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (i : I) : Fintype.card {t // linearSupport (gluedBlock B R attach) (.inl i) t}=
      Fintype.card {j // R i j} := by
  simpa only [glued_arrow_support_iff,←Nat.card_eq_fintype_card] using
    connector_neighbor_count B R attach i

theorem glued_internal_degree {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (j : J) (s : (B j).Source) :
    Fintype.card {t // linearSupport (gluedBlock B R attach) (.inr ⟨j,s⟩) t}=
      Fintype.card {t // linearSupport (B j) s t} := by
  simpa only [glued_arrow_support_iff,←Nat.card_eq_fintype_card] using
    internal_neighbor_count B R attach j s

/-- Connectors can be recognized from the dimensioned support alone. -/
theorem intrinsic_connector_iff {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (hB : ∀ j s,finrank ℂ ((B j).Space s)=1 → Fintype.card {t // linearSupport (B j) s t}=2)
    (s : (gluedBlock B R attach).Source) :
    IsConnector (gluedBlock B R attach) s ↔ ∃ i,s=Sum.inl i := by
  cases s with
  | inl i =>
    constructor
    · intro _; exact ⟨i,rfl⟩
    · intro _
      exact ⟨by change finrank ℂ ℂ=1; simp,(glued_connector_degree B R attach i).trans (h3 i)⟩
  | inr p =>
    rcases p with ⟨j,s⟩
    constructor
    · rintro ⟨hd,hdeg⟩
      change finrank ℂ ((B j).Space s)=1 at hd
      rw [glued_internal_degree,hB j s hd] at hdeg
      omega
    · rintro ⟨i,h⟩; cases h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem supported_dimension_one_degree_two (T : SaturatedBlockData) (s : (supportedBlock T).Source)
    (hd : finrank ℂ ((supportedBlock T).Space s)=1) :
    Fintype.card {t // linearSupport (supportedBlock T) s t}=2 := by
  have hp := retained_dimension_degree_pairs T.coloring s
  rw [supportGraph,left_degree] at hp
  rcases hp with ⟨_,h⟩ | ⟨h,_⟩
  · exact h
  · change finrank ℂ ((KroneckerRetainedReflectionKernels.retainedBlock T.incidence).Space s)=1 at hd
    omega

end KroneckerIntrinsicConnectors
end

/- Original module: KroneckerChainIntrinsicTransport -/
section
set_option autoImplicit false
namespace KroneckerChainIntrinsicTransport
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainRepresentativeStability
open KroneckerDimensionedSupportClasses KroneckerIntrinsicConnectors KroneckerReflectedSupportClasses
open KroneckerColoredIncidenceIso KroneckerSaturatedBlockData KroneckerActualSlotGluing
attribute [local instance] Classical.propDecidable

theorem connector_transport (X Y : ColoredBlock) (e : ColoredIso X.coloring Y.coloring)
    (he : ∀ s,finrank ℂ (Y.block.Space (e.source s))=finrank ℂ (X.block.Space s))
    (s : X.block.Source) : IsConnector Y.block (e.source s) ↔ IsConnector X.block s := by
  unfold IsConnector
  rw [he s,e.source_degree s]

theorem chain_connector_iff {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (hd : ∀ j,0<d j)
    (s : (gluedRepresentative M).block.Source) :
    IsConnector (gluedRepresentative M).block s ↔ ∃ i : Connector n,s=Sum.inl i := by
  apply intrinsic_connector_iff (familyBlock M) incidence (attachment (familyAssignment M))
    connector_degree
  intro j t ht
  exact supported_dimension_one_degree_two (tableData (d j) (hd j) (M j).1) t ht

noncomputable def insertedConnectorEquiv {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (hd : ∀ j,0<d j) :
    Connector n ≃ {s // IsConnector (gluedRepresentative M).block s} :=
  Equiv.ofBijective (fun i => ⟨Sum.inl i,(chain_connector_iff M hd _).mpr ⟨i,rfl⟩⟩) (by
    constructor
    · intro i k h; exact Sum.inl_injective (congrArg Subtype.val h)
    · intro s
      obtain ⟨i,hi⟩ := (chain_connector_iff M hd s).mp s.2
      exact ⟨i,Subtype.ext hi.symm⟩)

noncomputable def recoveredConnectorEquiv {n m : ℕ} {d : Block n → ℕ} {d' : Block m → ℕ}
    {σ : ColorChoices n} {τ : ColorChoices m}
    (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
    (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
    (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
    (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
      finrank ℂ ((gluedRepresentative M).block.Space s)) : Connector n ≃ Connector m :=
  (insertedConnectorEquiv M hd).trans
    ((Equiv.subtypeEquiv e.source (fun s => (connector_transport _ _ e he s).symm)).trans
      (insertedConnectorEquiv N hd').symm)

theorem dimensioned_class_recovers_chain_length {n m : ℕ} {d : Block n → ℕ} {d' : Block m → ℕ}
    {σ : ColorChoices n} {τ : ColorChoices m}
    (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
    (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
    (h : dimensionedSetoid (gluedRepresentative M) (gluedRepresentative N)) : n=m := by
  obtain ⟨e,he⟩ := h
  have hc := Fintype.card_congr (recoveredConnectorEquiv M N hd hd' e he)
  simpa [Connector] using hc

end KroneckerChainIntrinsicTransport
end

/- Original module: KroneckerIntrinsicBlockDeletion -/
section
set_option autoImplicit false
namespace KroneckerIntrinsicBlockDeletion
open SimpleGraph Module KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedLinearRepresentation KroneckerGluedSupportGraph
open KroneckerIntrinsicConnectors KroneckerDeletedConnectorGraph
attribute [local instance] Classical.propDecidable

def Survives (B : LinearCoverBlock) : B.Source ⊕ B.Sink → Prop
  | .inl s => ¬IsConnector B s
  | .inr _ => True

def intrinsicDeletion (B : LinearCoverBlock) : SimpleGraph {v // Survives B v} :=
  (supportGraph B).comap Subtype.val

variable {I J : Type} [Fintype I] [Fintype J]
  (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
  (h3 : ∀ i,Fintype.card {j // R i j}=3)
  (hB : ∀ j s,finrank ℂ ((B j).Space s)=1 → Fintype.card {t // linearSupport (B j) s t}=2)

def remainingSurvivor (v : RemainingVertex B) : {v // Survives (gluedBlock B R attach) v} :=
  ⟨remainingEmbedding B v,by
    rcases v with ⟨j,s | t⟩
    · change ¬IsConnector (gluedBlock B R attach) (.inr ⟨j,s⟩)
      rw [intrinsic_connector_iff B R attach h3 hB]
      rintro ⟨i,h⟩; cases h
    · trivial⟩

theorem remaining_survivor_bijective : Function.Bijective (remainingSurvivor B R attach h3 hB) := by
  constructor
  · intro u v h
    exact remaining_embedding_injective B (congrArg Subtype.val h)
  · rintro ⟨v,hv⟩
    cases v with
    | inl s => cases s with
      | inl i =>
        exact False.elim (hv ((intrinsic_connector_iff B R attach h3 hB _).mpr ⟨i,rfl⟩))
      | inr p => exact ⟨⟨p.1,.inl p.2⟩,rfl⟩
    | inr p => exact ⟨⟨p.1,.inr p.2⟩,rfl⟩

/-- Intrinsic deletion, defined only from dimensions and the actual arrow
support, is isomorphic to the disjoint union of the original blocks. -/
noncomputable def intrinsicDeletionIso : remainingGraph B ≃g intrinsicDeletion (gluedBlock B R attach) where
  toEquiv := Equiv.ofBijective _ (remaining_survivor_bijective B R attach h3 hB)
  map_rel_iff' := by
    intro u v
    change (supportGraph (gluedBlock B R attach)).Adj
      (remainingEmbedding B u) (remainingEmbedding B v) ↔ _
    rw [glued_support_graph]
    exact remaining_adj_iff B R attach u v

end KroneckerIntrinsicBlockDeletion
end

/- Original module: KroneckerIntrinsicDeletionTransport -/
section
set_option autoImplicit false
namespace KroneckerIntrinsicDeletionTransport
open Module KroneckerReflectedSupportClasses KroneckerColoredIncidenceIso
open KroneckerIntrinsicBlockDeletion KroneckerChainIntrinsicTransport

variable {X Y : ColoredBlock} (e : ColoredIso X.coloring Y.coloring)
  (he : ∀ s,finrank ℂ (Y.block.Space (e.source s))=finrank ℂ (X.block.Space s))

include he in
theorem survives_transport (v : X.block.Source ⊕ X.block.Sink) :
    Survives Y.block (e.graphIso v) ↔ Survives X.block v := by
  cases v with
  | inl s => exact not_congr (connector_transport X Y e he s)
  | inr t => rfl

/-- An arbitrary dimension-preserving colored isomorphism restricts to the
intrinsic deletion. The restriction uses no chosen block labeling. -/
def deletionIso : intrinsicDeletion X.block ≃g intrinsicDeletion Y.block where
  toEquiv := Equiv.subtypeEquiv e.graphIso.toEquiv (fun v => (survives_transport e he v).symm)
  map_rel_iff' := by
    intro u v
    exact e.graphIso.map_rel_iff

theorem deletion_embedding_natural (v : {v // Survives X.block v}) :
    (deletionIso e he v).1=e.graphIso v.1 := rfl

end KroneckerIntrinsicDeletionTransport
end

/- Original module: KroneckerChainDeletionTransport -/
section
set_option autoImplicit false
namespace KroneckerChainDeletionTransport
open Module SimpleGraph KroneckerChainIncidence KroneckerChainPortColors
open KroneckerChainSlotAssignments KroneckerChainRepresentativeIndependence
open KroneckerChainRepresentativeStability KroneckerSaturatedBlockData
open KroneckerIntrinsicBlockDeletion KroneckerDeletedConnectorGraph
open KroneckerIntrinsicDeletionTransport KroneckerIntrinsicConnectors
open KroneckerActualSlotGluing KroneckerColoredIncidenceIso
open KroneckerRetainedBlockSupport

variable {n m : ℕ} {d : Block n → ℕ} {d' : Block m → ℕ}
  {σ : ColorChoices n} {τ : ColorChoices m}
  (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
  (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)

noncomputable def chainDeletionIso : remainingGraph (familyBlock M) ≃g
    intrinsicDeletion (gluedRepresentative M).block :=
  intrinsicDeletionIso (familyBlock M) incidence (attachment (familyAssignment M)) connector_degree
    (fun j => supported_dimension_one_degree_two (tableData (d j) (hd j) (M j).1))

noncomputable def remainingIso
    (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
    (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
      finrank ℂ ((gluedRepresentative M).block.Space s)) :
    remainingGraph (familyBlock M) ≃g remainingGraph (familyBlock N) :=
  (chainDeletionIso M hd).trans ((deletionIso e he).trans (chainDeletionIso N hd').symm)

theorem remaining_embedding_natural
    (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
    (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
      finrank ℂ ((gluedRepresentative M).block.Space s))
    (v : RemainingVertex (familyBlock M)) :
    remainingEmbedding (familyBlock N) (remainingIso M N hd hd' e he v)=
      e.graphIso (remainingEmbedding (familyBlock M) v) := by
  have h := (chainDeletionIso N hd').apply_symm_apply
    (deletionIso e he (chainDeletionIso M hd v))
  exact congrArg Subtype.val h

include hd in
theorem block_connected (j : Block n) : (supportGraph (familyBlock M j)).Connected :=
  (supported_block_tree (tableData (d j) (hd j) (M j).1)).connected

end KroneckerChainDeletionTransport
end

/- Original module: KroneckerComponentBlockTransport -/
section
set_option autoImplicit false
namespace KroneckerComponentBlockTransport
open SimpleGraph KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerDeletedConnectorGraph KroneckerRecoveredBlockComponents

variable {J K : Type} (B : J → LinearCoverBlock) (D : K → LinearCoverBlock)
  (hB : ∀ j,(supportGraph (B j)).Connected) (hD : ∀ k,(supportGraph (D k)).Connected)
  (f : remainingGraph B ≃g remainingGraph D)

/-- The permutation of blocks is induced by the permutation of connected
components after intrinsic connector deletion. -/
noncomputable def blockEquiv : J ≃ K :=
  (recoveredBlockEquiv B hB).symm.trans
    (f.connectedComponentEquiv.trans (recoveredBlockEquiv D hD))

theorem block_label (v : RemainingVertex B) :
    (f v).1=blockEquiv B D hB hD f v.1 := by
  have h := (recoveredBlockEquiv B hB).symm_apply_apply ((remainingGraph B).connectedComponentMk v)
  change (recoveredBlockEquiv B hB).symm v.1=(remainingGraph B).connectedComponentMk v at h
  change (f v).1=recoveredBlockEquiv D hD
    (f.connectedComponentEquiv ((recoveredBlockEquiv B hB).symm v.1))
  rw [h]
  rfl

def blockFiberEquiv (j : J) : ((B j).Source ⊕ (B j).Sink) ≃ {v : RemainingVertex B // v.1=j} where
  toFun v := ⟨⟨j,v⟩,rfl⟩
  invFun v := v.2 ▸ v.1.2
  left_inv := by intro v; rfl
  right_inv := by rintro ⟨⟨k,v⟩,h⟩; dsimp at h; subst k; rfl

noncomputable def blockVertexEquiv (j : J) :
    ((B j).Source ⊕ (B j).Sink) ≃
      ((D (blockEquiv B D hB hD f j)).Source ⊕ (D (blockEquiv B D hB hD f j)).Sink) :=
  (blockFiberEquiv B j).trans
    ((Equiv.subtypeEquiv f.toEquiv (by
      intro v
      change v.1=j ↔ (f v).1=blockEquiv B D hB hD f j
      rw [block_label B D hB hD f v]
      exact (Equiv.apply_eq_iff_eq (blockEquiv B D hB hD f)).symm)).trans
    (blockFiberEquiv D _).symm)

theorem block_vertex_natural (j : J) (v : (B j).Source ⊕ (B j).Sink) :
    (⟨blockEquiv B D hB hD f j,blockVertexEquiv B D hB hD f j v⟩ : RemainingVertex D)=f ⟨j,v⟩ := by
  have h := (blockFiberEquiv D (blockEquiv B D hB hD f j)).apply_symm_apply
    ((Equiv.subtypeEquiv f.toEquiv (by
      intro w
      change w.1=j ↔ (f w).1=blockEquiv B D hB hD f j
      rw [block_label B D hB hD f w]
      exact (Equiv.apply_eq_iff_eq (blockEquiv B D hB hD f)).symm)) (blockFiberEquiv B j v))
  exact congrArg Subtype.val h

end KroneckerComponentBlockTransport
end

/- Original module: KroneckerRecoveredSkeleton -/
section
set_option autoImplicit false
namespace KroneckerRecoveredSkeleton
open SimpleGraph KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedSupportGraph KroneckerDeletedConnectorGraph KroneckerRecoveredBlockComponents

def recoveredIncidence {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) (i : I) (c : (remainingGraph B).ConnectedComponent) : Prop :=
  ∃ v : RemainingVertex B,(remainingGraph B).connectedComponentMk v=c ∧
    (gluedGraph B R attach).Adj (.inl (.inl i)) (remainingEmbedding B v)

theorem connector_remaining_incidence {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) (i : I) (v : RemainingVertex B)
    (h : (gluedGraph B R attach).Adj (.inl (.inl i)) (remainingEmbedding B v)) : R i v.1 := by
  rcases v with ⟨j,s | t⟩
  · exact False.elim h
  · exact Classical.choose ((glue_edge_connector_iff B R attach i j t).mp h)

/-- The skeleton is recovered from connector-to-component incidence; no
chosen root or hidden block label is required in its definition. -/
theorem recovered_incidence_iff {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) (hB : ∀ j,(supportGraph (B j)).Connected)
    (i : I) (c : (remainingGraph B).ConnectedComponent) :
    recoveredIncidence B R attach i c ↔ R i (recoveredBlockIndex B c) := by
  constructor
  · rintro ⟨v,hv,h⟩
    have he := congrArg (recoveredBlockIndex B) hv
    change v.1=recoveredBlockIndex B c at he
    rw [←he]
    exact connector_remaining_incidence B R attach i v h
  · intro h
    let j := recoveredBlockIndex B c
    let v : RemainingVertex B := ⟨j,.inr (attach i j h)⟩
    refine ⟨v,?_,GlueEdge.attachment i j h⟩
    exact (recovered_index_bijective B hB).1 rfl

theorem recovered_attachment_unique {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) (i : I) (j : J) (h : R i j) :
    ∃! v : (B j).Source ⊕ (B j).Sink,
      (gluedGraph B R attach).Adj (.inl (.inl i)) (blockVertex B j v) := by
  refine ⟨.inr (attach i j h),GlueEdge.attachment i j h,?_⟩
  intro v hv
  cases v with
  | inl s => exact False.elim hv
  | inr t =>
    obtain ⟨h',ht⟩ := (glue_edge_connector_iff B R attach i j t).mp hv
    exact congrArg Sum.inr ht.symm

end KroneckerRecoveredSkeleton
end

/- Original module: KroneckerChainRecoveredSkeleton -/
section
set_option autoImplicit false
namespace KroneckerChainRecoveredSkeleton
open Module SimpleGraph KroneckerChainIncidence KroneckerChainPortColors
open KroneckerChainSlotAssignments KroneckerChainRepresentativeIndependence
open KroneckerChainDeletionTransport KroneckerChainIntrinsicTransport
open KroneckerComponentBlockTransport KroneckerColoredIncidenceIso
open KroneckerDeletedConnectorGraph KroneckerGluedSupportGraph
open KroneckerRetainedBlockSupport KroneckerRecoveredSkeleton KroneckerActualSlotGluing

variable {n m : ℕ} {d : Block n → ℕ} {d' : Block m → ℕ}
  {σ : ColorChoices n} {τ : ColorChoices m}
  (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
  (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
  (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
  (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
    finrank ℂ ((gluedRepresentative M).block.Space s))

noncomputable def chainBlockEquiv : Block n ≃ Block m :=
  blockEquiv _ _ (block_connected M hd) (block_connected N hd') (remainingIso M N hd hd' e he)

noncomputable def chainBlockVertexEquiv (j : Block n) :
    ((familyBlock M j).Source ⊕ (familyBlock M j).Sink) ≃
      ((familyBlock N (chainBlockEquiv M N hd hd' e he j)).Source ⊕
        (familyBlock N (chainBlockEquiv M N hd hd' e he j)).Sink) :=
  blockVertexEquiv _ _ (block_connected M hd) (block_connected N hd') (remainingIso M N hd hd' e he) j

theorem chain_block_vertex_natural (j : Block n) (v : (familyBlock M j).Source ⊕ (familyBlock M j).Sink) :
    blockVertex (familyBlock N) (chainBlockEquiv M N hd hd' e he j)
      (chainBlockVertexEquiv M N hd hd' e he j v)=
    e.graphIso (blockVertex (familyBlock M) j v) := by
  change remainingEmbedding (familyBlock N) ⟨_,_⟩=_
  unfold chainBlockEquiv chainBlockVertexEquiv
  rw [block_vertex_natural]
  exact remaining_embedding_natural M N hd hd' e he ⟨j,v⟩

theorem chain_connector_natural (i : Connector n) :
    Sum.inl (recoveredConnectorEquiv M N hd hd' e he i)=e.source (.inl i) := by
  have h := (insertedConnectorEquiv N hd').apply_symm_apply
    ((Equiv.subtypeEquiv e.source (fun s => (connector_transport _ _ e he s).symm))
      (insertedConnectorEquiv M hd i))
  exact congrArg Subtype.val h

theorem incidence_iff_block_adj (i : Connector n) (j : Block n) :
    incidence i j ↔ ∃ v : (familyBlock M j).Source ⊕ (familyBlock M j).Sink,
      (supportGraph (gluedRepresentative M).block).Adj (.inl (.inl i))
        (blockVertex (familyBlock M) j v) := by
  change incidence i j ↔ ∃ v, (supportGraph
    (KroneckerGluedLinearRepresentation.gluedBlock _ _ _)).Adj _ _
  rw [glued_support_graph]
  constructor
  · intro h
    exact ⟨.inr (attachment (familyAssignment M) i j h),GlueEdge.attachment i j h⟩
  · rintro ⟨v,hv⟩
    exact connector_remaining_incidence _ _ _ i ⟨j,v⟩ hv

/-- A global isomorphism recovers an isomorphism of the actual chain skeleton. -/
theorem recovered_chain_incidence (i : Connector n) (j : Block n) :
    incidence (recoveredConnectorEquiv M N hd hd' e he i)
      (chainBlockEquiv M N hd hd' e he j) ↔ incidence i j := by
  rw [incidence_iff_block_adj N,incidence_iff_block_adj M]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨v,rfl⟩ := (chainBlockVertexEquiv M N hd hd' e he j).surjective w
    rw [chain_block_vertex_natural,chain_connector_natural] at hw
    exact ⟨v,e.graphIso.map_rel_iff.mp hw⟩
  · rintro ⟨v,hv⟩
    refine ⟨chainBlockVertexEquiv M N hd hd' e he j v,?_⟩
    rw [chain_block_vertex_natural,chain_connector_natural]
    exact e.graphIso.map_rel_iff.mpr hv

end KroneckerChainRecoveredSkeleton
end
