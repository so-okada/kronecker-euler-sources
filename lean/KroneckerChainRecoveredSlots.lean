import KroneckerChainRecoveredSkeleton

/- Original module: KroneckerChainRecoveredVertices -/
section
set_option autoImplicit false
namespace KroneckerChainRecoveredVertices
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainRecoveredSkeleton
open KroneckerColoredIncidenceIso KroneckerGluedSupportGraph

private def leftEquiv (A B : Type) : A ≃ {v : A ⊕ B // v.isLeft} where
  toFun a := ⟨.inl a,rfl⟩
  invFun v := v.1.getLeft v.2
  left_inv := fun _ => rfl
  right_inv := by rintro ⟨a | b,h⟩; rfl; cases h

private def rightEquiv (A B : Type) : B ≃ {v : A ⊕ B // v.isRight} where
  toFun b := ⟨.inr b,rfl⟩
  invFun v := v.1.getRight v.2
  left_inv := fun _ => rfl
  right_inv := by rintro ⟨a | b,h⟩; cases h; rfl

variable {n m : ℕ} {d : Block n → ℕ} {d' : Block m → ℕ}
  {σ : ColorChoices n} {τ : ColorChoices m}
  (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
  (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
  (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
  (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
    finrank ℂ ((gluedRepresentative M).block.Space s))
  (j : Block n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem block_bipartition (v : (familyBlock M j).Source ⊕ (familyBlock M j).Sink) :
    (chainBlockVertexEquiv M N hd hd' e he j v).isLeft ↔ v.isLeft := by
  have h := chain_block_vertex_natural M N hd hd' e he j v
  cases v <;> cases hv : chainBlockVertexEquiv M N hd hd' e he j _ <;>
    simp_all [blockVertex,ColoredIso.graphIso]

theorem block_bipartition_right (v : (familyBlock M j).Source ⊕ (familyBlock M j).Sink) :
    (chainBlockVertexEquiv M N hd hd' e he j v).isRight ↔ v.isRight := by
  have h := block_bipartition M N hd hd' e he j v
  cases v <;> cases hv : chainBlockVertexEquiv M N hd hd' e he j _ <;> simp_all

noncomputable def localSourceEquiv : (familyBlock M j).Source ≃
    (familyBlock N (chainBlockEquiv M N hd hd' e he j)).Source :=
  (leftEquiv _ _).trans ((Equiv.subtypeEquiv (chainBlockVertexEquiv M N hd hd' e he j)
    (fun v => (block_bipartition M N hd hd' e he j v).symm)).trans (leftEquiv _ _).symm)

noncomputable def localSinkEquiv : (familyBlock M j).Sink ≃
    (familyBlock N (chainBlockEquiv M N hd hd' e he j)).Sink :=
  (rightEquiv _ _).trans ((Equiv.subtypeEquiv (chainBlockVertexEquiv M N hd hd' e he j)
    (fun v => (block_bipartition_right M N hd hd' e he j v).symm)).trans (rightEquiv _ _).symm)

theorem local_source_natural (s : (familyBlock M j).Source) :
    Sum.inr ⟨chainBlockEquiv M N hd hd' e he j,localSourceEquiv M N hd hd' e he j s⟩=
      e.source (.inr ⟨j,s⟩) := by
  have hv : Sum.inl (localSourceEquiv M N hd hd' e he j s)=
      chainBlockVertexEquiv M N hd hd' e he j (.inl s) :=
    congrArg Subtype.val ((leftEquiv _ _).apply_symm_apply _)
  have h := chain_block_vertex_natural M N hd hd' e he j (.inl s)
  rw [←hv] at h
  exact Sum.inl_injective h

theorem local_sink_natural (t : (familyBlock M j).Sink) :
    (⟨chainBlockEquiv M N hd hd' e he j,localSinkEquiv M N hd hd' e he j t⟩ :
      (gluedRepresentative N).block.Sink)=e.sink ⟨j,t⟩ := by
  have hv : Sum.inr (localSinkEquiv M N hd hd' e he j t)=
      chainBlockVertexEquiv M N hd hd' e he j (.inr t) :=
    congrArg Subtype.val ((rightEquiv _ _).apply_symm_apply _)
  have h := chain_block_vertex_natural M N hd hd' e he j (.inr t)
  rw [←hv] at h
  exact Sum.inr_injective h

end KroneckerChainRecoveredVertices
end

/- Original module: KroneckerChainRecoveredColors -/
section
set_option autoImplicit false
namespace KroneckerChainRecoveredColors
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainRecoveredSkeleton
open KroneckerChainRecoveredVertices KroneckerColoredIncidenceIso KroneckerRetainedBlockSupport
open KroneckerGluedLinearRepresentation KroneckerActualSlotGluing KroneckerChainRepresentativeStability

variable {n m : ℕ} {d : Block n → ℕ} {d' : Block m → ℕ}
  {σ : ColorChoices n} {τ : ColorChoices m}
  (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
  (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
  (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
  (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
    finrank ℂ ((gluedRepresentative M).block.Space s))
  (j : Block n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem local_incidence_transport (s : (familyBlock M j).Source) (t : (familyBlock M j).Sink) :
    linearSupport (familyBlock N (chainBlockEquiv M N hd hd' e he j))
      (localSourceEquiv M N hd hd' e he j s) (localSinkEquiv M N hd hd' e he j t) ↔
    linearSupport (familyBlock M j) s t := by
  have h := e.incidence (.inr ⟨j,s⟩) ⟨j,t⟩
  rw [←local_source_natural M N hd hd' e he j s,←local_sink_natural M N hd hd' e he j t] at h
  simpa only [gluedRepresentative,linearSupport,internal_arrow_same] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The recovered block bijection restricts the global isomorphism to actual
colored reflected blocks, including every internal edge color. -/
noncomputable def localColoredIso : ColoredIso (familyColoring M j)
    (familyColoring N (chainBlockEquiv M N hd hd' e he j)) where
  source := localSourceEquiv M N hd hd' e he j
  sink := localSinkEquiv M N hd hd' e he j
  incidence := local_incidence_transport M N hd hd' e he j
  color := by
    intro s t h
    have hg : linearSupport (gluedRepresentative M).block (.inr ⟨j,s⟩) ⟨j,t⟩ := by
      simpa only [gluedRepresentative,linearSupport,internal_arrow_same] using h
    have hc := e.color (.inr ⟨j,s⟩) ⟨j,t⟩ hg
    simp only [←local_source_natural M N hd hd' e he j s,←local_sink_natural M N hd hd' e he j t] at hc
    exact hc

theorem recovered_block_dimensions : d' (chainBlockEquiv M N hd hd' e he j)=d j := by
  have hc := Fintype.card_congr (localSinkEquiv M N hd hd' e he j)
  rw [(representative_block_dimensions M hd j).2,
    (representative_block_dimensions N hd' _).2] at hc
  omega

end KroneckerChainRecoveredColors
end

/- Original module: KroneckerChainRecoveredSlots -/
section
set_option autoImplicit false
namespace KroneckerChainRecoveredSlots
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainRecoveredSkeleton
open KroneckerChainRecoveredVertices KroneckerChainRecoveredColors KroneckerChainIntrinsicTransport
open KroneckerColoredIncidenceIso KroneckerRetainedBlockSupport KroneckerGluedSupportGraph
open KroneckerGluedLinearRepresentation KroneckerActualSlotGluing KroneckerSlotIsoTransport

variable {n m : ℕ} {d : Block n → ℕ} {d' : Block m → ℕ}
  {σ : ColorChoices n} {τ : ColorChoices m}
  (M : RepresentativeFamily d σ) (N : RepresentativeFamily d' τ)
  (hd : ∀ j,0<d j) (hd' : ∀ j,0<d' j)
  (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
  (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
    finrank ℂ ((gluedRepresentative M).block.Space s))
  (i : Connector n) (j : Block n) (h : incidence i j)

theorem attachment_transport :
    localSinkEquiv M N hd hd' e he j (attachment (familyAssignment M) i j h)=
      attachment (familyAssignment N) (recoveredConnectorEquiv M N hd hd' e he i)
        (chainBlockEquiv M N hd hd' e he j) ((recovered_chain_incidence M N hd hd' e he i j).mpr h) := by
  have hg : linearSupport (gluedRepresentative M).block (.inl i)
      ⟨j,attachment (familyAssignment M) i j h⟩ :=
    (glued_arrow_support_iff _ _ _ _ _).mpr (GlueEdge.attachment i j h)
  have ht := (e.incidence _ _).mpr hg
  rw [←chain_connector_natural M N hd hd' e he i,
    ←local_sink_natural M N hd hd' e he j _] at ht
  obtain ⟨h',hv⟩ := (glue_edge_connector_iff _ _ _ _ _ _).mp
    ((glued_arrow_support_iff _ _ _ _ _).mp ht)
  exact hv.symm

theorem attachment_color_transport :
    ((familyAssignment N).slot (recoveredConnectorEquiv M N hd hd' e he i)
      (chainBlockEquiv M N hd hd' e he j) ((recovered_chain_incidence M N hd hd' e he i j).mpr h)).1.2=
    ((familyAssignment M).slot i j h).1.2 := by
  have hg : linearSupport (gluedRepresentative M).block (.inl i)
      ⟨j,attachment (familyAssignment M) i j h⟩ :=
    (glued_arrow_support_iff _ _ _ _ _).mpr (GlueEdge.attachment i j h)
  have hc := e.color _ _ hg
  simp only [←chain_connector_natural M N hd hd' e he i,
    ←local_sink_natural M N hd hd' e he j _,attachment_transport M N hd hd' e he i j h] at hc
  exact hc

/-- Arbitrary global isomorphisms carry the actual vacant attachment slots,
including their colors, through the recovered local colored isomorphism. -/
theorem marked_slot_transport :
    slotEquiv (localColoredIso M N hd hd' e he j) ((familyAssignment M).slot i j h)=
      (familyAssignment N).slot (recoveredConnectorEquiv M N hd hd' e he i)
        (chainBlockEquiv M N hd hd' e he j) ((recovered_chain_incidence M N hd hd' e he i j).mpr h) := by
  apply Subtype.ext
  exact Prod.ext (attachment_transport M N hd hd' e he i j h)
    (attachment_color_transport M N hd hd' e he i j h).symm

end KroneckerChainRecoveredSlots
end
