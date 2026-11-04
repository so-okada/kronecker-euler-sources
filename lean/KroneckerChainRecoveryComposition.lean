import KroneckerChainRecoveredSlots

set_option autoImplicit false
namespace KroneckerChainRecoveryComposition
open Module KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerChainIntrinsicTransport
open KroneckerChainRecoveredSkeleton KroneckerChainRecoveredVertices KroneckerColoredIncidenceIso

variable {n : ℕ} {d₁ d₂ d₃ : Block n → ℕ} {σ₁ σ₂ σ₃ : ColorChoices n}
  (M : RepresentativeFamily d₁ σ₁) (N : RepresentativeFamily d₂ σ₂) (P : RepresentativeFamily d₃ σ₃)
  (h₁ : ∀ j,0<d₁ j) (h₂ : ∀ j,0<d₂ j) (h₃ : ∀ j,0<d₃ j)
  (e : ColoredIso (gluedRepresentative M).coloring (gluedRepresentative N).coloring)
  (f : ColoredIso (gluedRepresentative N).coloring (gluedRepresentative P).coloring)
  (he : ∀ s,finrank ℂ ((gluedRepresentative N).block.Space (e.source s))=
    finrank ℂ ((gluedRepresentative M).block.Space s))
  (hf : ∀ s,finrank ℂ ((gluedRepresentative P).block.Space (f.source s))=
    finrank ℂ ((gluedRepresentative N).block.Space s))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem connector_composition (i : Connector n) :
    recoveredConnectorEquiv M P h₁ h₃ (e.trans f) (fun s => (hf (e.source s)).trans (he s)) i=
    recoveredConnectorEquiv N P h₂ h₃ f hf (recoveredConnectorEquiv M N h₁ h₂ e he i) := by
  apply Sum.inl_injective (β:= (Σ j,(familyBlock P j).Source))
  rw [chain_connector_natural]
  change f.source (e.source (.inl i))=_
  exact (congrArg f.source (chain_connector_natural M N h₁ h₂ e he i).symm).trans
    (chain_connector_natural N P h₂ h₃ f hf _).symm

theorem block_composition (j : Block n) :
    chainBlockEquiv M P h₁ h₃ (e.trans f) (fun s => (hf (e.source s)).trans (he s)) j=
    chainBlockEquiv N P h₂ h₃ f hf (chainBlockEquiv M N h₁ h₂ e he j) := by
  let t : (familyBlock M j).Sink := (0 : Fin (d₁ j+1))
  have hg := local_sink_natural M P h₁ h₃ (e.trans f) (fun s => (hf (e.source s)).trans (he s)) j t
  have he' := local_sink_natural M N h₁ h₂ e he j t
  have hf' := local_sink_natural N P h₂ h₃ f hf (chainBlockEquiv M N h₁ h₂ e he j)
    (localSinkEquiv M N h₁ h₂ e he j t)
  exact congrArg Sigma.fst (hg.trans ((congrArg f.sink he').symm.trans hf'.symm))

theorem connector_fixed_of_source_fixed
    (hfix : ∀ i,e.source (.inl i)=.inl i) (i : Connector n) :
    recoveredConnectorEquiv M N h₁ h₂ e he i=i :=
  Sum.inl_injective ((chain_connector_natural M N h₁ h₂ e he i).trans (hfix i))

theorem block_fixed_of_sink_fixed
    (hfix : ∀ j (t : (familyBlock M j).Sink),(e.sink ⟨j,t⟩).1=j) (j : Block n) :
    chainBlockEquiv M N h₁ h₂ e he j=j := by
  exact (congrArg Sigma.fst (local_sink_natural M N h₁ h₂ e he j (0 : Fin (d₁ j+1)))).trans (hfix j (0 : Fin (d₁ j+1)))

end KroneckerChainRecoveryComposition
