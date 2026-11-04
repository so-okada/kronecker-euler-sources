import KroneckerChainLocalSlotClasses
import KroneckerChainBinFamily

section

/- Original module: KroneckerSlotGluingIsomorphism -/
section
set_option autoImplicit false
namespace KroneckerSlotGluingIsomorphism
open KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport KroneckerProperColoredReflection
open KroneckerActualSlotGluing KroneckerColoredIncidenceIso KroneckerSlotIsoTransport
open KroneckerGluedSupportGraph KroneckerGluedProperColoring
attribute [local instance] Classical.propDecidable

variable {I J : Type} {B D : J → LinearCoverBlock} {R : I → J → Prop}
variable {C : ∀ j,ProperColoring (linearSupport (B j))}
variable {E : ∀ j,ProperColoring (linearSupport (D j))}

def sourceEquiv (f : ∀ j,ColoredIso (C j) (E j)) :
    (I ⊕ (Σ j,(B j).Source)) ≃ (I ⊕ (Σ j,(D j).Source)) :=
  Equiv.sumCongr (Equiv.refl I) (Equiv.sigmaCongrRight (fun j => (f j).source))

def sinkEquiv (f : ∀ j,ColoredIso (C j) (E j)) :
    (Σ j,(B j).Sink) ≃ (Σ j,(D j).Sink) :=
  Equiv.sigmaCongrRight (fun j => (f j).sink)

theorem glue_edge_map (S : SlotAssignment B R C) (T : SlotAssignment D R E)
    (f : ∀ j,ColoredIso (C j) (E j))
    (hf : ∀ i j (h : R i j),slotEquiv (f j) (S.slot i j h)=T.slot i j h)
    (s : I ⊕ (Σ j,(B j).Source)) (t : Σ j,(B j).Sink)
    (h : GlueEdge B R (attachment S) s t) :
    GlueEdge D R (attachment T) (sourceEquiv f s) (sinkEquiv f t) := by
  cases h with
  | internal j s t h =>
    exact GlueEdge.internal j ((f j).source s) ((f j).sink t) ((f j).incidence s t |>.mpr h)
  | attachment i j h =>
    have he := congrArg (fun q => q.1.1) (hf i j h)
    change (f j).sink (attachment S i j h)=attachment T i j h at he
    change GlueEdge D R (attachment T) (.inl i) ⟨j,(f j).sink (attachment S i j h)⟩
    rw [he]
    exact GlueEdge.attachment i j h

theorem glue_edge_iff (S : SlotAssignment B R C) (T : SlotAssignment D R E)
    (f : ∀ j,ColoredIso (C j) (E j))
    (hf : ∀ i j (h : R i j),slotEquiv (f j) (S.slot i j h)=T.slot i j h)
    (s : I ⊕ (Σ j,(B j).Source)) (t : Σ j,(B j).Sink) :
    GlueEdge D R (attachment T) (sourceEquiv f s) (sinkEquiv f t) ↔
      GlueEdge B R (attachment S) s t := by
  constructor
  · intro h
    have hr : ∀ i j (h : R i j),slotEquiv (f j).symm (T.slot i j h)=S.slot i j h := by
      intro i j h
      rw [←hf i j h]
      apply Subtype.ext
      exact Prod.ext ((f j).sink.symm_apply_apply _) rfl
    have hm := glue_edge_map T S (fun j => (f j).symm) hr _ _ h
    cases s with
    | inl i => simpa [sourceEquiv,sinkEquiv,ColoredIso.symm] using hm
    | inr p =>
      rcases p with ⟨j,s⟩
      simpa [sourceEquiv,sinkEquiv,ColoredIso.symm] using hm
  · exact glue_edge_map S T f hf s t

noncomputable def gluedColoredIso (S : SlotAssignment B R C) (T : SlotAssignment D R E)
    (f : ∀ j,ColoredIso (C j) (E j))
    (hf : ∀ i j (h : R i j),slotEquiv (f j) (S.slot i j h)=T.slot i j h) :
    ColoredIso (gluedProperColoring B R (attachment S) C (assignmentColors S))
      (gluedProperColoring D R (attachment T) E (assignmentColors T)) where
  source := sourceEquiv f
  sink := sinkEquiv f
  incidence := glue_edge_iff S T f hf
  color := by
    intro s t h
    cases h with
    | internal j s t h => exact (f j).color s t h
    | attachment i j h =>
      have he := congrArg (fun q => q.1.2) (hf i j h)
      exact he.symm

end KroneckerSlotGluingIsomorphism
end

/- Original module: KroneckerActualGluedColorTransport -/
section
set_option autoImplicit false
namespace KroneckerActualGluedColorTransport
open KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport KroneckerProperColoredReflection
open KroneckerActualSlotGluing KroneckerColoredIncidenceIso KroneckerSlotIsoTransport
open KroneckerGluedSupportGraph KroneckerGluedProperColoring KroneckerGluedLinearRepresentation
open KroneckerSlotGluingIsomorphism

def along {I J : Type} {R R' : I → J → Prop} (C : ProperColoring R)
    (h : ∀ i j,R' i j ↔ R i j) : ProperColoring R' where
  color := fun i j hij => C.color i j ((h i j).mp hij)
  at_source := by
    intro i u v he
    have hv := C.at_source i (a₁:=⟨u.1,(h i u.1).mp u.2⟩)
      (a₂:=⟨v.1,(h i v.1).mp v.2⟩) he
    exact Subtype.ext (congrArg (fun q : {j // R i j} => q.1) hv)
  at_sink := by
    intro j u v he
    have hv := C.at_sink j (a₁:=⟨u.1,(h u.1 j).mp u.2⟩)
      (a₂:=⟨v.1,(h v.1 j).mp v.2⟩) he
    exact Subtype.ext (congrArg (fun q : {i // R i j} => q.1) hv)

def isoAlong {I J K L : Type} {R R' : I → J → Prop} {S S' : K → L → Prop}
    {C : ProperColoring R} {D : ProperColoring S} (e : ColoredIso C D)
    (hR : ∀ i j,R' i j ↔ R i j) (hS : ∀ k l,S' k l ↔ S k l) :
    ColoredIso (along C hR) (along D hS) where
  source := e.source
  sink := e.sink
  incidence := fun i j => (hS _ _).trans ((e.incidence i j).trans (hR i j).symm)
  color := fun i j hij => e.color i j ((hR i j).mp hij)

variable {I J : Type} [Fintype I] [Fintype J] {B D : J → LinearCoverBlock}
variable {R : I → J → Prop} {C : ∀ j,ProperColoring (linearSupport (B j))}
variable {E : ∀ j,ProperColoring (linearSupport (D j))}

/-- The colors live on the nonzero arrows of the actual glued linear block. -/
noncomputable def actualColoring (S : SlotAssignment B R C) :
    ProperColoring (linearSupport (gluedBlock B R (attachment S))) :=
  along (gluedProperColoring B R (attachment S) C (assignmentColors S))
    (glued_arrow_support_iff B R (attachment S))

noncomputable def actualGluedIso (S : SlotAssignment B R C) (T : SlotAssignment D R E)
    (f : ∀ j,ColoredIso (C j) (E j))
    (hf : ∀ i j (h : R i j),slotEquiv (f j) (S.slot i j h)=T.slot i j h) :
    ColoredIso (actualColoring S) (actualColoring T) :=
  isoAlong (gluedColoredIso S T f hf) (glued_arrow_support_iff B R (attachment S))
    (glued_arrow_support_iff D R (attachment T))



end KroneckerActualGluedColorTransport
end

/- Original module: KroneckerChainRepresentativeIndependence -/
section
set_option autoImplicit false
namespace KroneckerChainRepresentativeIndependence
open KroneckerChainIncidence KroneckerChainPortColors KroneckerChainNeighborIndices
open KroneckerChainSlotAssignments KroneckerChainLocalSlotClasses KroneckerAssignedSlotObjects
open KroneckerReflectedSupportClasses KroneckerGluedLinearRepresentation KroneckerActualSlotGluing
open KroneckerActualGluedColorTransport
attribute [local instance] Classical.propDecidable

noncomputable def representedClass {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) : FamilyClass d σ := fun j => Quotient.mk _ (M j)

noncomputable def representatives {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (X : FamilyClass d σ) : RepresentativeFamily d σ := fun j => (X j).out

theorem representatives_correct {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (X : FamilyClass d σ) : representedClass (representatives X)=X := by
  funext j
  exact Quotient.out_eq (X j)

noncomputable def gluedRepresentative {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) : ColoredBlock :=
  ⟨gluedBlock (familyBlock M) incidence (attachment (familyAssignment M)),
    actualColoring (familyAssignment M)⟩


/-- This is a well-defined map to actual colored-support classes. Its global
forgetting fibers and the moduli/Euler interpretation are separate obligations. -/
noncomputable def glueClasses {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (X : FamilyClass d σ) : Quotient supportSetoid :=
  Quotient.mk supportSetoid (gluedRepresentative (representatives X))


end KroneckerChainRepresentativeIndependence
end
end

section

/- Original module: KroneckerChainFlowEquations -/
section
set_option autoImplicit false
namespace KroneckerChainFlowEquations
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainFlowWeights
open KroneckerChainBlockSizes KroneckerChainFlowRecovery KroneckerFlowEdgeExtension
open KroneckerSkeletonFlowExistence
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem left_column (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) :
    (∑ i : Connector n,weight x l r i (leftBlock n))=l 0 := by
  have h0 : ∀ i : Connector n,(0 : Fin (n+2))=i.castSucc ↔ i=0 := by
    intro i
    simp only [Fin.ext_iff,Fin.val_zero,Fin.val_castSucc]
    omega
  have hs : ∀ i : Connector n,(0 : Fin (n+2))≠i.succ := by
    intro i h
    have hv := congrArg Fin.val h
    change 0=i.val+1 at hv
    omega
  simp [leftBlock,weight,h0,hs]

theorem right_column (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) :
    (∑ i : Connector n,weight x l r i (rightBlock n))=r n := by
  have h0 : ∀ i : Connector n,Fin.last (n+1)≠i.castSucc := by
    intro i h; have hv := congrArg Fin.val h; have hi := i.isLt; simp at hv; omega
  have hs : ∀ i : Connector n,Fin.last (n+1)=i.succ ↔ i=Fin.last n := by
    intro i; simp [Fin.ext_iff,eq_comm]
  simp [rightBlock,weight,h0,hs]

theorem middle_column {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) (t : Connector n) :
    (∑ i : Connector n,weight x l r i (middleBlock t))=x+1-l t-r t := by
  simp [middleBlock,weight]

theorem internal_column {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) (t : Fin n) :
    (∑ i : Connector n,weight x l r i (internalBlock t))=r t+l (t+1) := by
  have h0 : ∀ i : Connector n,t.castSucc.succ=i.castSucc ↔ i=t.succ := by
    intro i; simp [Fin.ext_iff,eq_comm]
  have hs : ∀ i : Connector n,t.castSucc.succ=i.succ ↔ i=t.castSucc := by
    intro i; simp [Fin.ext_iff,eq_comm]
  simp [internalBlock,weight,h0,hs,Finset.sum_add_distrib,add_comm]

theorem column_balance (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (j : Block n) :
    (∑ i,extendFlow (chainFlow x l r) i j)=x-blockSize n x l r j := by
  simp only [flow_extension]
  rcases block_cases j with rfl|rfl|⟨t,rfl⟩|⟨t,rfl⟩
  · rw [left_column,size_left]; simp [leftEnd]
  · rw [right_column,size_right]; simp [rightEnd]
  · rw [middle_column,size_middle]; simp only [middleSize]; ring
  · rw [internal_column,size_internal]; simp only [internalSize]; ring

/-- The explicit left, middle and right flows solve the actual incidence
equations of the constructed chain, for the manuscript's block sizes. -/
theorem chain_flow_equations (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (a : Block n → ℕ)
    (ha : ∀ j,(a j : ℝ)=blockSize n x l r j) :
    FlowEquations x a (chainFlow x l r) := by
  exact ⟨row_balance x l r,fun j => (column_balance n x l r j).trans (by rw [ha])⟩

end KroneckerChainFlowEquations
end

/- Original module: KroneckerChainIntegerDimensions -/
section
set_option autoImplicit false
namespace KroneckerChainIntegerDimensions
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainBlockSizes
open KroneckerChainFlowIntegrality
open scoped BigOperators

theorem all_block_sizes_integral (n a : ℕ) (x : ℝ) (l r : ℕ → ℝ)
    (ha : ((n : ℝ)+2)*x=a)
    (hl : ∀ t≤n,OnLattice (((t : ℝ)+1)*x) (l t))
    (hr : ∀ t≤n,OnLattice (-((t : ℝ)+1)*x) (r t)) :
    ∀ j : Block n,∃ z : ℤ,blockSize n x l r j=z := by
  intro j
  rcases block_cases j with rfl|rfl|⟨t,rfl⟩|⟨t,rfl⟩
  · rw [size_left]
    apply chain_left_integral x l
    simpa using hl 0 (by omega)
  · rw [size_right]
    exact chain_right_integral x n a r ha (hr n le_rfl)
  · rw [size_middle]
    exact chain_middle_integral x l r t (hl t (by omega)) (hr t (by omega))
  · rw [size_internal]
    exact chain_internal_integral x l r t (hr t (by omega)) (hl (t+1) (by omega))

theorem natural_dimensions_unique (n : ℕ) (x : ℝ) (l r : ℕ → ℝ)
    (hz : ∀ j : Block n,∃ z : ℤ,blockSize n x l r j=z)
    (hp : ∀ j : Block n,0≤blockSize n x l r j) :
    ∃! a : Block n → ℕ,∀ j,(a j : ℝ)=blockSize n x l r j := by
  classical
  choose z hz using hz
  have hn : ∀ j,0≤z j := by intro j; exact_mod_cast (hz j ▸ hp j)
  refine ⟨fun j => (z j).toNat,?_,?_⟩
  · intro j
    rw [hz j]
    exact_mod_cast Int.toNat_of_nonneg (hn j)
  · intro b hb
    funext j
    have h : (b j : ℝ)=((z j).toNat : ℝ) := by
      rw [hb j,hz j]
      exact_mod_cast (Int.toNat_of_nonneg (hn j)).symm
    exact_mod_cast h

theorem natural_dimension_balance (n a : ℕ) (x : ℝ) (l r : ℕ → ℝ)
    (d : Block n → ℕ) (hd : ∀ j,(d j : ℝ)=blockSize n x l r j)
    (ha : ((n : ℝ)+2)*x=a) : (∑ j,d j)+(n+1)=a := by
  have hs := block_size_sum n x l r
  have hc : (∑ j,(d j : ℝ))+((n : ℝ)+1)=a := by
    simp_rw [hd]
    rw [hs,ha]
    ring
  exact_mod_cast hc

end KroneckerChainIntegerDimensions
end

/- Original module: KroneckerChainSkeletonTree -/
section
set_option autoImplicit false
namespace KroneckerChainSkeletonTree
open SimpleGraph KroneckerBipartiteIncidence KroneckerChainIncidence
open KroneckerGluedSupportTree
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem connectors_reachable (n : ℕ) (i : Connector n) :
    (incidenceGraph (@incidence n)).Reachable (.inl 0) (.inl i) := by
  induction i using Fin.induction with
  | zero => exact Reachable.refl _
  | succ i hi =>
    have hl : (incidenceGraph (@incidence n)).Adj
        (.inl i.castSucc) (.inr (.inl i.castSucc.succ)) := Or.inr rfl
    have hr : (incidenceGraph (@incidence n)).Adj
        (.inr (.inl i.castSucc.succ)) (.inl i.succ) := Or.inl (by ext; rfl)
    exact hi.trans (hl.reachable.trans hr.reachable)

theorem chain_connected (n : ℕ) : (incidenceGraph (@incidence n)).Connected := by
  have hr : ∀ v,(incidenceGraph (@incidence n)).Reachable (.inl 0) v := by
    intro v
    cases v with
    | inl i => exact connectors_reachable n i
    | inr j =>
      cases j with
      | inr j =>
        exact (connectors_reachable n j).trans
          (show (incidenceGraph (@incidence n)).Adj (.inl j) (.inr (.inr j)) from rfl).reachable
      | inl j =>
        refine Fin.cases ?_ (fun i => ?_) j
        · exact (show (incidenceGraph (@incidence n)).Adj (.inl 0) (.inr (.inl 0))
            from Or.inl rfl).reachable
        · exact (connectors_reachable n i).trans
            (show (incidenceGraph (@incidence n)).Adj (.inl i) (.inr (.inl i.succ))
              from Or.inr rfl).reachable
  exact { preconnected := fun u v => (hr u).symm.trans (hr v), nonempty := ⟨.inl 0⟩ }

theorem chain_tree (n : ℕ) : (incidenceGraph (@incidence n)).IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨chain_connected n,?_⟩
  rw [Nat.card_eq_fintype_card,←edgeFinset_card,incidence_edgeFinset_count,
    KroneckerTreeFlowUniqueness.incidence_edge_count]
  simp [connector_degree,Connector,Block]
  omega

end KroneckerChainSkeletonTree
end

/- Original module: KroneckerChainStabilityCriterion -/
section
set_option autoImplicit false
namespace KroneckerChainStabilityCriterion
open KroneckerChainIncidence KroneckerChainSkeletonTree KroneckerChainBlockSizes
open KroneckerChainFlowWeights KroneckerChainFlowEquations KroneckerChainBinFamily
open KroneckerLinearCoverBlocks KroneckerGluingKingWeight KroneckerTreeGluingCriterion
open KroneckerGluedSubrepEquivalence KroneckerGluedLinearRepresentation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem chain_slope (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (B : Block n → LinearCoverBlock)
    (hB : ∀ j,(sourceDimension (B j) : ℝ)=blockSize n x l r j) :
    slopeParameter (I:=Connector n) B=x := by
  have hb := slope_parameter_balance (I:=Connector n) B
  simp only [Connector,Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hb
  simp_rw [hB] at hb
  rw [block_size_sum] at hb
  have hn : (0 : ℝ)≤n := Nat.cast_nonneg n
  nlinarith

/-- Stability of the concrete chain is exactly positivity of its three
explicit port flows, including the one-connector case. -/
theorem chain_stability_iff (n : ℕ) (x : ℝ) (l r : ℕ → ℝ)
    (B : Block n → LinearCoverBlock)
    (attach : ∀ i j,incidence i j → (B j).Sink)
    (hdef : ∀ j,PositiveDefect (B j))
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1)
    (hB : ∀ j,(sourceDimension (B j) : ℝ)=blockSize n x l r j) :
    BlockKingStable (gluedBlock B incidence attach) ↔
      ∀ i : Connector n,0<l i ∧ 0<x+1-l i-r i ∧ 0<r i := by
  have hf := chain_flow_equations n x l r (fun j => sourceDimension (B j)) hB
  rw [←chain_slope n x l r B hB] at hf
  rw [global_stability_iff,tree_flow_stability_criterion B incidence attach
    (chain_tree n) connector_degree hdef hdim _ hf,flow_positive_iff]
  rw [chain_slope n x l r B hB]

theorem bin_chain_stable (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ)
    (hx : 100000≤x) (D : BinData n x l r i h)
    (B : Block n → LinearCoverBlock)
    (attach : ∀ i j,incidence i j → (B j).Sink)
    (hdef : ∀ j,PositiveDefect (B j))
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1)
    (hB : ∀ j,(sourceDimension (B j) : ℝ)=blockSize n x l r j) :
    BlockKingStable (gluedBlock B incidence attach) := by
  apply (chain_stability_iff n x l r B attach hdef hdim hB).mpr
  exact (flow_positive_iff x l r).mp (bin_flows_positive n x l r i h hx D)

end KroneckerChainStabilityCriterion
end

/- Original module: KroneckerStableSupportedChain -/
section
set_option autoImplicit false
namespace KroneckerStableSupportedChain
open KroneckerChainIncidence KroneckerChainSkeletonTree KroneckerChainBlockSizes
open KroneckerChainStabilityCriterion KroneckerChainBinFamily KroneckerChainIntegerDimensions
open KroneckerLinearCoverBlocks KroneckerSaturatedBlockData KroneckerRetainedBlockSupport
open KroneckerGluedLinearRepresentation KroneckerGluedSubrepEquivalence KroneckerGluingKingWeight
open KroneckerCoverTitsForm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem supported_chain_stable_tree (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ)
    (hx : 100000≤x) (D : BinData n x l r i h) (T : Block n → SaturatedBlockData)
    (attach : ∀ i j,incidence i j → (supportedBlock (T j)).Sink)
    (hd : ∀ j,(((T j).sources-1 : ℕ) : ℝ)=blockSize n x l r j) :
    BlockKingStable (gluedBlock (fun j => supportedBlock (T j)) incidence attach) ∧
    (supportGraph (gluedBlock (fun j => supportedBlock (T j)) incidence attach)).IsTree ∧
    titsForm (gluedBlock (fun j => supportedBlock (T j)) incidence attach)=1 := by
  have hdim : ∀ j,Fintype.card (supportedBlock (T j)).Sink=
      sourceDimension (supportedBlock (T j))+1 := by
    intro j
    obtain ⟨ha,hb⟩ := supported_block_dimensions (T j)
    have hn := (T j).sources_ge_two
    omega
  have htree := supported_tree_gluing T incidence attach (chain_tree n) connector_degree
  refine ⟨bin_chain_stable n x l r i h hx D _ attach
    (fun j => supported_block_defect (T j)) hdim ?_,htree.1,htree.2.1⟩
  intro j
  rw [(supported_block_dimensions (T j)).1]
  exact hd j

theorem supported_chain_dimensions (n a : ℕ) (x : ℝ) (l r : ℕ → ℝ)
    (T : Block n → SaturatedBlockData)
    (attach : ∀ i j,incidence i j → (supportedBlock (T j)).Sink)
    (hd : ∀ j,(((T j).sources-1 : ℕ) : ℝ)=blockSize n x l r j)
    (ha : ((n : ℝ)+2)*x=a) :
    sourceDimension (gluedBlock (fun j => supportedBlock (T j)) incidence attach)=a ∧
    Fintype.card (gluedBlock (fun j => supportedBlock (T j)) incidence attach).Sink=a+(n+2) := by
  have hs := natural_dimension_balance n a x l r (fun j => (T j).sources-1) hd ha
  have hb : ∀ j,sourceDimension (supportedBlock (T j))=(T j).sources-1 :=
    fun j => (supported_block_dimensions (T j)).1
  have htotal : totalSource (I:=Connector n) (fun j => supportedBlock (T j))=a := by
    simpa only [totalSource,Connector,Fintype.card_fin,hb] using hs
  have hdim : ∀ j,Fintype.card (supportedBlock (T j)).Sink=
      sourceDimension (supportedBlock (T j))+1 := by
    intro j
    obtain ⟨hb,hc⟩ := supported_block_dimensions (T j)
    have hn := (T j).sources_ge_two
    omega
  have ht := glued_total_dimension (fun j => supportedBlock (T j)) incidence
    (chain_tree n) connector_degree hdim
  have hg := glued_representation_dimensions (fun j => supportedBlock (T j)) incidence attach
  rw [htotal] at ht
  constructor
  · exact hg.1.trans htotal
  · rw [hg.2,ht]; simp [Connector,Nat.add_assoc]

end KroneckerStableSupportedChain
end

/- Original module: KroneckerChainRepresentativeStability -/
section
set_option autoImplicit false
namespace KroneckerChainRepresentativeStability
open KroneckerChainIncidence KroneckerChainPortColors KroneckerChainSlotAssignments
open KroneckerChainRepresentativeIndependence KroneckerStableSupportedChain KroneckerChainBinFamily
open KroneckerChainBlockSizes KroneckerSaturatedBlockData KroneckerSaturatedTableAction
open KroneckerFiniteColoredTables KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerActualSlotGluing KroneckerGluedSubrepEquivalence KroneckerCoverTitsForm
attribute [local instance] Classical.propDecidable

noncomputable def tableData (d : ℕ) (hd : 0<d)
    (T : SaturatedTable (Fin (d+1)) (Fin (2*(d+1)+1))) : SaturatedBlockData where
  sources := d+1
  sinks := 2*(d+1)+1
  sources_ge_two := by omega
  incidence := Incidence T.1
  tree := T.2.1
  saturated := T.2.2
  coloring := coloring T.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem representative_block_dimensions {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (hd : ∀ j,0<d j) (j : Block n) :
    sourceDimension (familyBlock M j)=d j ∧ Fintype.card (familyBlock M j).Sink=d j+1 := by
  have h := supported_block_dimensions (tableData (d j) (hd j) (M j).1)
  simpa [tableData,supportedBlock,familyBlock] using h

/-- Every representative of every marked slot-class choice is an actual
stable tree representation with Tits form one under the manuscript bin data. -/
theorem representative_stable_tree {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (hd : ∀ j,0<d j)
    (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ) (hx : 100000≤x)
    (D : BinData n x l r i h) (hs : ∀ j,(d j : ℝ)=blockSize n x l r j) :
    BlockKingStable (gluedRepresentative M).block ∧
    (supportGraph (gluedRepresentative M).block).IsTree ∧
    titsForm (gluedRepresentative M).block=1 := by
  let T := fun j => tableData (d j) (hd j) (M j).1
  apply supported_chain_stable_tree n x l r i h hx D T (attachment (familyAssignment M))
  intro j
  simpa [T,tableData] using hs j

theorem representative_total_dimensions {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (hd : ∀ j,0<d j)
    (a : ℕ) (x : ℝ) (l r : ℕ → ℝ)
    (hs : ∀ j,(d j : ℝ)=blockSize n x l r j) (ha : ((n : ℝ)+2)*x=a) :
    sourceDimension (gluedRepresentative M).block=a ∧
    Fintype.card (gluedRepresentative M).block.Sink=a+(n+2) := by
  let T := fun j => tableData (d j) (hd j) (M j).1
  apply supported_chain_dimensions n a x l r T (attachment (familyAssignment M)) ?_ ha
  intro j
  simpa [T,tableData] using hs j

end KroneckerChainRepresentativeStability
end
end

