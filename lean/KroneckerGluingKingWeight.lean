import KroneckerGluedSubrepresentations
import KroneckerTreeCutComponents
import KroneckerSkeletonFlowExistence

/- Original module: KroneckerPositiveGluingWeight -/
section
set_option autoImplicit false
namespace KroneckerPositiveGluingWeight
open SimpleGraph KroneckerBipartiteIncidence KroneckerFlowBoundaryIdentity
open KroneckerPositiveFlowBoundary
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def blockWeight (x : ℝ) (u v : ℕ) : ℝ := x*((v : ℝ)-(u : ℝ))-(u : ℝ)

theorem block_weight_lower (x : ℝ) (u v a : ℕ) (hx : 0≤x)
    (hdef : u+1≤v) (hu : u≤a) : x-a≤blockWeight x u v := by
  have hd : (u : ℝ)+1≤v := by exact_mod_cast hdef
  have ha : (u : ℝ)≤a := by exact_mod_cast hu
  dsimp [blockWeight]
  nlinarith

theorem block_weight_strict (x : ℝ) (u v a : ℕ) (hx : 0≤x)
    (hdef : u+1≤v) (hu : u<a) : x-a<blockWeight x u v := by
  have hd : (u : ℝ)+1≤v := by exact_mod_cast hdef
  have ha : (u : ℝ)<a := by exact_mod_cast hu
  dsimp [blockWeight]
  nlinarith

/-- The numerical stability step. Flow existence and construction of the glued
representation are separate internal obligations, not external assumptions. -/
theorem positive_gluing_weight {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hc : (incidenceGraph R).Connected)
    (f : I → J → ℝ) (hf : ∀ i j,0≤f i j) (hpos : ∀ i j,R i j → 0<f i j)
    (hoff : ∀ i j,¬R i j → f i j=0) (x : ℝ) (hx : 0≤x) (a u v : J → ℕ)
    (hrow : ∀ i,∑ j,f i j=x+1) (hcol : ∀ j,∑ i,f i j=x-a j)
    (C : Finset I) (B : Finset J) (hB : B.Nonempty)
    (hclosed : ∀ i∈C,∀ j,R i j → j∈B)
    (hzero : ∀ j∉B,u j=0 ∧ v j=0) (hdef : ∀ j∈B,u j+1≤v j)
    (hu : ∀ j,u j≤a j)
    (hproper : (∑ j,u j)+(∑ j,v j)+C.card<
      (∑ j,a j)+(∑ j,(a j+1))+Fintype.card I) :
    0<(∑ j,blockWeight x (u j) (v j))-(x+1)*(C.card : ℝ) := by
  have hfclosed : ∀ i∈C,∀ j∉B,f i j=0 := by
    intro i hi j hj
    exact hoff i j (fun hij => hj (hclosed i hi j hij))
  have hflux : boundaryFlux f C B=(∑ j∈B,(x-(a j : ℝ)))-(x+1)*(C.card : ℝ) := by
    rw [←boundary_demand_difference f C B hfclosed]
    simp [hrow,hcol,mul_comm]
    ring
  have hweights : (∑ j,blockWeight x (u j) (v j))=∑ j∈B,blockWeight x (u j) (v j) := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.subset_univ B)
    intro j _ hj
    simp [blockWeight,(hzero j hj).1,(hzero j hj).2]
  have hle : (∑ j∈B,(x-(a j : ℝ)))≤∑ j∈B,blockWeight x (u j) (v j) :=
    Finset.sum_le_sum (fun j hj => block_weight_lower x _ _ _ hx (hdef j hj) (hu j))
  rw [hweights]
  by_cases hfull : C=Finset.univ ∧ B=Finset.univ
  · have hex : ∃ j∈B,u j<a j := by
      by_contra h
      push Not at h
      have hueq : ∀ j,u j=a j := fun j => Nat.le_antisymm (hu j) (h j (by simp [hfull.2]))
      have hvle : (∑ j,(a j+1))≤∑ j,v j :=
        Finset.sum_le_sum (fun j _ => by simpa [hueq] using hdef j (by simp [hfull.2]))
      simp only [hueq,hfull.1,Finset.card_univ] at hproper
      omega
    have hlt : (∑ j∈B,(x-(a j : ℝ)))<∑ j∈B,blockWeight x (u j) (v j) := by
      apply Finset.sum_lt_sum (fun j hj => block_weight_lower x _ _ _ hx (hdef j hj) (hu j))
      obtain ⟨j,hj,hja⟩ := hex
      exact ⟨j,hj,block_weight_strict x _ _ _ hx (hdef j hj) hja⟩
    have hn := boundary_flux_nonnegative f C B hf
    rw [hflux] at hn
    linarith
  · have hp := positive_boundary_flux R hc f hf hpos C B hB hclosed hfull
    rw [hflux] at hp
    linarith

theorem gluing_total_weight_formula {J : Type*} [Fintype J]
    (x : ℝ) (u v : J → ℕ) (c : ℕ) :
    x*((∑ j,(v j : ℝ))-((∑ j,(u j : ℝ))+c))-((∑ j,(u j : ℝ))+c)=
      (∑ j,blockWeight x (u j) (v j))-(x+1)*c := by
  simp only [blockWeight,Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

end KroneckerPositiveGluingWeight
end

/- Original module: KroneckerPositiveGluedStability -/
section
set_option autoImplicit false
namespace KroneckerPositiveGluedStability
open Module SimpleGraph KroneckerLinearCoverBlocks KroneckerGluedSubrepresentations
open KroneckerPositiveGluingWeight KroneckerBipartiteIncidence
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def gluedSourceSize {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) : ℕ := (∑ j,sourceSize (S.block j))+(chosenConnectors S).card

noncomputable def gluedSinkSize {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) : ℕ := ∑ j,sinkSize (S.block j)

noncomputable def gluedWeight {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (x : ℝ) (S : GluedSubrep B R attach) : ℝ :=
  x*((gluedSinkSize S : ℝ)-(gluedSourceSize S : ℝ))-(gluedSourceSize S : ℝ)

def NormalizedStable {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (x : ℝ) : Prop := ∀ S : GluedSubrep B R attach,
      0<gluedSourceSize S+gluedSinkSize S →
      gluedSourceSize S+gluedSinkSize S<
        (∑ j,sourceDimension (B j))+Fintype.card I+(∑ j,Fintype.card (B j).Sink) →
      0<gluedWeight x S

theorem occupied_nonempty {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) (hneigh : ∀ i,∃ j,R i j)
    (hn : 0<gluedSourceSize S+gluedSinkSize S) : (occupiedBlocks S).Nonempty := by
  by_contra h
  have he : occupiedBlocks S=∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : ∀ j,sourceSize (S.block j)=0 ∧ sinkSize (S.block j)=0 :=
    fun j => empty_block_dimensions S j (by simp [he])
  have hc : 0<(chosenConnectors S).card := by
    simpa [gluedSourceSize,gluedSinkSize,fun j => (hz j).1,fun j => (hz j).2] using hn
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hc
  obtain ⟨j,hij⟩ := hneigh i
  have hj := attachment_forces_occupied S hi hij
  simp [he] at hj

theorem glued_weight_decomposition {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (x : ℝ) (S : GluedSubrep B R attach) :
    gluedWeight x S=(∑ j,blockWeight x (sourceSize (S.block j)) (sinkSize (S.block j)))-
      (x+1)*((chosenConnectors S).card : ℝ) := by
  simpa [gluedWeight,gluedSourceSize,gluedSinkSize,Nat.cast_sum] using
    gluing_total_weight_formula x (fun j => sourceSize (S.block j))
      (fun j => sinkSize (S.block j)) (chosenConnectors S).card

/-- Positive flows imply stability for every actual vertexwise subrepresentation
of the blocks together with the identity attachment arrows. -/
theorem positive_flows_imply_stability {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hc : (incidenceGraph R).Connected) (hneigh : ∀ i,∃ j,R i j)
    (hdef : ∀ j,PositiveDefect (B j))
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1)
    (f : I → J → ℝ) (hf : ∀ i j,0≤f i j) (hpos : ∀ i j,R i j → 0<f i j)
    (hoff : ∀ i j,¬R i j → f i j=0) (x : ℝ) (hx : 0≤x)
    (hrow : ∀ i,∑ j,f i j=x+1) (hcol : ∀ j,∑ i,f i j=x-sourceDimension (B j)) :
    NormalizedStable B R attach x := by
  intro S hn hp
  have hB := occupied_nonempty S hneigh hn
  have hd : ∀ j∈occupiedBlocks S,sourceSize (S.block j)+1≤sinkSize (S.block j) := by
    intro j hj
    have hn : 0<sourceSize (S.block j)+sinkSize (S.block j) := by
      simpa [occupiedBlocks] using hj
    exact hdef j (S.block j) hn
  have hp' : (∑ j,sourceSize (S.block j))+(∑ j,sinkSize (S.block j))+
      (chosenConnectors S).card<(∑ j,sourceDimension (B j))+
      (∑ j,(sourceDimension (B j)+1))+Fintype.card I := by
    simp only [gluedSourceSize,gluedSinkSize,hdim] at hp
    omega
  rw [glued_weight_decomposition]
  exact positive_gluing_weight R hc f hf hpos hoff x hx (fun j => sourceDimension (B j))
    (fun j => sourceSize (S.block j)) (fun j => sinkSize (S.block j)) hrow hcol
    (chosenConnectors S) (occupiedBlocks S) hB
    (fun i hi j hij => attachment_forces_occupied S hi hij)
    (fun j hj => empty_block_dimensions S j hj) hd
    (fun j => block_source_bound (S.block j)) hp'

end KroneckerPositiveGluedStability
end

/- Original module: KroneckerCutGluedSubobjects -/
section
set_option autoImplicit false
namespace KroneckerCutGluedSubobjects
open Module KroneckerLinearCoverBlocks KroneckerGluedSubrepresentations
open KroneckerPositiveGluedStability KroneckerPositiveGluingWeight
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Full block spaces and full connector spaces on a connector-closed subset
form an actual subrepresentation of the glued arrow system. -/
noncomputable def closedSubrep {I J : Type} (B : J → LinearCoverBlock)
    (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : Finset I) (D : Finset J) (hclosed : ∀ i∈C,∀ j,R i j → j∈D) :
    GluedSubrep B R attach where
  block := fun j => if j∈D then fullBlock (B j) else zeroBlock (B j)
  connector := fun i => if i∈C then ⊤ else ⊥
  attachment := by
    intro i j hij x hx
    by_cases hi : i∈C
    · simp [hclosed i hi j hij,fullBlock]
    · have hx0 : x=0 := by simpa [hi] using hx
      subst x
      exact Submodule.zero_mem _

theorem closed_subrep_connectors {I J : Type} [Fintype I]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : Finset I) (D : Finset J) (hclosed : ∀ i∈C,∀ j,R i j → j∈D) :
    chosenConnectors (closedSubrep B R attach C D hclosed)=C := by
  classical
  ext i
  by_cases hi : i∈C <;> simp [chosenConnectors,closedSubrep,hi]

theorem closed_block_dimensions {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : Finset I) (D : Finset J) (hclosed : ∀ i∈C,∀ j,R i j → j∈D) (j : J) :
    sourceSize ((closedSubrep B R attach C D hclosed).block j)=
      (if j∈D then sourceDimension (B j) else 0) ∧
    sinkSize ((closedSubrep B R attach C D hclosed).block j)=
      (if j∈D then Fintype.card (B j).Sink else 0) := by
  by_cases hj : j∈D
  · simpa only [closedSubrep,ite_eq_left hj] using full_block_dimensions (B j)
  · simpa only [closedSubrep,ite_eq_right hj] using zero_block_dimensions (B j)

theorem closed_subrep_dimensions {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : Finset I) (D : Finset J) (hclosed : ∀ i∈C,∀ j,R i j → j∈D) :
    gluedSourceSize (closedSubrep B R attach C D hclosed)=(∑ j∈D,sourceDimension (B j))+C.card ∧
    gluedSinkSize (closedSubrep B R attach C D hclosed)=∑ j∈D,Fintype.card (B j).Sink := by
  simp only [gluedSourceSize,gluedSinkSize,closed_subrep_connectors,
    fun j => (closed_block_dimensions B R attach C D hclosed j).1,
    fun j => (closed_block_dimensions B R attach C D hclosed j).2]
  simp

theorem closed_subrep_weight {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : Finset I) (D : Finset J) (hclosed : ∀ i∈C,∀ j,R i j → j∈D)
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1) (x : ℝ) :
    gluedWeight x (closedSubrep B R attach C D hclosed)=
      (∑ j∈D,(x-(sourceDimension (B j) : ℝ)))-(x+1)*(C.card : ℝ) := by
  rw [glued_weight_decomposition,closed_subrep_connectors]
  congr 1
  have he : ∀ j,blockWeight x
      (sourceSize ((closedSubrep B R attach C D hclosed).block j))
      (sinkSize ((closedSubrep B R attach C D hclosed).block j))=
      if j∈D then x-(sourceDimension (B j) : ℝ) else 0 := by
    intro j
    rw [(closed_block_dimensions B R attach C D hclosed j).1,
      (closed_block_dimensions B R attach C D hclosed j).2]
    by_cases hj : j∈D
    · simp [hj,hdim,blockWeight]
    · simp [hj,blockWeight]
  simp_rw [he]
  simp

end KroneckerCutGluedSubobjects
end

/- Original module: KroneckerTreeCutFlow -/
section
set_option autoImplicit false
namespace KroneckerTreeCutFlow
open SimpleGraph KroneckerBipartiteIncidence KroneckerTreeCutComponents
open KroneckerFlowBoundaryIdentity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem cut_boundary_flux {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (hT : (incidenceGraph R).IsTree)
    (f : I → J → ℝ) (hoff : ∀ i j,¬R i j → f i j=0)
    {i₀ : I} {j₀ : J} (h₀ : R i₀ j₀) :
    boundaryFlux f (cutConnectors R i₀ j₀) (cutBlocks R i₀ j₀)=f i₀ j₀ := by
  classical
  unfold boundaryFlux
  rw [Finset.sum_eq_single j₀]
  · rw [Finset.sum_eq_single i₀]
    · intro i hi hne
      by_cases h : R i j₀
      · exact False.elim (hne (cut_boundary_unique R i₀ j₀
          (Finset.mem_sdiff.mp hi).2 (cut_block_included R i₀ j₀) h).1)
      · exact hoff i j₀ h
    · intro hi
      exact False.elim (hi (by simp [cut_connector_excluded hT h₀]))
  · intro j hj hne
    apply Finset.sum_eq_zero
    intro i hi
    by_cases h : R i j
    · exact False.elim (hne (cut_boundary_unique R i₀ j₀ (Finset.mem_sdiff.mp hi).2 hj h).2)
    · exact hoff i j h
  · intro hj
    exact False.elim (hj (cut_block_included R i₀ j₀))

/-- The block-side cut has normalized weight equal to the cut edge's flow. -/
theorem cut_demand_equals_flow {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (hT : (incidenceGraph R).IsTree)
    (f : I → J → ℝ) (hoff : ∀ i j,¬R i j → f i j=0)
    (x : ℝ) (a : J → ℕ) (hrow : ∀ i,∑ j,f i j=x+1)
    (hcol : ∀ j,∑ i,f i j=x-a j) {i₀ : I} {j₀ : J} (h₀ : R i₀ j₀) :
    (∑ j∈cutBlocks R i₀ j₀,(x-(a j : ℝ)))-
      (x+1)*((cutConnectors R i₀ j₀).card : ℝ)=f i₀ j₀ := by
  have hc : ∀ i∈cutConnectors R i₀ j₀,∀ j∉cutBlocks R i₀ j₀,f i j=0 := by
    intro i hi j hj
    exact hoff i j (fun h => hj (cut_is_connector_closed hT h₀ hi h))
  have h := boundary_demand_difference f (cutConnectors R i₀ j₀) (cutBlocks R i₀ j₀) hc
  rw [cut_boundary_flux hT f hoff h₀] at h
  simpa [hrow,hcol,mul_comm,mul_add] using h

end KroneckerTreeCutFlow
end

/- Original module: KroneckerGluedCutStability -/
section
set_option autoImplicit false
namespace KroneckerGluedCutStability
open SimpleGraph KroneckerBipartiteIncidence KroneckerTreeCutComponents KroneckerTreeCutFlow
open KroneckerLinearCoverBlocks KroneckerGluedSubrepresentations
open KroneckerPositiveGluedStability KroneckerCutGluedSubobjects
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem closed_subrep_nonzero {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : Finset I) (D : Finset J) (hclosed : ∀ i∈C,∀ j,R i j → j∈D)
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1) (hD : D.Nonempty) :
    0<gluedSourceSize (closedSubrep B R attach C D hclosed)+
      gluedSinkSize (closedSubrep B R attach C D hclosed) := by
  rw [(closed_subrep_dimensions B R attach C D hclosed).1,
    (closed_subrep_dimensions B R attach C D hclosed).2]
  obtain ⟨j,hj⟩ := hD
  have hs : Fintype.card (B j).Sink≤∑ k∈D,Fintype.card (B k).Sink :=
    Finset.single_le_sum (f:=fun k => Fintype.card (B k).Sink) (fun k _ => Nat.zero_le _) hj
  rw [hdim j] at hs
  omega

theorem closed_subrep_proper {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : Finset I) (D : Finset J) (hclosed : ∀ i∈C,∀ j,R i j → j∈D)
    (hC : C.card<Fintype.card I) :
    gluedSourceSize (closedSubrep B R attach C D hclosed)+
      gluedSinkSize (closedSubrep B R attach C D hclosed)<
      (∑ j,sourceDimension (B j))+Fintype.card I+(∑ j,Fintype.card (B j).Sink) := by
  rw [(closed_subrep_dimensions B R attach C D hclosed).1,
    (closed_subrep_dimensions B R attach C D hclosed).2]
  have hu : (∑ j∈D,sourceDimension (B j))≤∑ j,sourceDimension (B j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
  have hv : (∑ j∈D,Fintype.card (B j).Sink)≤∑ j,Fintype.card (B j).Sink :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
  omega

/-- The converse uses explicit cut subobjects, with no positive-flow premise. -/
theorem stability_implies_positive_flows {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hT : (incidenceGraph R).IsTree)
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1)
    (f : I → J → ℝ) (hoff : ∀ i j,¬R i j → f i j=0) (x : ℝ)
    (hrow : ∀ i,∑ j,f i j=x+1) (hcol : ∀ j,∑ i,f i j=x-sourceDimension (B j))
    (hs : NormalizedStable B R attach x) : ∀ i j,R i j → 0<f i j := by
  classical
  intro i j hij
  let C := cutConnectors R i j
  let D := cutBlocks R i j
  have hclosed : ∀ k∈C,∀ l,R k l → l∈D := fun k hk l hkl =>
    cut_is_connector_closed hT hij hk hkl
  have hi : i∉C := cut_connector_excluded hT hij
  have hC : C.card<Fintype.card I := by
    have hlt : C⊂Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,fun he => hi (by simp [he])⟩
    simpa using Finset.card_lt_card hlt
  have hD : D.Nonempty := ⟨j,cut_block_included R i j⟩
  have hp := hs (closedSubrep B R attach C D hclosed)
    (closed_subrep_nonzero B R attach C D hclosed hdim hD)
    (closed_subrep_proper B R attach C D hclosed hC)
  rw [closed_subrep_weight B R attach C D hclosed hdim] at hp
  have he := cut_demand_equals_flow hT f hoff x (fun j => sourceDimension (B j)) hrow hcol hij
  exact he ▸ hp

end KroneckerGluedCutStability
end

/- Original module: KroneckerGluingKingWeight -/
section
set_option autoImplicit false
namespace KroneckerGluingKingWeight
open SimpleGraph KroneckerLinearCoverBlocks KroneckerGluedSubrepresentations
open KroneckerPositiveGluedStability KroneckerBipartiteIncidence KroneckerSaturatedTreeDimensions
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def totalSource {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) : ℕ := (∑ j,sourceDimension (B j))+Fintype.card I

noncomputable def totalSink {J : Type} [Fintype J]
    (B : J → LinearCoverBlock) : ℕ := ∑ j,Fintype.card (B j).Sink

noncomputable def slopeParameter {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) : ℝ := (totalSource (I:=I) B : ℝ)/((Fintype.card I : ℝ)+1)

def KingStable {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink) : Prop :=
  ∀ S : GluedSubrep B R attach,0<gluedSourceSize S+gluedSinkSize S →
    gluedSourceSize S+gluedSinkSize S<totalSource (I:=I) B+totalSink B →
    totalSink B*gluedSourceSize S<totalSource (I:=I) B*gluedSinkSize S

theorem glued_total_dimension {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (hdim : ∀ j,Fintype.card (B j).Sink=sourceDimension (B j)+1) :
    totalSink B=totalSource (I:=I) B+(Fintype.card I+1) := by
  have hc := saturated_tree_sink_count R hT h3
  simp only [totalSink,totalSource,hdim,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one]
  omega

theorem slope_parameter_balance {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) :
    (∑ j,(sourceDimension (B j) : ℝ))+(Fintype.card I : ℝ)=
      slopeParameter (I:=I) B*((Fintype.card I : ℝ)+1) := by
  have hk : (Fintype.card I : ℝ)+1≠0 := by positivity
  simp [slopeParameter,totalSource,Nat.cast_sum,div_mul_cancel₀ _ hk]

theorem king_weight_identity {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hdim : totalSink B=totalSource (I:=I) B+(Fintype.card I+1)) (S : GluedSubrep B R attach) :
    ((Fintype.card I : ℝ)+1)*gluedWeight (slopeParameter (I:=I) B) S=
      (totalSource (I:=I) B : ℝ)*gluedSinkSize S-(totalSink B : ℝ)*gluedSourceSize S := by
  have hk : (Fintype.card I : ℝ)+1≠0 := by positivity
  have hx : slopeParameter (I:=I) B*((Fintype.card I : ℝ)+1)=totalSource (I:=I) B := by
    exact div_mul_cancel₀ _ hk
  have hb : (totalSink B : ℝ)=(totalSource (I:=I) B : ℝ)+((Fintype.card I : ℝ)+1) := by
    exact_mod_cast hdim
  dsimp [gluedWeight]
  rw [hb]
  nlinarith

theorem king_stable_iff_normalized {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hdim : totalSink B=totalSource (I:=I) B+(Fintype.card I+1)) :
    KingStable B R attach ↔ NormalizedStable B R attach (slopeParameter (I:=I) B) := by
  have hk : 0<(Fintype.card I : ℝ)+1 := by positivity
  constructor
  · intro h S hn hp
    have hnat := h S hn hp
    have hr : (totalSink B : ℝ)*gluedSourceSize S<
        (totalSource (I:=I) B : ℝ)*gluedSinkSize S := by exact_mod_cast hnat
    have he := king_weight_identity B R attach hdim S
    nlinarith
  · intro h S hn hp
    have hw := h S hn hp
    have he := king_weight_identity B R attach hdim S
    have hr : (totalSink B : ℝ)*gluedSourceSize S<
        (totalSource (I:=I) B : ℝ)*gluedSinkSize S := by nlinarith
    exact_mod_cast hr

end KroneckerGluingKingWeight
end
