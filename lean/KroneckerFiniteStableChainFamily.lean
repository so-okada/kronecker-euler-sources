import KroneckerFiniteChainInputs
import Mathlib.Combinatorics.Pigeonhole

/- Original module: KroneckerChainClassExistence -/
section
set_option autoImplicit false
namespace KroneckerChainClassExistence
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainPortColors
open KroneckerChainLocalSlotClasses KroneckerChainRepresentativeIndependence
open KroneckerChainRepresentativeStability KroneckerChainBinFamily KroneckerChainBlockSizes
open KroneckerReflectedSingleSlotCounts KroneckerReflectedPairSlotCounts
open KroneckerLinearCoverBlocks KroneckerGluedSubrepEquivalence KroneckerRetainedBlockSupport
attribute [local instance] Classical.propDecidable




end KroneckerChainClassExistence
end

/- Original module: KroneckerFiniteChainFibers -/
section
set_option autoImplicit false
namespace KroneckerFiniteChainFibers
open Module KroneckerChainIncidence KroneckerFiniteChainInputs KroneckerChainRepresentativeIndependence
open KroneckerChainParameterLabelRecovery KroneckerChainLabelCollision KroneckerChainSkeletonPermutations
open KroneckerChainClassFibers KroneckerColoredIncidenceIso KroneckerDimensionedSupportClasses
attribute [local instance] Classical.propDecidable

theorem input_label_collision {n a : ℕ} (X Z Y : ChainInput n a)
    (e : ColoredIso (gluedRepresentative (representatives X.2.2)).coloring
      (gluedRepresentative (representatives Y.2.2)).coloring)
    (f : ColoredIso (gluedRepresentative (representatives Z.2.2)).coloring
      (gluedRepresentative (representatives Y.2.2)).coloring)
    (he : ∀ s,finrank ℂ ((gluedRepresentative (representatives Y.2.2)).block.Space (e.source s))=
      finrank ℂ ((gluedRepresentative (representatives X.2.2)).block.Space s))
    (hf : ∀ s,finrank ℂ ((gluedRepresentative (representatives Y.2.2)).block.Space (f.source s))=
      finrank ℂ ((gluedRepresentative (representatives Z.2.2)).block.Space s))
    (h : recoveredSkeletonPerm (representatives X.2.2) (representatives Y.2.2)
        X.1.2.1 Y.1.2.1 e he=
      recoveredSkeletonPerm (representatives Z.2.2) (representatives Y.2.2) Z.1.2.1 Y.1.2.1 f hf) : X=Z := by
  rcases X with ⟨d,σ,U⟩
  rcases Z with ⟨d',τ,V⟩
  have hp := equal_labels_recover_parameters (representatives U) (representatives V)
    (representatives Y.2.2) d.2.1 d'.2.1 Y.1.2.1 e f he hf h
  have hd := dimensions_injective n a hp.1
  subst d'
  have hc : σ=τ := hp.2
  subst τ
  have hm := equal_labels_recover_classes (representatives U) (representatives V)
    (representatives Y.2.2) d.2.1 Y.1.2.1 e f he hf h
  have huv : U=V := by simpa only [representatives_correct] using hm
  subst V
  rfl

/-- Dimensions and connector colors vary throughout this fiber. A chosen
isomorphism supplies a skeleton code, and equality of codes recovers every
input parameter and every marked block class. -/
theorem complete_input_fiber_le {n a : ℕ} (Y : ChainInput n a) :
    Fintype.card {X : ChainInput n a // forgetInput X=forgetInput Y}≤Fintype.card (SkeletonPerm n) := by
  classical
  let A := {X : ChainInput n a // forgetInput X=forgetInput Y}
  have hw : ∀ X : A,∃ e : ColoredIso (gluedRepresentative (representatives X.1.2.2)).coloring
      (gluedRepresentative (representatives Y.2.2)).coloring,
      ∀ s,finrank ℂ ((gluedRepresentative (representatives Y.2.2)).block.Space (e.source s))=
        finrank ℂ ((gluedRepresentative (representatives X.1.2.2)).block.Space s) :=
    fun X => Quotient.exact X.2
  choose e he using hw
  let code : A → SkeletonPerm n := fun X =>
    recoveredSkeletonPerm (representatives X.1.2.2) (representatives Y.2.2)
      X.1.1.2.1 Y.1.2.1 (e X) (he X)
  apply Fintype.card_le_of_injective code
  intro X Z h
  apply Subtype.ext
  exact input_label_collision X.1 Z.1 Y (e X) (e Z) (he X) (he Z) h

theorem complete_input_all_fibers (n a : ℕ) (q : Quotient dimensionedSetoid) :
    Fintype.card {X : ChainInput n a // forgetInput X=q}≤labelingBound n := by
  classical
  by_cases h : ∃ Y : ChainInput n a,forgetInput Y=q
  · obtain ⟨Y,rfl⟩ := h
    exact (complete_input_fiber_le Y).trans (skeleton_count_bound n)
  · haveI : IsEmpty {X : ChainInput n a // forgetInput X=q} := ⟨fun X => h ⟨X.1,X.2⟩⟩
    simp

end KroneckerFiniteChainFibers
end

/- Original module: KroneckerFiniteChainCounting -/
section
set_option autoImplicit false
namespace KroneckerFiniteChainCounting
open KroneckerFiniteChainInputs KroneckerFiniteChainFibers KroneckerChainClassFibers
open KroneckerChainIncidence KroneckerChainPortColors KroneckerChainLocalSlotClasses
attribute [local instance] Classical.propDecidable

/-- Any chosen finite subfamily loses at most the proved 8/6 factor when
its actual dimensioned colored supports forget all construction labels. -/
theorem chain_subset_count {n a : ℕ} (S : Finset (ChainInput n a)) :
    S.card≤(S.image forgetInput).card*labelingBound n := by
  classical
  by_contra h
  obtain ⟨q,hq,hbig⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun X hX => Finset.mem_image_of_mem forgetInput hX) (Nat.lt_of_not_ge h)
  have hb := complete_input_all_fibers n a q
  rw [Fintype.card_subtype] at hb
  have hs : (S.filter (fun X => forgetInput X=q)).card≤
      (Finset.univ.filter (fun X => forgetInput X=q)).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
  omega

theorem chain_subset_real_lower {n a : ℕ} (S : Finset (ChainInput n a)) :
    (S.card : ℝ)/(labelingBound n : ℝ)≤(S.image forgetInput).card := by
  have hp : (0 : ℝ)<labelingBound n := by unfold labelingBound; split_ifs <;> norm_num
  apply (div_le_iff₀ hp).mpr
  exact_mod_cast chain_subset_count S


end KroneckerFiniteChainCounting
end

/- Original module: KroneckerFiniteStableChainFamily -/
section
set_option autoImplicit false
namespace KroneckerFiniteStableChainFamily
open KroneckerFiniteChainInputs KroneckerFiniteChainCounting KroneckerChainClassFibers
open KroneckerChainIncidence KroneckerChainBlockSizes KroneckerChainBinFamily
open KroneckerChainIntegerDimensions KroneckerChainFlowIntegrality KroneckerChainPortColors
open KroneckerChainRepresentativeIndependence KroneckerChainRepresentativeStability
open KroneckerChainSlotAssignments KroneckerGluedSubrepEquivalence KroneckerRetainedBlockSupport
open KroneckerCoverTitsForm KroneckerLinearCoverBlocks
attribute [local instance] Classical.propDecidable

def BinCompatible {n a : ℕ} (d : DimensionData n a) : Prop :=
  ∃ (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ),100000≤x ∧ ((n : ℝ)+2)*x=a ∧
    BinData n x l r i h ∧ ∀ j,(dimensions d j : ℝ)=blockSize n x l r j

noncomputable def stableInputs (n a : ℕ) : Finset (ChainInput n a) :=
  Finset.univ.filter (fun X => BinCompatible X.1)

/-- Every integer-lattice flow satisfying the manuscript bins enters the
finite dimension family; the dimension code is constructed, not assumed. -/
theorem lattice_flow_enters_family (n a : ℕ) (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ)
    (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) (D : BinData n x l r i h)
    (hl : ∀ t≤n,OnLattice (((t : ℝ)+1)*x) (l t))
    (hr : ∀ t≤n,OnLattice (-((t : ℝ)+1)*x) (r t)) :
    ∃ d : DimensionData n a,(∀ j,(dimensions d j : ℝ)=blockSize n x l r j) ∧ BinCompatible d := by
  have hb := bin_block_size_bounds n x l r i h hx D
  obtain ⟨d,hd,_⟩ := natural_dimensions_unique n x l r
    (all_block_sizes_integral n a x l r ha hl hr) (fun j => le_of_lt (lt_trans (by norm_num) (hb j).1))
  have hp : ∀ j,0<d j := by
    intro j
    have ht : (0 : ℝ)<d j := by rw [hd j]; linarith [(hb j).1]
    exact_mod_cast ht
  let code := encodeDimensions d hp (natural_dimension_balance n a x l r d hd ha)
  refine ⟨code,hd,x,l,r,i,h,hx,ha,D,hd⟩

/-- Each retained input yields the actual stable tree representation, Tits
form one, and the required total dimensions (a,a+n+2). -/
theorem stable_input_realization {n a : ℕ} (X : ChainInput n a) (hX : X∈stableInputs n a) :
    BlockKingStable (gluedRepresentative (representatives X.2.2)).block ∧
    (supportGraph (gluedRepresentative (representatives X.2.2)).block).IsTree ∧
    titsForm (gluedRepresentative (representatives X.2.2)).block=1 ∧
    sourceDimension (gluedRepresentative (representatives X.2.2)).block=a ∧
    Fintype.card (gluedRepresentative (representatives X.2.2)).block.Sink=a+(n+2) := by
  obtain ⟨x,l,r,i,h,hx,ha,D,hd⟩ := (Finset.mem_filter.mp hX).2
  have ht := representative_stable_tree (representatives X.2.2) X.1.2.1 x l r i h hx D hd
  have hs := representative_total_dimensions (representatives X.2.2) X.1.2.1 a x l r hd ha
  exact ⟨ht.1,ht.2.1,ht.2.2,hs.1,hs.2⟩


end KroneckerFiniteStableChainFamily
end
