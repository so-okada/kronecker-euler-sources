import KroneckerChainSlotProductLower
import KroneckerMarkedLatticeInputs
import KroneckerExactSlotCounts

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace KroneckerManuscriptSlotBounds
open KroneckerChainUniformSlotBounds KroneckerChainBlockProducts KroneckerChainIncidence
open KroneckerChainBlockNeighbors KroneckerChainPortColors KroneckerChainLocalSlotClasses
open KroneckerReflectedSingleSlotCounts KroneckerReflectedPairSlotCounts
open KroneckerChainSlotProductLower KroneckerFiniteChainInputs
open KroneckerFiniteStableChainFamily KroneckerLatticeDimensionEmbedding
open KroneckerChainLatticeParameters KroneckerChainBinFamily

def SlotBounds256 (A B : ℝ) : Prop :=
  (∀ j : ℕ, 256 ≤ j → ∀ c : Fin 3, A*(256/27 : ℝ)^j*(j : ℝ)^(-3/2 : ℝ) ≤
    (Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) c) : ℝ)) ∧
  (∀ j : ℕ, 256 ≤ j → ∀ c e : Fin 3, B*(256/27 : ℝ)^j*(j : ℝ)^(-1/2 : ℝ) ≤
    (Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) c e) : ℝ))

theorem from_uniform (A B : ℝ) (H : SlotBounds A B) : SlotBounds256 A B :=
  ⟨fun j hj => H.1 j (by omega), fun j hj => H.2 j (by omega)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
theorem local_lower {n : ℕ} (A B : ℝ) (H : SlotBounds256 A B)
    (d : Block n → ℕ) (σ : ColorChoices n) (hd : ∀ j, 256 ≤ d j) (j : Block n) :
    slotLower A B d j ≤ (Fintype.card (LocalClass d σ j) : ℝ) := by
  rcases block_cases j with rfl|rfl|⟨t,rfl⟩|⟨t,rfl⟩
  · rw [leaf_local_class_card d σ _ 0 left_incidence]
    exact H.1 _ (hd _) _
  · rw [leaf_local_class_card d σ _ (Fin.last n) right_incidence]
    simp only [slotLower,blockProfile,rightBlock,show Fin.last (n+1)=(Fin.last n).succ by rfl,
      Fin.cases_succ,Fin.lastCases_last]
    convert H.1 (d (rightBlock n)) (hd (rightBlock n))
      (prescribed σ (Fin.last n) (rightBlock n) ((right_incidence (Fin.last n)).mpr rfl)) using 1
    congr 1
    apply congrArg (fun k : ℕ => (k : ℝ))
    exact Fintype.card_congr (Equiv.refl _)
  · rw [leaf_local_class_card d σ _ t (fun i => middle_incidence i t)]
    exact H.1 _ (hd _) _
  · rw [internal_local_class_card]
    simpa only [slotLower,blockProfile,internalBlock,Fin.cases_succ,Fin.lastCases_castSucc]
      using H.2 _ (hd (internalBlock t)) _ _

theorem family_lower {n : ℕ} (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (H : SlotBounds256 A B) (d : Block n → ℕ) (σ : ColorChoices n) (hd : ∀ j, 256 ≤ d j) :
    A^(n+3)*B^n*(256/27 : ℝ)^(∑ j,d j)*dimensionWeight d ≤
      (Fintype.card (FamilyClass d σ) : ℝ) := by
  rw [←slot_product_factorization,family_class_card,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun j _ => slot_lower_nonnegative A B d hA hB j)
    (fun j _ => local_lower A B H d σ hd j)

theorem compatible_dimensions_ge {n a : ℕ} (d : DimensionData n a) (h : BinCompatible d) :
    ∀ j, 256 ≤ dimensions d j := by
  obtain ⟨x,l,r,i,k,hx,ha,hb,hd⟩ := h
  intro j
  have hbound := (KroneckerChainBinFamily.bin_block_size_bounds n x l r i k hx hb j).1
  rw [←hd j] at hbound
  have : (256 : ℝ) ≤ dimensions d j := hbound.le
  exact_mod_cast this


theorem from_one_color (A B : ℝ) (d : Fin 3)
    (hA : ∀ j : ℕ, 256 ≤ j → A*(256/27 : ℝ)^j*(j : ℝ)^(-3/2 : ℝ) ≤
      (Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d) : ℝ))
    (hB : ∀ j : ℕ, 256 ≤ j → B*(256/27 : ℝ)^j*(j : ℝ)^(-1/2 : ℝ) ≤
      (Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d d) : ℝ)) :
    SlotBounds256 A B := by
  constructor
  · intro j hj c
    have hc := (reflected_single_slot_closed_count j c).trans
      (reflected_single_slot_closed_count j d).symm
    have he : Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) c) =
        Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d) := by
      exact_mod_cast hc
    rw [he]
    exact hA j hj
  · intro j hj c e
    have he : Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) c c) =
        Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d d) := by
      obtain ⟨k,hk⟩ : ∃ k : ℕ, j=k+1 := ⟨j-1,by omega⟩
      subst j
      exact (reflected_same_slot_count k c).trans (reflected_same_slot_count k d).symm
    have hb : B*(256/27 : ℝ)^j*(j : ℝ)^(-1/2 : ℝ) ≤
        (Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) c c) : ℝ) := by
      rw [he]
      exact hB j hj
    by_cases hce : c=e
    · subst e
      exact hb
    · exact hb.trans (by exact_mod_cast reflected_slot_pair_comparison j hce)

end KroneckerManuscriptSlotBounds

