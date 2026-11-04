import KroneckerChainLocalSlotClasses

/- Original module: KroneckerChainBlockProducts -/
section
set_option autoImplicit false
namespace KroneckerChainBlockProducts
open KroneckerChainIncidence KroneckerChainBlockNeighbors

/-- Separate the two end leaves, all middle leaves and all internal blocks. -/
theorem chain_block_product {M : Type*} [CommMonoid M] (n : ℕ) (f : Block n → M) :
    (∏ j,f j)=f (leftBlock n)*f (rightBlock n)*
      (∏ t : Connector n,f (middleBlock t))*(∏ t : Fin n,f (internalBlock t)) := by
  rw [Fintype.prod_sum_type,Fin.prod_univ_succ]
  rw [Fin.prod_univ_castSucc (fun t : Fin (n+1) => f (Sum.inl t.succ))]
  change (f (leftBlock n)*((∏ t : Fin n,f (internalBlock t))*f (rightBlock n)))*
    (∏ t : Connector n,f (middleBlock t))=_
  ac_rfl

theorem chain_block_sum (n : ℕ) (d : Block n → ℕ) :
    (∑ j,d j)=d (leftBlock n)+d (rightBlock n)+
      (∑ t : Connector n,d (middleBlock t))+(∑ t : Fin n,d (internalBlock t)) := by
  rw [Fintype.sum_sum_type,Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc (fun t : Fin (n+1) => d (Sum.inl t.succ))]
  change (d (leftBlock n)+((∑ t : Fin n,d (internalBlock t))+d (rightBlock n)))+
    (∑ t : Connector n,d (middleBlock t))=_
  omega

end KroneckerChainBlockProducts
end

/- Original module: KroneckerChainUniformSlotBounds -/
section
set_option autoImplicit false
namespace KroneckerChainUniformSlotBounds
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainLocalSlotClasses
open KroneckerChainPortColors KroneckerReflectedSingleSlotCounts KroneckerReflectedPairSlotCounts

attribute [local instance] Classical.propDecidable

noncomputable def blockProfile {n : ℕ} (leaf internal : ℝ) : Block n → ℝ
  | Sum.inl j => Fin.cases leaf (Fin.lastCases leaf (fun _ => internal)) j
  | Sum.inr _ => leaf

noncomputable def slotLower {n : ℕ} (A B : ℝ) (d : Block n → ℕ) (j : Block n) : ℝ :=
  blockProfile A B j*(256/27 : ℝ)^(d j)*(d j : ℝ)^blockProfile (-3/2) (-1/2) j

def SlotBounds (A B : ℝ) : Prop :=
  (∀ j : ℕ,0<j → ∀ c : Fin 3,A*(256/27 : ℝ)^j*(j : ℝ)^(-3/2 : ℝ)≤
    (Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) c) : ℝ)) ∧
  (∀ j : ℕ,0<j → ∀ c e : Fin 3,B*(256/27 : ℝ)^j*(j : ℝ)^(-1/2 : ℝ)≤
    (Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) c e) : ℝ))

theorem uniform_slot_constants : ∃ A B : ℝ,0<A ∧ 0<B ∧ SlotBounds A B := by
  obtain ⟨A,hA,hP⟩ := reflected_single_slot_uniform_lower
  obtain ⟨B,hB,hQ⟩ := reflected_pair_slot_uniform_lower
  exact ⟨A,B,hA,hB,hP,hQ⟩

theorem slot_lower_nonnegative {n : ℕ} (A B : ℝ) (d : Block n → ℕ) (hA : 0≤A) (hB : 0≤B)
    (j : Block n) : 0≤slotLower A B d j := by
  have hc : 0≤blockProfile A B j := by
    rcases block_cases j with rfl|rfl|⟨t,rfl⟩|⟨t,rfl⟩ <;>
      simpa only [blockProfile,leftBlock,rightBlock,middleBlock,internalBlock,
        show Fin.last (n+1)=(Fin.last n).succ by rfl,
        Fin.cases_zero,Fin.cases_succ,Fin.lastCases_last,Fin.lastCases_castSucc] using
        (by first | exact hA | exact hB)
  exact mul_nonneg (mul_nonneg hc (by positivity)) (Real.rpow_nonneg (by positivity) _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
/-- The uniform reflected-slot bounds apply to the actual local class at every chain block. -/
theorem actual_local_slot_lower {n : ℕ} (A B : ℝ) (H : SlotBounds A B)
    (d : Block n → ℕ) (σ : ColorChoices n) (hd : ∀ j,0<d j) (j : Block n) :
    slotLower A B d j≤(Fintype.card (LocalClass d σ j) : ℝ) := by
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

end KroneckerChainUniformSlotBounds
end

/- Original module: KroneckerChainSlotProductLower -/
section
set_option autoImplicit false
namespace KroneckerChainSlotProductLower
open KroneckerChainUniformSlotBounds KroneckerChainBlockProducts KroneckerChainIncidence
open KroneckerChainBlockNeighbors KroneckerChainPortColors KroneckerChainLocalSlotClasses

attribute [local instance] Classical.propDecidable

noncomputable def dimensionWeight {n : ℕ} (d : Block n → ℕ) : ℝ :=
  ∏ j : Block n,(d j : ℝ)^blockProfile (-3/2) (-1/2) j

theorem block_coefficient_product (n : ℕ) (A B : ℝ) :
    (∏ j : Block n,blockProfile A B j)=A^(n+3)*B^n := by
  rw [chain_block_product]
  simp only [blockProfile,leftBlock,rightBlock,middleBlock,internalBlock,
    show Fin.last (n+1)=(Fin.last n).succ by rfl,
    Fin.cases_zero,Fin.cases_succ,Fin.lastCases_last,Fin.lastCases_castSucc,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simp only [pow_succ]
  ring

theorem slot_product_factorization {n : ℕ} (A B : ℝ) (d : Block n → ℕ) :
    (∏ j : Block n,slotLower A B d j)=
      A^(n+3)*B^n*(256/27 : ℝ)^(∑ j,d j)*dimensionWeight d := by
  simp only [slotLower,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
    block_coefficient_product,dimensionWeight]

/-- The complete marked-class product has the manuscript exponential factor
and the exact blockwise inverse-power weight, uniformly in connector colors. -/
theorem family_class_product_lower {n : ℕ} (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (H : SlotBounds A B) (d : Block n → ℕ) (σ : ColorChoices n) (hd : ∀ j,0<d j) :
    A^(n+3)*B^n*(256/27 : ℝ)^(∑ j,d j)*dimensionWeight d≤
      (Fintype.card (FamilyClass d σ) : ℝ) := by
  rw [←slot_product_factorization,family_class_card,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun j _ => slot_lower_nonnegative A B d hA hB j)
    (fun j _ => actual_local_slot_lower A B H d σ hd j)

end KroneckerChainSlotProductLower
end
