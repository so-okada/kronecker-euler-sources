import KroneckerTotalLatticeWeight

/- Original module: KroneckerLatticeScaleNormalization -/
section
set_option autoImplicit false
namespace KroneckerLatticeScaleNormalization
open KroneckerParameterWeightLower

noncomputable def gamma (x : ℝ) : ℝ := 1-256/x

theorem lattice_scale_cancellation (x : ℝ) (hx : 0<x) :
    (x/256-1)^2*((256 : ℝ)^2*x^(-2 : ℝ))=gamma x^2 := by
  rw [show (-2 : ℝ)=-(2 : ℝ) by norm_num,Real.rpow_neg hx.le,Real.rpow_two]
  unfold gamma
  field_simp

theorem endpoint_scale_cancellation (x : ℝ) (hx : 0<x) :
    (x/256-1)^2*x^(-9/2 : ℝ)=gamma x^2*x^(-5/2 : ℝ)/(256 : ℝ)^2 := by
  have hq : x/256-1=gamma x*x/256 := by unfold gamma; field_simp
  have hp : x^2*x^(-9/2 : ℝ)=x^(-5/2 : ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hx]
    norm_num
  rw [hq]
  calc
    (gamma x*x/256)^2*x^(-9/2 : ℝ)=gamma x^2*(x^2*x^(-9/2 : ℝ))/(256 : ℝ)^2 := by ring
    _=_ := by rw [hp]

/-- All2(n+1) interval lengths cancel the transition scale, leaving x^(-5/2). -/
theorem lattice_geometry_normalization (n : ℕ) (x : ℝ) (hx : 0<x) :
    (x/256-1)^(2*(n+1))*geometryFactor n x=
      gamma x^(2*(n+1))*x^(-5/2 : ℝ)/(256 : ℝ)^2 := by
  unfold geometryFactor
  calc
    (x/256-1)^(2*(n+1))*(x^(-9/2 : ℝ)*((256 : ℝ)^2*x^(-2 : ℝ))^n)=
        ((x/256-1)^2*x^(-9/2 : ℝ))*
          (((x/256-1)^2*((256 : ℝ)^2*x^(-2 : ℝ)))^n) := by
      simp only [pow_mul,pow_succ,mul_pow]
      ring
    _=(gamma x^2*x^(-5/2 : ℝ)/(256 : ℝ)^2)*(gamma x^2)^n := by
      rw [lattice_scale_cancellation x hx,endpoint_scale_cancellation x hx]
    _=_ := by rw [pow_mul,pow_succ]; ring

end KroneckerLatticeScaleNormalization
end

/- Original module: KroneckerMarkedLatticeWeightSum -/
section
set_option autoImplicit false
namespace KroneckerMarkedLatticeWeightSum
open KroneckerMarkedLatticeInputs KroneckerLatticeDimensionEmbedding KroneckerChainLatticeParameters
open KroneckerFiniteChainInputs KroneckerChainSlotProductLower KroneckerChainUniformSlotBounds
open KroneckerChainLocalSlotClasses KroneckerChainPortColors
attribute [local instance] Classical.propDecidable

theorem parameter_dimension_sum {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) (p : LatticeParameter n x) :
    (∑ j,dimensions (parameterDimensions hx ha p) j)=a-(n+1) := by
  have h := (parameterDimensions hx ha p).property.2
  change (∑ j,dimensions (parameterDimensions hx ha p) j)+(n+1)=a at h
  omega

theorem marked_card_as_family_sum {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) :
    (Fintype.card (MarkedLatticeInput hx ha) : ℝ)=∑ p : LatticeParameter n x,
      ∑ σ : ColorChoices n,(Fintype.card (FamilyClass (dimensions (parameterDimensions hx ha p)) σ) : ℝ) := by
  rw [marked_lattice_card]
  simp only [Nat.cast_sum,family_class_card,Nat.cast_prod]

/-- Summing all actual class bounds preserves the full6^(n+1) color factor. -/
theorem marked_weight_sum_lower {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) (H : SlotBounds A B) :
    (6 : ℝ)^(n+1)*(A^(n+3)*B^n*(256/27 : ℝ)^(a-(n+1)))*
      (∑ p : LatticeParameter n x,dimensionWeight (dimensions (parameterDimensions hx ha p)))≤
      (Fintype.card (MarkedLatticeInput hx ha) : ℝ) := by
  rw [marked_card_as_family_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  have hb (σ : ColorChoices n) := family_class_product_lower A B hA hB H
    (dimensions (parameterDimensions hx ha p)) σ (parameterDimensions hx ha p).property.1
  simp only [parameter_dimension_sum hx ha p] at hb
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun σ _ => hb σ)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    independent_color_count,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using hs

end KroneckerMarkedLatticeWeightSum
end

/- Original module: KroneckerQuantitativeSupportCount -/
section
set_option autoImplicit false
namespace KroneckerQuantitativeSupportCount
open KroneckerTotalLatticeWeight KroneckerMarkedLatticeWeightSum KroneckerMarkedLatticeInputs
open KroneckerParameterWeightLower KroneckerChainUniformSlotBounds KroneckerLatticeFamilyCounting
open KroneckerFiniteChainInputs KroneckerFiniteChainCounting KroneckerChainClassFibers
attribute [local instance] Classical.propDecidable

noncomputable def markedLower (n a : ℕ) (x A B : ℝ) : ℝ :=
  (6 : ℝ)^(n+1)*(A^(n+3)*B^n*(256/27 : ℝ)^(a-(n+1)))*
    ((x/256-1)^(2*(n+1))*geometryFactor n x*(1/100 : ℝ)^n)

theorem marked_lattice_quantitative_lower {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) (A B : ℝ) (hA : 0≤A) (hB : 0≤B) (H : SlotBounds A B) :
    markedLower n a x A B≤(Fintype.card (MarkedLatticeInput hx ha) : ℝ) := by
  exact (mul_le_mul_of_nonneg_left (total_lattice_weight_lower hx ha) (by positivity)).trans
    (marked_weight_sum_lower hx ha A B hA hB H)

/-- The fully enumerated stable dimensioned-support family satisfies the
quantitative lower count before scalar normalization to the manuscript formula. -/
theorem stable_support_quantitative_lower {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) (A B : ℝ) (hA : 0≤A) (hB : 0≤B) (H : SlotBounds A B) :
    markedLower n a x A B/8≤((enumeratedInputs hx ha).image forgetInput).card := by
  have hmark := marked_lattice_quantitative_lower hx ha A B hA hB H
  have hcard : (enumeratedInputs hx ha).card=Fintype.card (MarkedLatticeInput hx ha) := by
    rw [enumerated_inputs_card,marked_lattice_card]
  have hlabel : (0 : ℝ)<labelingBound n ∧ (labelingBound n : ℝ)≤8 := by
    unfold labelingBound
    split_ifs <;> norm_num
  calc
    markedLower n a x A B/8≤(Fintype.card (MarkedLatticeInput hx ha) : ℝ)/8 :=
      div_le_div_of_nonneg_right hmark (by norm_num)
    _≤(Fintype.card (MarkedLatticeInput hx ha) : ℝ)/(labelingBound n : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hlabel.1 hlabel.2
    _≤_ := by rw [←hcard]; exact chain_subset_real_lower _

end KroneckerQuantitativeSupportCount
end

/- Original module: KroneckerManuscriptSupportBound -/
section
set_option autoImplicit false
namespace KroneckerManuscriptSupportBound
open KroneckerQuantitativeSupportCount KroneckerLatticeScaleNormalization
open KroneckerChainUniformSlotBounds KroneckerLatticeFamilyCounting KroneckerFiniteChainInputs
attribute [local instance] Classical.propDecidable

noncomputable def manuscriptLower (n a : ℕ) (x A B : ℝ) : ℝ :=
  (256/27 : ℝ)^a*x^(-5/2 : ℝ)*(A^2/(8*B*(1/100 : ℝ)*(256 : ℝ)^2))*
    ((6*A*B*(1/100 : ℝ)*gamma x^2)/(256/27 : ℝ))^(n+1)

theorem marked_lower_normalization (n a : ℕ) (x A B : ℝ) (hx : 0<x)
    (ha : n+1≤a) (hB : 0<B) :
    markedLower n a x A B/8=manuscriptLower n a x A B := by
  have hb : (256/27 : ℝ)^a=(256/27 : ℝ)^(a-(n+1))*(256/27 : ℝ)^(n+1) := by
    rw [←pow_add,Nat.sub_add_cancel ha]
  unfold markedLower manuscriptLower
  rw [lattice_geometry_normalization n x hx,hb]
  simp only [mul_pow,div_pow,pow_mul,pow_succ]
  field_simp

/-- The manuscript numerical lower bound is now proved for the actual finite
set of stable dimensioned colored supports. Cover and Euler interpretation is separate. -/
theorem enumerated_manuscript_lower {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) (A B : ℝ) (hA : 0<A) (hB : 0<B) (H : SlotBounds A B) :
    manuscriptLower n a x A B≤((enumeratedInputs hx ha).image forgetInput).card := by
  have hn : n+1≤a := by
    have hnR : (n : ℝ)+1≤(a : ℝ) := by rw [←ha]; nlinarith [show (0 : ℝ)≤(n : ℝ) by positivity]
    exact_mod_cast hnR
  rw [←marked_lower_normalization n a x A B (by linarith) hn hB]
  exact stable_support_quantitative_lower hx ha A B hA.le hB.le H

/-- The constants are supplied by the proved slot-class enumeration bounds,
so the numerical estimate does not postulate a new external counting interface. -/
theorem uniform_manuscript_support_bound : ∃ A B : ℝ,0<A ∧ 0<B ∧
    ∀ (n a : ℕ) (x : ℝ) (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a),
      manuscriptLower n a x A B≤((enumeratedInputs hx ha).image forgetInput).card := by
  obtain ⟨A,B,hA,hB,H⟩ := uniform_slot_constants
  exact ⟨A,B,hA,hB,fun _ _ _ hx ha => enumerated_manuscript_lower hx ha A B hA hB H⟩

end KroneckerManuscriptSupportBound
end
