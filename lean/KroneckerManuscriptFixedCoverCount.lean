import KroneckerManuscriptCountedIndex
import KroneckerManuscriptSlotBounds

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace KroneckerManuscriptFixedCoverCount
open KroneckerManuscriptSlotBounds
open KroneckerChainLatticeParameters KroneckerLatticeDimensionEmbedding
open KroneckerMarkedLatticeInputs KroneckerFiniteChainInputs KroneckerFiniteStableChainFamily
open KroneckerChainLocalSlotClasses KroneckerChainPortColors KroneckerChainUniformSlotBounds
open KroneckerEnumeratedStableExistence KroneckerManuscriptSupportBound
open KroneckerMarkedLatticeWeightSum KroneckerQuantitativeSupportCount
open KroneckerParameterWeightLower KroneckerChainSlotProductLower KroneckerTotalLatticeWeight
open KroneckerFiniteChainCounting KroneckerChainClassFibers
open KroneckerStableChainCoverData KroneckerEnumeratedCoverClasses KroneckerDeckDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

variable {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x) (ha : ((n : ℝ)+2)*x=a)

abbrev Marked := Σ L : LatticeFor x (canonicalBins n),
  Σ σ : ColorChoices n,FamilyClass
    (dimensions (parameterDimensions hx ha ⟨canonicalBins n,L⟩)) σ

def includeMarked (X : Marked hx ha) : MarkedLatticeInput hx ha :=
  ⟨⟨canonicalBins n,X.1⟩,X.2⟩

theorem includeMarked_injective : Function.Injective (includeMarked hx ha) := by
  rintro ⟨L,s⟩ ⟨M,t⟩ he
  have hLM : L=M := by
    have h := congrArg (fun z : MarkedLatticeInput hx ha => z.1) he
    simpa only [includeMarked,Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  cases hLM
  have hst : s=t := by
    simpa only [includeMarked,Sigma.mk.inj_iff,heq_eq_eq,true_and] using he
  cases hst
  rfl

def input (X : Marked hx ha) : ChainInput n a := toChainInput (includeMarked hx ha X)

theorem input_injective : Function.Injective (input hx ha) :=
  (marked_input_injective hx ha).comp (includeMarked_injective hx ha)

instance : Fintype (Marked hx ha) := Fintype.ofFinite _

def inputs : Finset (ChainInput n a) := Finset.univ.image (input hx ha)

theorem inputs_card : (inputs hx ha).card = Fintype.card (Marked hx ha) := by
  rw [inputs,Finset.card_image_of_injective _ (input_injective hx ha),Finset.card_univ]

theorem inputs_stable : inputs hx ha ⊆ stableInputs n a := by
  intro X hX
  obtain ⟨Y,_,rfl⟩ := Finset.mem_image.mp hX
  exact marked_input_stable (includeMarked hx ha Y)

theorem marked_weight_lower (A B : ℝ) (hA : 0≤A) (hB : 0≤B) (H : SlotBounds256 A B) :
    (6 : ℝ)^(n+1)*(A^(n+3)*B^n*(256/27 : ℝ)^(a-(n+1)))*
      (∑ L : LatticeFor x (canonicalBins n),
        dimensionWeight (dimensions (parameterDimensions hx ha ⟨canonicalBins n,L⟩))) ≤
      (Fintype.card (Marked hx ha) : ℝ) := by
  have hc : Fintype.card (Marked hx ha) = ∑ L : LatticeFor x (canonicalBins n),
      ∑ σ : ColorChoices n, Fintype.card
        (FamilyClass (dimensions (parameterDimensions hx ha ⟨canonicalBins n,L⟩)) σ) := by
    simp only [←Nat.card_eq_fintype_card,Marked,Nat.card_sigma]
  rw [hc]
  simp only [Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro L _
  have hb (σ : ColorChoices n) := family_lower A B hA hB H
    (dimensions (parameterDimensions hx ha ⟨canonicalBins n,L⟩)) σ
    (compatible_dimensions_ge _ (parameter_dimensions_spec hx ha ⟨canonicalBins n,L⟩).2)
  simp only [parameter_dimension_sum hx ha] at hb
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun σ _ => hb σ)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    independent_color_count,Nat.cast_pow,Nat.cast_ofNat,mul_assoc] using hs

theorem marked_quantitative_lower (A B : ℝ) (hA : 0≤A) (hB : 0≤B) (H : SlotBounds256 A B) :
    markedLower n a x A B ≤ (Fintype.card (Marked hx ha) : ℝ) := by
  exact (mul_le_mul_of_nonneg_left (fixed_lattice_weight_lower hx ha) (by positivity)).trans
    (marked_weight_lower hx ha A B hA hB H)

theorem support_lower (A B : ℝ) (hA : 0<A) (hB : 0<B) (H : SlotBounds256 A B) :
    manuscriptLower n a x A B ≤ ((inputs hx ha).image forgetInput).card := by
  have hn : n+1≤a := by
    have h : (n : ℝ)+1≤(a : ℝ) := by rw [←ha]; nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    exact_mod_cast h
  rw [←marked_lower_normalization n a x A B (by linarith) hn hB]
  have hm := marked_quantitative_lower hx ha A B hA.le hB.le H
  have hl : (0 : ℝ)<labelingBound n ∧ (labelingBound n : ℝ)≤8 := by
    unfold labelingBound
    split_ifs <;> norm_num
  calc
    markedLower n a x A B/8 ≤ (Fintype.card (Marked hx ha) : ℝ)/8 :=
      div_le_div_of_nonneg_right hm (by norm_num)
    _ ≤ (Fintype.card (Marked hx ha) : ℝ)/(labelingBound n : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hl.1 hl.2
    _ ≤ _ := by rw [←inputs_card hx ha]; exact chain_subset_real_lower _

def stable (X : {X // X ∈ inputs hx ha}) : StableInput n a :=
  ⟨X.val,inputs_stable hx ha X.property⟩

def coverClasses : Finset DimensionClass :=
  (inputs hx ha).attach.image (fun X => stableCoverClass (stable hx ha X))

theorem cover_card : (coverClasses hx ha).card = ((inputs hx ha).image forgetInput).card := by
  unfold coverClasses
  let g : {X // X ∈ inputs hx ha} →
    Quotient KroneckerDimensionedSupportClasses.dimensionedSetoid := fun X => forgetInput X.val
  trans ((inputs hx ha).attach.image g).card
  · exact equal_kernel_image_card (inputs hx ha).attach
      (fun X => stableCoverClass (stable hx ha X)) g
      (fun X _ Y _ => stable_cover_class_iff (stable hx ha X) (stable hx ha Y))
  congr 1
  ext q
  dsimp only [g]
  simp only [Finset.mem_image,Finset.mem_attach,true_and,Subtype.exists,exists_prop]

theorem cover_lower (A B : ℝ) (hA : 0<A) (hB : 0<B) (H : SlotBounds256 A B) :
    manuscriptLower n a x A B ≤ (coverClasses hx ha).card := by
  rw [cover_card]
  exact support_lower hx ha A B hA hB H

theorem cover_realized (q : DimensionClass) (hq : q ∈ coverClasses hx ha) :
    ∃ X : {X // X ∈ inputs hx ha}, stableCoverClass (stable hx ha X) = q ∧
      (stableDimensions (stable hx ha X)).sum
        (fun w k => if KroneckerWordParity.parity w = 0 then k else 0) = a ∧
      (stableDimensions (stable hx ha X)).sum
        (fun w k => if KroneckerWordParity.parity w = 1 then k else 0) = a+n+2 := by
  obtain ⟨X,_,hX⟩ := Finset.mem_image.mp hq
  exact ⟨X,hX,stable_cover_totals (stable hx ha X)⟩

end KroneckerManuscriptFixedCoverCount

#print axioms KroneckerManuscriptFixedCoverCount.cover_lower
