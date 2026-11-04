import KroneckerFiniteStableChainFamily
import KroneckerManuscriptSlotBounds

/-! Fiber bounds, color choices and marked representation counts.
The manuscript parameters are c = n+1 and k = n+2. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace KroneckerSplitMarkedChainLemmas
open KroneckerFiniteChainInputs KroneckerDimensionedSupportClasses
open KroneckerChainClassFibers KroneckerFiniteChainFibers
open KroneckerChainIncidence KroneckerChainPortColors KroneckerChainLocalSlotClasses
open KroneckerChainSlotProductLower
open KroneckerChainBlockProducts KroneckerManuscriptSlotBounds

theorem fiber_bounds (n a : ℕ) (q : Quotient dimensionedSetoid) :
    Fintype.card {X : ChainInput n a // forgetInput X=q} ≤ 8 ∧
    (n=0 → Fintype.card {X : ChainInput n a // forgetInput X=q} ≤ 6) := by
  have h := complete_input_all_fibers n a q
  constructor
  · exact h.trans (by unfold labelingBound; split <;> omega)
  · intro hn
    simpa [labelingBound,hn] using h

theorem color_count (n : ℕ) : Fintype.card (ColorChoices n)=6^(n+1) :=
  independent_color_count n

theorem representation_count {n : ℕ} (d : Block n → ℕ) (σ : ColorChoices n) :
    Fintype.card (FamilyClass d σ)=∏ j,Fintype.card (LocalClass d σ j) :=
  family_class_card d σ

theorem representation_lower {n : ℕ} (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (H : SlotBounds256 A B) (d : Block n → ℕ) (σ : ColorChoices n) (hd : ∀ j, 256 ≤ d j) :
    A^(n+3)*B^n*(256/27 : ℝ)^(∑ j,d j)*dimensionWeight d ≤
      (Fintype.card (FamilyClass d σ) : ℝ) :=
  family_lower A B hA hB H d σ hd

end KroneckerSplitMarkedChainLemmas

#print axioms KroneckerSplitMarkedChainLemmas.fiber_bounds
#print axioms KroneckerSplitMarkedChainLemmas.color_count
#print axioms KroneckerSplitMarkedChainLemmas.representation_count
#print axioms KroneckerSplitMarkedChainLemmas.representation_lower
