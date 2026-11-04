import KroneckerMarkedLatticeInputs

set_option autoImplicit false
namespace KroneckerLatticeFamilyCounting
open KroneckerMarkedLatticeInputs KroneckerLatticeDimensionEmbedding KroneckerChainLatticeParameters
open KroneckerFiniteChainInputs KroneckerFiniteStableChainFamily KroneckerFiniteChainCounting
open KroneckerChainClassFibers KroneckerChainLocalSlotClasses KroneckerChainIncidence KroneckerChainPortColors
attribute [local instance] Classical.propDecidable

noncomputable def enumeratedInputs {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) :
    Finset (ChainInput n a) := Finset.univ.image (toChainInput (hx:=hx) (ha:=ha))

theorem enumerated_inputs_card {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) :
    (enumeratedInputs hx ha).card=∑ p : LatticeParameter n x,∑ σ : ColorChoices n,
      ∏ j : Block n,Fintype.card (LocalClass (dimensions (parameterDimensions hx ha p)) σ j) := by
  rw [enumeratedInputs,Finset.card_image_of_injective _ (marked_input_injective hx ha),Finset.card_univ]
  exact marked_lattice_card hx ha

theorem enumerated_inputs_subset {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) :
    enumeratedInputs hx ha⊆stableInputs n a := by
  intro X hX
  obtain ⟨Y,_,rfl⟩ := Finset.mem_image.mp hX
  exact marked_input_stable Y



end KroneckerLatticeFamilyCounting
