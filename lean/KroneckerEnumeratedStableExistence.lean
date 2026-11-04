import KroneckerLatticeFamilyCounting
import KroneckerLatticeFiberCount

set_option autoImplicit false
namespace KroneckerEnumeratedStableExistence
open KroneckerFiniteStateBins KroneckerLatticeFiberCount KroneckerChainLatticeParameters
open KroneckerMarkedLatticeInputs KroneckerLatticeDimensionEmbedding KroneckerFiniteChainInputs
open KroneckerFiniteStableChainFamily KroneckerChainClassExistence KroneckerChainPortColors

/-- A concrete admissible state word and transition-bin word, for every chain length. -/
def canonicalBins (n : ℕ) : StateBins n :=
  ⟨fun _ => 0,fun _ => ⟨0,by norm_num [stateValue]⟩⟩




end KroneckerEnumeratedStableExistence
