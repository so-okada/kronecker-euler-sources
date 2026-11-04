import KroneckerAbstractCoordinatesStable

/-! Every subobject of a stable pair is zero, strictly negative, or the entire pair. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairStableSubobjectCases
open Module KroneckerAbstractPairHom KroneckerAbstractPairSubobject KroneckerAbstractPairStability KroneckerFareyWeightIdentity
variable {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
 [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
theorem cases {R : Rep m V W} (hs : Stable R) (U : Subobject R) :
 (U.source=⊥ ∧ U.sink=⊥) ∨
 weight (finrank ℂ V) (finrank ℂ W) (finrank ℂ U.source) (finrank ℂ U.sink)<0 ∨
 (U.source=⊤ ∧ U.sink=⊤) := by
 by_cases hz : finrank ℂ U.source+finrank ℂ U.sink=0
 · exact Or.inl ((KroneckerPairSubobjectZero.criterion U).mp hz)
 by_cases ht : finrank ℂ U.source+finrank ℂ U.sink=finrank ℂ V+finrank ℂ W
 · exact Or.inr (Or.inr ((KroneckerPairSubobjectFull.criterion U).mp ht))
 have hb := KroneckerPairSubobjectDimensionBounds.bounds U
 exact Or.inr (Or.inl (hs U (by omega) (by omega)))
end KroneckerPairStableSubobjectCases
