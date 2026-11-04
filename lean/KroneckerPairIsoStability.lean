import KroneckerStableMatrixKernelCover

/-! Stability of the actual pair representation is invariant under its
coordinate-free source and sink isomorphisms, using the canonical dictionary. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairIsoStability
open KroneckerReflectionPairModel KroneckerCanonicalKroneckerModuli
theorem stable_iff {m a b : ℕ} {R S : PairRep m a b} (e : KroneckerAbstractPairIso.Iso R S) :
    PairStable R ↔ PairStable S := by
  rw [← KroneckerReflectionPairStability.stable_iff R,
    ← KroneckerReflectionPairStability.stable_iff S]
  exact (KroneckerPairIsoCanonicalDictionary.toCanonical e).stable_iff (character a b)
end KroneckerPairIsoStability
