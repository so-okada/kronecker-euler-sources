import KroneckerEmbeddedSubrepresentationEquivalence
import KroneckerFiniteQuiverPullbackStability

/-! All-subrepresentation King stability and the original vertex dimension
statistics are preserved by the exact embedded-component equivalence. This
proves a representation-level bridge, not only a combinatorial support match. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedStabilityEquivalence
open KroneckerAbelianCover KroneckerFiniteQuiverHom KroneckerTypedQuiverMaps
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportInducedQuiver
open KroneckerDirectSumEmbeddingLocalLifts KroneckerEmbeddedSupportQuiverIso
open KroneckerEmbeddedRepresentationEquivalence KroneckerFiniteSupportStability
open KroneckerFiniteQuiverPullbackStability
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

local instance supportQuiverFintype (Q : TypedQuiver) (d : Q.V →₀ ℕ) : Fintype (supportQuiver Q d).V :=
  supportFintype d



theorem stable_iff (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d) (θ : Q.V → ℤ)
    (R : Representation Q.source Q.target (fun v => d v)) :
    FiniteSupportStable (descend f.vertex hv d) (θ ∘ f.vertex)
      (KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd R) ↔
      FiniteSupportStable d θ R := by
  rw [finiteSupportStable_iff_restrict P,finiteSupportStable_iff_restrict Q,restricted_representation]
  exact finite_pull_stable_iff (supportIso f hv ha hf d hd) (supportFinsupp d)
    (supportCharacter d θ) (restrictToSupport Q d R)

end KroneckerEmbeddedStabilityEquivalence
