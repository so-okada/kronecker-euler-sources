import KroneckerFiniteAccumulatedStableIndex

/-! The stable dimension index in the genuine direct-sum iterate is defined
using actual finite-support representations and recursively finite-character
deck equivalence. Pushing representations gives an injective comparison with
the bounded-total stable index in the product model. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumStableDimensionIndex
open KroneckerAbelianCover KroneckerFiniteQuiverHom KroneckerFiniteSupportStability
open KroneckerDirectSumDimensionClasses KroneckerDirectSumIteratedEmbedding
open KroneckerDirectSumSupportedBridge KroneckerDirectSumSupportedStatistics
open KroneckerQuiverPullbackComposition
attribute [local instance] Classical.decEq Classical.propDecidable

def StableIndex (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) : Set (DimensionClass Q n) :=
  {q | ∃ d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ,
    d ≠ 0 ∧ d.sum (fun _ k => k) ≤ B ∧
    (∃ R : Representation (KroneckerDirectSumIteratedGirth.iterate Q n).source
      (KroneckerDirectSumIteratedGirth.iterate Q n).target (fun v => d v),
      FiniteSupportStable d (θ ∘ baseVertex Q n) R) ∧ Quotient.mk (dimensionSetoid Q n) d = q}

theorem push_mem (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ)
    (q : DimensionClass Q n) (hq : q ∈ StableIndex Q n B θ) :
    productClass Q n q ∈ KroneckerFiniteAccumulatedStableIndex.StableIndex Q n B θ := by
  obtain ⟨d,hd,hB,⟨R,hR⟩,rfl⟩ := hq
  let S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n) := ⟨d,R⟩
  refine ⟨(push Q n S).1,(not_congr (push_zero_iff Q n S)).mpr hd,?_,
    ⟨(push Q n S).2,(push_stable_iff Q n θ S).mpr hR⟩,?_⟩
  · rwa [push_sum]
  · change Quotient.mk _ (push Q n S).1 = Quotient.mk _ (KroneckerDirectSumDimensionNaturality.pushDimension Q n d)
    rw [push_dimension]

def indexMap (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) :
    StableIndex Q n B θ → KroneckerFiniteAccumulatedStableIndex.StableIndex Q n B θ :=
  fun q => ⟨productClass Q n q.val,push_mem Q n B θ q.val q.property⟩

theorem indexMap_injective (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) :
    Function.Injective (indexMap Q n B θ) := by
  intro c d h
  exact Subtype.ext (productClass_injective Q n (congrArg Subtype.val h))

end KroneckerDirectSumStableDimensionIndex
