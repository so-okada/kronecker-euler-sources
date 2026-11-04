import KroneckerUniversalDimensionClassStatistics
import KroneckerUniversalDirectStableIndexEquivalence

/- Original module: KroneckerStableShapeInvariantFormulas -/
section
/-! Every weighted colored cross-model stable realization preserves the
complete original dimension vector, total and actual self-Euler integer.
These formulas hold for ANY related representatives and therefore provide
the choice-independent numerical input to the stable quotient bijection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableShapeInvariantFormulas
open KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerStableColoredRepresentatives KroneckerStableShapeQuotientEquivalence
open KroneckerColoredSupportStatistics KroneckerFiniteSupportEulerTransport
open KroneckerFiniteSupportDeckRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable


theorem shape_original_dimension (B : ℕ) (θ : Fin 2 → ℤ) {S : DirectStable B θ} {T : WordStable B θ}
    (h : ShapeRelated B θ S T) :
    S.val.1.mapDomain (KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B)) =
      T.val.1.mapDomain KroneckerUniversalWordBaseProjection.baseVertex :=
  mapDomain_eq (Classical.choice h) _ _ (fun v => Fin.ext ((Classical.choice h).side v))


end KroneckerStableShapeInvariantFormulas
end
end

/- Original module: KroneckerUniversalDirectIndexInvariants -/
section
/-! The genuine cross-model stable INDEX bijection preserves original
source/sink dimensions, total and self-Euler as functions on quotient classes.
The proof works with arbitrary representatives and uses the realization-
independent value theorem, not a preferred normalization's numerical values. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalDirectIndexInvariants
open KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerStableColoredRepresentatives KroneckerStableShapeQuotientEquivalence
open KroneckerUniversalDirectStableIndexEquivalence KroneckerStableShapeInvariantFormulas
open KroneckerDirectStableRepresentativeIndex KroneckerTwoSidedQuotientBridge
attribute [local instance] Classical.decEq Classical.propDecidable

theorem index_base (B : ℕ) (θ : Fin 2 → ℤ)
    (q : KroneckerDirectSumStableDimensionIndex.StableIndex baseQuiver (depth B) B θ) :
    KroneckerUniversalDimensionClassStatistics.classBase (stableIndexEquiv B θ q).val =
      KroneckerDirectSumClassInvariants.classBaseDimension baseQuiver (depth B) q.val := by
  rcases q with ⟨q,d,hn,hB,⟨R,hs⟩,rfl⟩
  let S : DirectStable B θ := ⟨⟨d,R⟩,hn,hB,hs⟩
  let T := forwardChoice (stableBridge B θ) S
  have h : ShapeRelated B θ S T := forward_related (stableBridge B θ) S
  change KroneckerUniversalDimensionClassStatistics.classBase (stableIndexEquiv B θ (representativeIndex B θ S)).val = _
  rw [equiv_on_realization B θ h]
  exact (shape_original_dimension B θ h).symm



end KroneckerUniversalDirectIndexInvariants
end
end
