import KroneckerDirectSumStableDimensionIndex
import KroneckerStableShapeQuotientEquivalence
import KroneckerUniversalStableDimensionIndex

/- Original module: KroneckerDirectStableRepresentativeIndex -/
section
/-! Quotienting witnessed stable representatives by direct-sum dimension
deck equivalence gives EXACTLY the previously defined bounded stable index.
The projection is proved injective and surjective, so retaining a witness
representation adds no unintended distinction to the dimension index. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectStableRepresentativeIndex
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerStableColoredRepresentatives KroneckerDirectSumStableDimensionIndex
open KroneckerDirectSumDimensionClasses KroneckerQuiverPullbackComposition
attribute [local instance] Classical.decEq Classical.propDecidable

def representativeIndex (B : ℕ) (θ : Fin 2 → ℤ) (S : DirectStable B θ) : StableIndex baseQuiver (depth B) B θ :=
  ⟨Quotient.mk (dimensionSetoid baseQuiver (depth B)) S.val.1,
    S.val.1,S.property.1,S.property.2.1,⟨S.val.2,S.property.2.2⟩,rfl⟩

def quotientIndex (B : ℕ) (θ : Fin 2 → ℤ) : Quotient (directSetoid B θ) → StableIndex baseQuiver (depth B) B θ :=
  Quotient.lift (representativeIndex B θ) (fun _ _ h => Subtype.ext (Quotient.sound h))

theorem quotientIndex_injective (B : ℕ) (θ : Fin 2 → ℤ) : Function.Injective (quotientIndex B θ) := by
  intro x y
  induction x using Quotient.inductionOn with | h S =>
    induction y using Quotient.inductionOn with | h T =>
      intro h
      have he : Quotient.mk (dimensionSetoid baseQuiver (depth B)) S.val.1 =
          Quotient.mk (dimensionSetoid baseQuiver (depth B)) T.val.1 := congrArg Subtype.val h
      have hr : Related baseQuiver (depth B) S.val.1 T.val.1 := Quotient.exact he
      exact Quotient.sound hr

theorem quotientIndex_surjective (B : ℕ) (θ : Fin 2 → ℤ) : Function.Surjective (quotientIndex B θ) := by
  rintro ⟨q,d,hn,hB,⟨R,hR⟩,hq⟩
  exact ⟨Quotient.mk (directSetoid B θ) ⟨⟨d,R⟩,hn,hB,hR⟩,Subtype.ext hq⟩

def indexEquiv (B : ℕ) (θ : Fin 2 → ℤ) : Quotient (directSetoid B θ) ≃ StableIndex baseQuiver (depth B) B θ :=
  Equiv.ofBijective (quotientIndex B θ) ⟨quotientIndex_injective B θ,quotientIndex_surjective B θ⟩

end KroneckerDirectStableRepresentativeIndex
end
end

/- Original module: KroneckerUniversalDirectStableIndexEquivalence -/
section
/-! The established genuine direct-sum stable index at depth3B+1 is
bijective with the universal-word stable dimension index. The map agrees
with EVERY weighted-colored actual realization, making its independence
from roots, normalizations and chosen stable witnesses explicit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalDirectStableIndexEquivalence
open KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerStableColoredRepresentatives KroneckerStableShapeQuotientEquivalence
attribute [local instance] Classical.decEq Classical.propDecidable

def stableIndexEquiv (B : ℕ) (θ : Fin 2 → ℤ) :
    KroneckerDirectSumStableDimensionIndex.StableIndex baseQuiver (depth B) B θ ≃
      KroneckerUniversalStableDimensionIndex.StableIndex B θ :=
  (KroneckerDirectStableRepresentativeIndex.indexEquiv B θ).symm.trans
    ((stableDimensionQuotientEquiv B θ).trans (KroneckerUniversalStableDimensionIndex.indexEquiv B θ))

theorem equiv_on_realization (B : ℕ) (θ : Fin 2 → ℤ) {S : DirectStable B θ} {T : WordStable B θ}
    (h : ShapeRelated B θ S T) :
    stableIndexEquiv B θ (KroneckerDirectStableRepresentativeIndex.representativeIndex B θ S) =
      KroneckerUniversalStableDimensionIndex.representativeIndex B θ T := by
  change (KroneckerUniversalStableDimensionIndex.indexEquiv B θ)
    (stableDimensionQuotientEquiv B θ ((KroneckerDirectStableRepresentativeIndex.indexEquiv B θ).symm
      ((KroneckerDirectStableRepresentativeIndex.indexEquiv B θ) (Quotient.mk _ S)))) = _
  rw [Equiv.symm_apply_apply,equiv_on_any_realization B θ h]
  rfl


end KroneckerUniversalDirectStableIndexEquivalence
end
end
