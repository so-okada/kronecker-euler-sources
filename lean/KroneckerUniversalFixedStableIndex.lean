import KroneckerUniversalStableDimensionIndex
import KroneckerUniversalDimensionClassStatistics

/- Original module: KroneckerBoundedStableExistenceDictionary -/
section
/-! Exact two-way existence dictionary at the common depth3B+1: nonzero
stable objects with a prescribed original dimension, a bounded total and a
prescribed self-Euler form exist on the direct-sum cover iff they exist on
the universal colored-word cover. This does not identify geometric moduli. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBoundedStableExistenceDictionary
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportStability KroneckerFiniteSupportEulerTransport
attribute [local instance] Classical.decEq Classical.propDecidable




end KroneckerBoundedStableExistenceDictionary
end
end

/- Original module: KroneckerFixedDimensionStableRealizationDictionary -/
section
/-! At fixed original dimension D the bound is intrinsic: every lift has
total equal to total(D). Hence the explicit depth3*total(D)+1 gives a two-way
stable existence dictionary preserving any specified self-Euler integer, with
no extra size assumption on either representation family. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFixedDimensionStableRealizationDictionary
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportStability KroneckerFiniteSupportEulerTransport
open KroneckerBoundedStableExistenceDictionary
attribute [local instance] Classical.decEq Classical.propDecidable

theorem total_of_original_dimension {V : Type} (d : V →₀ ℕ) (f : V → Fin 2)
    (D : Fin 2 →₀ ℕ) (h : d.mapDomain f = D) : d.sum (fun _ k => k) = D.sum (fun _ k => k) := by
  rw [← h]
  symm
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)


end KroneckerFixedDimensionStableRealizationDictionary
end
end

/- Original module: KroneckerUniversalFixedStableIndex -/
section
/-! The universal stable index at a prescribed original dimension vector
is exactly the corresponding fiber of its total-bounded index. Nonvanishing,
all-subrepresentation stability and the original multiplicities remain
explicit in the witness definition, including the zero-D edge case. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalFixedStableIndex
open KroneckerDeckDimensionClasses KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportStability KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerUniversalStableDimensionIndex KroneckerUniversalDimensionClassStatistics
attribute [local instance] Classical.decEq Classical.propDecidable

def FixedStableIndex (D : Fin 2 →₀ ℕ) (θ : Fin 2 → ℤ) : Set DimensionClass :=
  {q | ∃ S : SupportedRepresentation coloredCoverQuiver,
    S.1 ≠ 0 ∧ S.1.mapDomain KroneckerUniversalWordBaseProjection.baseVertex = D ∧
    FiniteSupportStable S.1 (θ ∘ KroneckerUniversalWordBaseProjection.baseVertex) S.2 ∧
    Quotient.mk dimensionSetoid S.1 = q}

theorem fixed_mem_iff (D : Fin 2 →₀ ℕ) (θ : Fin 2 → ℤ) (q : DimensionClass) :
    q ∈ FixedStableIndex D θ ↔ q ∈ StableIndex (D.sum (fun _ k => k)) θ ∧ classBase q = D := by
  constructor
  · rintro ⟨S,hn,hD,hs,rfl⟩
    have ht := KroneckerFixedDimensionStableRealizationDictionary.total_of_original_dimension S.1 _ D hD
    exact ⟨⟨S,hn,ht.le,hs,rfl⟩,hD⟩
  · rintro ⟨⟨S,hn,_,hs,hq⟩,hD⟩
    rw [← hq] at hD
    exact ⟨S,hn,hD,hs,hq⟩

def fixedFiberEquiv (D : Fin 2 →₀ ℕ) (θ : Fin 2 → ℤ) : FixedStableIndex D θ ≃
    {q : StableIndex (D.sum (fun _ k => k)) θ // classBase q.val = D} where
  toFun q := ⟨⟨q.val,((fixed_mem_iff D θ q.val).mp q.property).1⟩,
    ((fixed_mem_iff D θ q.val).mp q.property).2⟩
  invFun q := ⟨q.val.val,(fixed_mem_iff D θ q.val.val).mpr ⟨q.val.property,q.property⟩⟩
  left_inv q := Subtype.ext rfl
  right_inv q := Subtype.ext (Subtype.ext rfl)

end KroneckerUniversalFixedStableIndex
end
end
