import KroneckerUniversalFixedStableIndex
import KroneckerUniversalDirectIndexInvariants

/- Original module: KroneckerAccumulatedBaseStatistics -/
section
/-! Pushforward to original vertices preserves total dimension and every
character-weighted sum. Each lifted multiplicity is bounded by its original
vertex multiplicity; in particular nonzero finite support cannot disappear
under aggregation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedBaseStatistics
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver
open KroneckerAccumulatedDeckBaseDimensions
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

theorem base_total (Q : TypedQuiver) (n : ℕ) (d : (Q.iterate n).V →₀ ℕ) :
    (baseDimension Q n d).sum (fun _ k => k) = d.sum (fun _ k => k) := by
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)


theorem coordinate_le_base (Q : TypedQuiver) (n : ℕ) (d : (Q.iterate n).V →₀ ℕ)
    (v : (Q.iterate n).V) : d v ≤ baseDimension Q n d (baseVertex Q n v) := by
  by_cases hv : v ∈ d.support
  · unfold baseDimension Finsupp.mapDomain
    rw [Finsupp.sum_apply]
    change d v ≤ ∑ x ∈ d.support, (Finsupp.single (baseVertex Q n x) (d x)) (baseVertex Q n v)
    have h := Finset.single_le_sum (fun x _ => Nat.zero_le
      ((Finsupp.single (baseVertex Q n x) (d x)) (baseVertex Q n v))) hv
    simpa only [Finsupp.single_eq_same] using h
  · rw [Finsupp.notMem_support_iff.mp hv]
    exact Nat.zero_le _


theorem support_maps_to_base_support (Q : TypedQuiver) (n : ℕ)
    (d : (Q.iterate n).V →₀ ℕ) {v : (Q.iterate n).V} (hv : v ∈ d.support) :
    baseVertex Q n v ∈ (baseDimension Q n d).support := by
  apply Finsupp.mem_support_iff.mpr
  exact Nat.ne_of_gt ((Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)).trans_le
    (coordinate_le_base Q n d v))

end KroneckerAccumulatedBaseStatistics
end
end

/- Original module: KroneckerFixedBaseAccumulatedStableIndex -/
section
/-! A fixed finitely supported original dimension gives a finite accumulated
stable index even when the ORIGINAL vertex set is infinite. Only the original
arrow alphabet must be finite. The explicit bound uses the support and total
of that original dimension, not the size of the ambient vertex set. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFixedBaseAccumulatedStableIndex
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver
open KroneckerFiniteQuiverHom KroneckerFiniteSupportStability KroneckerFiniteSupportInducedQuiver
open KroneckerAccumulatedDeckBaseDimensions KroneckerAccumulatedBaseStatistics
open KroneckerAccumulatedDimensionClasses KroneckerIteratedRootedDimensionBound
open KroneckerStableAccumulatedBallNormalization KroneckerAccumulatedDeckRootTransitivity
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

def FixedStableIndex (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) : Set (DimensionClass Q n) :=
  {q | ∃ (d : (Q.iterate n).V →₀ ℕ), d ≠ 0 ∧ baseDimension Q n d = D ∧
    (∃ R : Representation (Q.iterate n).source (Q.iterate n).target (fun v => d v),
      FiniteSupportStable d (θ ∘ baseVertex Q n) R) ∧ Quotient.mk (dimensionSetoid Q n) d = q}

abbrev FixedNormalizedIndex (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) :=
  Σ v : SupportVertex D, BallDimension Q n (D.sum (fun _ k => k)) (D.sum (fun _ k => k)) (zeroRoot Q n v.val)

theorem exists_fixed_index (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ)
    (q : FixedStableIndex Q n D θ) : ∃ i : FixedNormalizedIndex Q n D,
      Quotient.mk (dimensionSetoid Q n) i.2.val = q.val := by
  obtain ⟨d,hd,hD,⟨R,hR⟩,hq⟩ := q.property
  have ht : d.sum (fun _ k => k) = D.sum (fun _ k => k) := by rw [← hD,base_total]
  obtain ⟨f,i,hi,hroot⟩ := exists_bounded_normal_form Q n _ d hd (le_of_eq ht) _ R hR
  have hb : baseDimension Q n i.2.val = D := by rw [hi,baseDimension_pull,hD]
  have hm := support_maps_to_base_support Q n i.2.val (Finsupp.mem_support_iff.mpr hroot)
  rw [zeroRoot_base,hb] at hm
  refine ⟨⟨⟨i.1,hm⟩,i.2⟩,?_⟩
  exact (show Quotient.mk (dimensionSetoid Q n) d = Quotient.mk (dimensionSetoid Q n) i.2.val from
    Quotient.sound ⟨f,hi.symm⟩).symm.trans hq

def fixedCode (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ)
    (q : FixedStableIndex Q n D θ) : FixedNormalizedIndex Q n D :=
  Classical.choose (exists_fixed_index Q n D θ q)

theorem fixedCode_injective (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    Function.Injective (fixedCode Q n D θ) := by
  intro q r h
  apply Subtype.ext
  exact (Classical.choose_spec (exists_fixed_index Q n D θ q)).symm.trans
    ((congrArg (fun i : FixedNormalizedIndex Q n D => Quotient.mk (dimensionSetoid Q n) i.2.val) h).trans
      (Classical.choose_spec (exists_fixed_index Q n D θ r)))

theorem fixedStableIndex_finite (Q : TypedQuiver) [Finite Q.A] (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    Finite (FixedStableIndex Q n D θ) := by
  let (v : SupportVertex D) := ballDimension_finite Q n (D.sum (fun _ k => k)) (D.sum (fun _ k => k)) (zeroRoot Q n v.val)
  exact Finite.of_injective (fixedCode Q n D θ) (fixedCode_injective Q n D θ)

theorem fixedStableIndex_card_le (Q : TypedQuiver) [Fintype Q.A] (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    Nat.card (FixedStableIndex Q n D θ) ≤ D.support.card *
      (D.sum (fun _ k => k) + 1)^wordBudget Q (D.sum (fun _ k => k)) := by
  let B := D.sum (fun _ k => k)
  let (v : SupportVertex D) := ballDimension_finite Q n B B (zeroRoot Q n v.val)
  let (v : SupportVertex D) := Fintype.ofFinite (BallDimension Q n B B (zeroRoot Q n v.val))
  have h := Nat.card_le_card_of_injective (fixedCode Q n D θ) (fixedCode_injective Q n D θ)
  have hc : Nat.card (FixedNormalizedIndex Q n D) ≤ D.support.card * (B+1)^wordBudget Q B := by
    rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
    calc
      _ ≤ ∑ v : SupportVertex D, (B+1)^wordBudget Q B := Finset.sum_le_sum (fun v _ => by
        simpa only [Nat.card_eq_fintype_card] using ballDimension_card_le Q n B B (zeroRoot Q n v.val))
      _ = _ := by simp
  exact h.trans hc

end KroneckerFixedBaseAccumulatedStableIndex
end
end

/- Original module: KroneckerDirectSumFixedStableIndex -/
section
/-! For a fixed original finite dimension vector, actual stable direct-sum
representations define a faithful dimension index in the product model. The
map preserves every original multiplicity and does not require finitely many
original vertices. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumFixedStableIndex
open KroneckerAbelianCover KroneckerFiniteQuiverHom KroneckerFiniteSupportStability
open KroneckerDirectSumDimensionClasses KroneckerDirectSumIteratedEmbedding
open KroneckerDirectSumSupportedBridge KroneckerDirectSumSupportedStatistics
open KroneckerQuiverPullbackComposition
attribute [local instance] Classical.decEq Classical.propDecidable

def FixedStableIndex (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) : Set (DimensionClass Q n) :=
  {q | ∃ d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ,
    d ≠ 0 ∧ KroneckerDirectSumBaseDimensions.baseDimension Q n d = D ∧
    (∃ R : Representation (KroneckerDirectSumIteratedGirth.iterate Q n).source
      (KroneckerDirectSumIteratedGirth.iterate Q n).target (fun v => d v),
      FiniteSupportStable d (θ ∘ baseVertex Q n) R) ∧ Quotient.mk (dimensionSetoid Q n) d = q}

theorem push_mem (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ)
    (q : DimensionClass Q n) (hq : q ∈ FixedStableIndex Q n D θ) :
    productClass Q n q ∈ KroneckerFixedBaseAccumulatedStableIndex.FixedStableIndex Q n D θ := by
  obtain ⟨d,hd,hD,⟨R,hR⟩,rfl⟩ := hq
  let S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n) := ⟨d,R⟩
  refine ⟨(push Q n S).1,(not_congr (push_zero_iff Q n S)).mpr hd,?_,
    ⟨(push Q n S).2,(push_stable_iff Q n θ S).mpr hR⟩,?_⟩
  · rwa [push_base]
  · change Quotient.mk _ (push Q n S).1 = Quotient.mk _ (KroneckerDirectSumDimensionNaturality.pushDimension Q n d)
    rw [push_dimension]

def indexMap (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    FixedStableIndex Q n D θ → KroneckerFixedBaseAccumulatedStableIndex.FixedStableIndex Q n D θ :=
  fun q => ⟨productClass Q n q.val,push_mem Q n D θ q.val q.property⟩

theorem indexMap_injective (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    Function.Injective (indexMap Q n D θ) := by
  intro c d h
  exact Subtype.ext (productClass_injective Q n (congrArg Subtype.val h))

end KroneckerDirectSumFixedStableIndex
end
end

/- Original module: KroneckerDirectFixedIndexFiber -/
section
/-! The previously defined direct-sum fixed-original-dimension stable index
is exactly the original-dimension fiber of the bounded-total stable index at
bound total(D). This identifies the existing index, rather than silently
replacing it by a new subset with an unproved size condition. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectFixedIndexFiber
open KroneckerAbelianCover KroneckerDirectSumDimensionClasses
open KroneckerDirectSumFixedStableIndex KroneckerDirectSumStableDimensionIndex
open KroneckerDirectSumBaseDimensions KroneckerDirectSumClassInvariants
attribute [local instance] Classical.decEq Classical.propDecidable

theorem fixed_mem_iff (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) (q : DimensionClass Q n) :
    q ∈ FixedStableIndex Q n D θ ↔ q ∈ StableIndex Q n (D.sum (fun _ k => k)) θ ∧ classBaseDimension Q n q = D := by
  constructor
  · rintro ⟨d,hn,hD,hR,rfl⟩
    have ht : (baseDimension Q n d).sum (fun _ k => k) = d.sum (fun _ k => k) :=
      Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
    exact ⟨⟨d,hn,by rw [← ht,hD],hR,rfl⟩,hD⟩
  · rintro ⟨⟨d,hn,_,hR,hq⟩,hD⟩
    rw [← hq] at hD
    exact ⟨d,hn,hD,hR,hq⟩

def fixedFiberEquiv (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    FixedStableIndex Q n D θ ≃
      {q : StableIndex Q n (D.sum (fun _ k => k)) θ // classBaseDimension Q n q.val = D} where
  toFun q := ⟨⟨q.val,((fixed_mem_iff Q n D θ q.val).mp q.property).1⟩,
    ((fixed_mem_iff Q n D θ q.val).mp q.property).2⟩
  invFun q := ⟨q.val.val,(fixed_mem_iff Q n D θ q.val.val).mpr ⟨q.val.property,q.property⟩⟩
  left_inv q := Subtype.ext rfl
  right_inv q := Subtype.ext (Subtype.ext rfl)

end KroneckerDirectFixedIndexFiber
end
end

/- Original module: KroneckerDirectSumFixedIndexEquivalence -/
section
/-! At a fixed original dimension vector, the direct-sum and product stable
indices are exactly equivalent. Surjectivity descends the normalized actual
representation, preserving every original multiplicity, and faithfulness uses
the recursively finite-character accumulated relation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumFixedIndexEquivalence
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerDirectSumFixedStableIndex KroneckerDirectSumDimensionClasses
open KroneckerExactDirectSumNormalForm KroneckerDirectSumSupportedBridge
open KroneckerStableSupportTypedConnectivity
attribute [local instance] Classical.decEq Classical.propDecidable

theorem indexMap_surjective (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    Function.Surjective (indexMap Q n D θ) := by
  intro q
  obtain ⟨d,hd,hD,⟨R,hR⟩,hq⟩ := q.property
  let S : SupportedRepresentation (Q.iterate n) := ⟨d,R⟩
  obtain ⟨F,T,hT⟩ := exists_exact_normal_form Q n S (stable_connected_dimension _ d hd R _ hR)
  obtain ⟨hn,hbase,ht,hstable⟩ := normal_form_statistics Q n θ S T F hT
  let c : FixedStableIndex Q n D θ := ⟨Quotient.mk (dimensionSetoid Q n) T.1,
    T.1,hn.mpr hd,hbase.trans hD,⟨T.2,hstable.mpr hR⟩,rfl⟩
  refine ⟨c,Subtype.ext ?_⟩
  have hp := congrArg Sigma.fst hT
  dsimp only [pullSupported] at hp
  rw [push_dimension] at hp
  have he : Quotient.mk (KroneckerAccumulatedDimensionClasses.dimensionSetoid Q n) d =
      productClass Q n c.val := Quotient.sound ⟨F,hp.symm⟩
  exact he.symm.trans hq

def indexEquiv (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    FixedStableIndex Q n D θ ≃ KroneckerFixedBaseAccumulatedStableIndex.FixedStableIndex Q n D θ :=
  Equiv.ofBijective (indexMap Q n D θ) ⟨indexMap_injective Q n D θ,indexMap_surjective Q n D θ⟩


end KroneckerDirectSumFixedIndexEquivalence
end
end

/- Original module: KroneckerDirectSumFixedIndexBounds -/
section
/-! Fixed-original-dimension stable indices in the exact direct-sum tower
are finite even for an infinite original vertex set. Their explicit bound
uses only the original arrow count and the support and total of the prescribed
dimension vector, uniformly in the cover depth. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumFixedIndexBounds
open KroneckerAbelianCover KroneckerDirectSumFixedStableIndex
open KroneckerDirectSumFixedIndexEquivalence KroneckerIteratedRootedDimensionBound
attribute [local instance] Classical.decEq Classical.propDecidable

theorem index_card_eq (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    Nat.card (FixedStableIndex Q n D θ) = Nat.card (KroneckerFixedBaseAccumulatedStableIndex.FixedStableIndex Q n D θ) :=
  Nat.card_congr (indexEquiv Q n D θ)

theorem fixedStableIndex_finite (Q : TypedQuiver) [Finite Q.A]
    (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) : Finite (FixedStableIndex Q n D θ) := by
  haveI := KroneckerFixedBaseAccumulatedStableIndex.fixedStableIndex_finite Q n D θ
  exact Finite.of_injective (indexEquiv Q n D θ) (indexEquiv Q n D θ).injective

theorem fixedStableIndex_card_le (Q : TypedQuiver) [Fintype Q.A]
    (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) :
    Nat.card (FixedStableIndex Q n D θ) ≤ D.support.card *
      (D.sum (fun _ k => k) + 1)^wordBudget Q (D.sum (fun _ k => k)) := by
  rw [index_card_eq]
  exact KroneckerFixedBaseAccumulatedStableIndex.fixedStableIndex_card_le Q n D θ

end KroneckerDirectSumFixedIndexBounds
end
end

/- Original module: KroneckerDirectSumStableIndexEquivalence -/
section
/-! Every product stable dimension class of bounded total size has an actual
stable direct-sum representative. Together with the faithful accumulated
relation this is an exact bijection of stable indices, preserving the chosen
total bound and original King character. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumStableIndexEquivalence
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerDirectSumStableDimensionIndex KroneckerDirectSumDimensionClasses
open KroneckerExactDirectSumNormalForm KroneckerDirectSumSupportedBridge
open KroneckerStableSupportTypedConnectivity
attribute [local instance] Classical.decEq Classical.propDecidable

theorem indexMap_surjective (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) :
    Function.Surjective (indexMap Q n B θ) := by
  intro q
  obtain ⟨d,hd,hB,⟨R,hR⟩,hq⟩ := q.property
  let S : SupportedRepresentation (Q.iterate n) := ⟨d,R⟩
  obtain ⟨F,T,hT⟩ := exists_exact_normal_form Q n S (stable_connected_dimension _ d hd R _ hR)
  obtain ⟨hn,hbase,ht,hstable⟩ := normal_form_statistics Q n θ S T F hT
  let c : StableIndex Q n B θ := ⟨Quotient.mk (dimensionSetoid Q n) T.1,
    T.1,hn.mpr hd,by rw [ht]; exact hB,⟨T.2,hstable.mpr hR⟩,rfl⟩
  refine ⟨c,Subtype.ext ?_⟩
  have hp := congrArg Sigma.fst hT
  dsimp only [pullSupported] at hp
  rw [push_dimension] at hp
  have he : Quotient.mk (KroneckerAccumulatedDimensionClasses.dimensionSetoid Q n) d =
      productClass Q n c.val := Quotient.sound ⟨F,hp.symm⟩
  exact he.symm.trans hq

def indexEquiv (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) :
    StableIndex Q n B θ ≃ KroneckerFiniteAccumulatedStableIndex.StableIndex Q n B θ :=
  Equiv.ofBijective (indexMap Q n B θ) ⟨indexMap_injective Q n B θ,indexMap_surjective Q n B θ⟩


end KroneckerDirectSumStableIndexEquivalence
end
end

/- Original module: KroneckerDirectSumStableIndexBounds -/
section
/-! The exact direct-sum stable index is finite with the SAME explicit bound
uniform in the depth of the successive abelian covers. The cardinal equality
is proved through the actual stable-representation index bijection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumStableIndexBounds
open KroneckerAbelianCover KroneckerDirectSumStableDimensionIndex
open KroneckerDirectSumStableIndexEquivalence KroneckerIteratedRootedDimensionBound
attribute [local instance] Classical.decEq Classical.propDecidable

theorem index_card_eq (Q : TypedQuiver) (n B : ℕ) (θ : Q.V → ℤ) :
    Nat.card (StableIndex Q n B θ) = Nat.card (KroneckerFiniteAccumulatedStableIndex.StableIndex Q n B θ) :=
  Nat.card_congr (indexEquiv Q n B θ)

theorem stableIndex_finite (Q : TypedQuiver) [Finite Q.V] [Finite Q.A]
    (n B : ℕ) (θ : Q.V → ℤ) : Finite (StableIndex Q n B θ) := by
  haveI := KroneckerFiniteAccumulatedStableIndex.stableIndex_finite Q n B θ
  exact Finite.of_injective (indexEquiv Q n B θ) (indexEquiv Q n B θ).injective

theorem stableIndex_card_le (Q : TypedQuiver) [Fintype Q.V] [Fintype Q.A]
    (n B : ℕ) (θ : Q.V → ℤ) :
    Nat.card (StableIndex Q n B θ) ≤ Fintype.card Q.V * (B+1)^wordBudget Q B := by
  rw [index_card_eq]
  exact KroneckerFiniteAccumulatedStableIndex.stableIndex_card_le Q n B θ

end KroneckerDirectSumStableIndexBounds
end
end

/- Original module: KroneckerUniversalDirectFixedIndexEquivalence -/
section
/-! The existing fixed-original-dimension direct-sum stable index is
bijective with the universal fixed-dimension index at depth3*total(D)+1.
This is a restriction of the checked quotient bijection to the exact original
dimension fiber, with its underlying class map and self-Euler formula proved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalDirectFixedIndexEquivalence
open KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerUniversalDirectStableIndexEquivalence KroneckerUniversalDirectIndexInvariants
attribute [local instance] Classical.decEq Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def fixedIndexEquiv (D : Fin 2 →₀ ℕ) (θ : Fin 2 → ℤ) :
    KroneckerDirectSumFixedStableIndex.FixedStableIndex baseQuiver (depth (D.sum (fun _ k => k))) D θ ≃
      KroneckerUniversalFixedStableIndex.FixedStableIndex D θ :=
  (KroneckerDirectFixedIndexFiber.fixedFiberEquiv baseQuiver _ D θ).trans
    (((stableIndexEquiv (D.sum (fun _ k => k)) θ).subtypeEquiv
      (fun q => by rw [index_base])).trans (KroneckerUniversalFixedStableIndex.fixedFiberEquiv D θ).symm)



end KroneckerUniversalDirectFixedIndexEquivalence
end
end

/- Original module: KroneckerUniversalStableIndexBounds -/
section
/-! The exact universal stable dimension index inherits explicit finite
cardinality bounds from the genuine direct-sum index bijection, both for
bounded total and fixed original dimension. These count DIMENSION indices;
no general finiteness of stable representation moduli is inferred. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalStableIndexBounds
open KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerUniversalDirectStableIndexEquivalence KroneckerUniversalDirectFixedIndexEquivalence
open KroneckerUniversalStableDimensionIndex KroneckerIteratedRootedDimensionBound
attribute [local instance] Classical.decEq Classical.propDecidable

theorem stableIndex_finite (B : ℕ) (θ : Fin 2 → ℤ) : Finite (StableIndex B θ) := by
  haveI := KroneckerDirectSumStableIndexBounds.stableIndex_finite baseQuiver (depth B) B θ
  exact Finite.of_injective (stableIndexEquiv B θ).symm (stableIndexEquiv B θ).symm.injective

theorem stableIndex_card_le (B : ℕ) (θ : Fin 2 → ℤ) :
    Nat.card (StableIndex B θ) ≤ 2*(B+1)^wordBudget baseQuiver B := by
  rw [← Nat.card_congr (stableIndexEquiv B θ)]
  simpa only [vertex_card] using KroneckerDirectSumStableIndexBounds.stableIndex_card_le baseQuiver (depth B) B θ

theorem fixedIndex_finite (D : Fin 2 →₀ ℕ) (θ : Fin 2 → ℤ) :
    Finite (KroneckerUniversalFixedStableIndex.FixedStableIndex D θ) := by
  haveI := KroneckerDirectSumFixedIndexBounds.fixedStableIndex_finite baseQuiver (depth (D.sum (fun _ k => k))) D θ
  exact Finite.of_injective (fixedIndexEquiv D θ).symm (fixedIndexEquiv D θ).symm.injective


end KroneckerUniversalStableIndexBounds
end
end
