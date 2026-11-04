import KroneckerDirectSumWordEvaluation
import KroneckerFiniteSupportEulerTransport
import KroneckerQuiverSupportEulerTransport
import KroneckerDirectSumBaseDimensions
import KroneckerEmbeddedAcrossIsomorphisms

section

/-! Actual all-subrepresentation King stability descends under accumulated
deck pullback together with the dimension at every original vertex. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDeckStablePullback
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver KroneckerFiniteQuiverHom
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerFiniteSupportStability
open KroneckerQuiverPullbackComposition KroneckerQuiverPullbackStability
open KroneckerAccumulatedCoverDeckActions KroneckerAccumulatedDeckBaseLabels
open KroneckerAccumulatedDeckBaseDimensions
attribute [local instance] Classical.decEq Classical.propDecidable

theorem accumulated_stable_iff (Q : TypedQuiver) (n : ℕ) (f : Deck Q n)
    (d : (Q.iterate n).V →₀ ℕ) (θ : Q.V → ℤ)
    (S : Representation (Q.iterate n).source (Q.iterate n).target (fun v => d v)) :
    FiniteSupportStable (pullDimension f.val d) (θ ∘ baseVertex Q n)
      (pullRepresentation f.val d S) ↔ FiniteSupportStable d (θ ∘ baseVertex Q n) S := by
  have hθ : (fun v => (θ ∘ baseVertex Q n) (f.val.vertexEquiv v)) = θ ∘ baseVertex Q n := by
    funext v
    exact congrArg θ (vertex_base_invariant Q n f.val f.property v)
  simpa only [hθ] using pull_stable_iff f.val d (θ ∘ baseVertex Q n) S

def StableOver (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ)
    (S : SupportedRepresentation (Q.iterate n)) : Prop :=
  baseDimension Q n S.1 = D ∧ FiniteSupportStable S.1 (θ ∘ baseVertex Q n) S.2

theorem stableOver_pull_iff (Q : TypedQuiver) (n : ℕ) (f : Deck Q n)
    (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) (S : SupportedRepresentation (Q.iterate n)) :
    StableOver Q n D θ (pullSupported f.val S) ↔ StableOver Q n D θ S := by
  unfold StableOver pullSupported
  rw [baseDimension_pull,accumulated_stable_iff]

end KroneckerAccumulatedDeckStablePullback
end
end

section

/-! Every nonempty walk-connected finite dimension support has a representative
of its accumulated deck class lying in the precise iterated direct-sum cover.
The full original dimension vector is preserved by this normalization. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDimensionNormalization
open KroneckerAbelianCover LabeledWalk KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerAccumulatedCoverDeckActions
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumRootComponentBridge
open KroneckerEmbeddedFiniteDimensions KroneckerAccumulatedDeckBaseDimensions
open KroneckerAccumulatedDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

def ConnectedDimension (Q : TypedQuiver) (d : Q.V →₀ ℕ) : Prop :=
  ∃ r : SupportVertex d, ∀ v : SupportVertex d, Nonempty (LabeledWalk Q.source Q.target r.val v.val)

theorem exists_normalized_dimension (Q : TypedQuiver) (n : ℕ) (d : (Q.iterate n).V →₀ ℕ)
    (hc : ConnectedDimension (Q.iterate n) d) :
    ∃ f : Deck Q n, InImage (embedding Q n).vertex (pullDimension f.val d) ∧
      baseDimension Q n (pullDimension f.val d) = baseDimension Q n d := by
  obtain ⟨r,hc⟩ := hc
  obtain ⟨f,_,hf⟩ := normalize_connected_family Q n r.val (fun v : SupportVertex d => v.val) hc
  refine ⟨inverse f,?_,baseDimension_pull Q n (inverse f) d⟩
  intro x hx
  change x ∈ (pullDimension (inverse f).val d).support at hx
  have hm : f.val.vertexEquiv.symm x ∈ d.support := by
    rw [Finsupp.mem_support_iff,pullDimension_apply] at hx
    rw [Finsupp.mem_support_iff]
    exact hx
  have hh := hf ⟨f.val.vertexEquiv.symm x,hm⟩
  simpa only [Equiv.apply_symm_apply] using hh

theorem class_has_direct_sum_representative (Q : TypedQuiver) (n : ℕ)
    (d : (Q.iterate n).V →₀ ℕ) (hc : ConnectedDimension (Q.iterate n) d) :
    ∃ δ : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ,
      Related Q n d (δ.mapDomain (embedding Q n).vertex) := by
  obtain ⟨f,hf,_⟩ := exists_normalized_dimension Q n d hc
  refine ⟨descend (embedding Q n).vertex (embedding_injective Q n).1 (pullDimension f.val d),f,?_⟩
  exact (Finsupp.mapDomain_comapDomain _ (embedding_injective Q n).1 _ hf).symm

end KroneckerAccumulatedDimensionNormalization
end
end

section

/- Original module: KroneckerAccumulatedSupportEuler -/
section
/-! Actual self-Euler forms descend to accumulated dimension classes and agree
under the exact direct-sum component bridge. All induced support arrows are
finite because the ORIGINAL arrow alphabet is finite. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedSupportEuler
open KroneckerAbelianCover KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerFiniteSupportEulerTransport
open KroneckerAccumulatedCoverDeckActions KroneckerAccumulatedDimensionClasses
open KroneckerIteratedFiniteSupportArrows KroneckerQuiverSupportEulerTransport
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumEmbeddingLocalLifts
open KroneckerEmbeddedFiniteDimensions KroneckerEmbeddedSupportQuiverIso
attribute [local instance] Classical.decEq Classical.propDecidable

local instance productSupportFinite (Q : TypedQuiver) [Finite Q.A] (n : ℕ) (d : (Q.iterate n).V →₀ ℕ) :
    Finite (SupportArrow (Q.iterate n).source (Q.iterate n).target d) := supportArrow_finite Q n d
local instance directSupportFinite (Q : TypedQuiver) [Finite Q.A] (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    Finite (SupportArrow (KroneckerDirectSumIteratedGirth.iterate Q n).source
      (KroneckerDirectSumIteratedGirth.iterate Q n).target d) := directSupportArrow_finite Q n d

def iteratedEuler (Q : TypedQuiver) [Finite Q.A] (n : ℕ) (d : (Q.iterate n).V →₀ ℕ) : ℤ :=
  supportEuler (Q.iterate n) d

def directEuler (Q : TypedQuiver) [Finite Q.A] (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) : ℤ :=
  supportEuler (KroneckerDirectSumIteratedGirth.iterate Q n) d

theorem iteratedEuler_pull (Q : TypedQuiver) [Finite Q.A] (n : ℕ) (f : Deck Q n)
    (d : (Q.iterate n).V →₀ ℕ) : iteratedEuler Q n (pullDimension f.val d) = iteratedEuler Q n d :=
  supportEuler_iso _ _ (supportQuiverIso f.val d) (fun v => (pullDimension_apply f.val d v.val).symm)

def classEuler (Q : TypedQuiver) [Finite Q.A] (n : ℕ) : DimensionClass Q n → ℤ :=
  Quotient.lift (iteratedEuler Q n) (by
    rintro d e ⟨f,rfl⟩
    exact (iteratedEuler_pull Q n f d).symm)

theorem directEuler_descent (Q : TypedQuiver) [Finite Q.A] (n : ℕ)
    (d : (Q.iterate n).V →₀ ℕ) (hd : InImage (embedding Q n).vertex d) :
    directEuler Q n (descend (embedding Q n).vertex (embedding_injective Q n).1 d) = iteratedEuler Q n d :=
  supportEuler_iso _ _ (supportIso (embedding Q n) (embedding_injective Q n).1
    (embedding_injective Q n).2 (embedding_locallySurjective Q n) d hd) (fun _ => rfl)

theorem directEuler_push (Q : TypedQuiver) [Finite Q.A] (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    directEuler Q n d = iteratedEuler Q n (d.mapDomain (embedding Q n).vertex) := by
  have hd := (dimensionEquiv (embedding Q n).vertex (embedding_injective Q n).1 d).property
  have hh := directEuler_descent Q n (d.mapDomain (embedding Q n).vertex) hd
  rw [show descend (embedding Q n).vertex (embedding_injective Q n).1
      (d.mapDomain (embedding Q n).vertex) = d from
        Finsupp.comapDomain_mapDomain _ (embedding_injective Q n).1 d] at hh
  exact hh

end KroneckerAccumulatedSupportEuler
end
end

/- Original module: KroneckerDirectSumClassInvariants -/
section
/-! The exact dimension-class embedding preserves the actual self-Euler form,
total dimension, and every original-vertex multiplicity. The direct-sum
quotient therefore carries the same numerical invariants as its product image. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumClassInvariants
open KroneckerAbelianCover KroneckerDirectSumAccumulatedActions
open KroneckerDirectSumDimensionNaturality KroneckerDirectSumDimensionClasses
open KroneckerDirectSumBaseDimensions KroneckerAccumulatedSupportEuler
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerDirectSumDeckExtension
open KroneckerFiniteSupportStability KroneckerQuiverPullbackStability
attribute [local instance] Classical.decEq Classical.propDecidable

theorem directEuler_pull (Q : TypedQuiver) [Finite Q.A] (n : ℕ) (f : Deck Q n)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    directEuler Q n (pullDimension f.val d) = directEuler Q n d := by
  rw [directEuler_push,directEuler_push]
  change iteratedEuler Q n (pushDimension Q n (pullDimension f.val d)) =
    iteratedEuler Q n (pushDimension Q n d)
  rw [push_pull Q n f.val (extension f).val (extension_compatible f),iteratedEuler_pull]

def classEuler (Q : TypedQuiver) [Finite Q.A] (n : ℕ) : DimensionClass Q n → ℤ :=
  Quotient.lift (directEuler Q n) (by rintro d e ⟨f,rfl⟩; exact (directEuler_pull Q n f d).symm)

def classBaseDimension (Q : TypedQuiver) (n : ℕ) : DimensionClass Q n → (Q.V →₀ ℕ) :=
  Quotient.lift (baseDimension Q n) (by rintro d e ⟨f,rfl⟩; exact (baseDimension_pull Q n f d).symm)

def classTotal (Q : TypedQuiver) (n : ℕ) : DimensionClass Q n → ℕ :=
  Quotient.lift supportTotalDimension (by rintro d e ⟨f,rfl⟩; exact (pull_total_dimension f.val d).symm)



end KroneckerDirectSumClassInvariants
end
end
end

section

/-! Dimensioned direct-sum representations embed bijectively into product
representations supported on the embedded components. Exact inverse formulas
and reflected gauge isomorphisms retain the actual coordinate arrow maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumSupportedBridge
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumEmbeddingLocalLifts
open KroneckerDirectSumDimensionNaturality KroneckerEmbeddedSupportedRepresentations
open KroneckerEmbeddedFiniteDimensions KroneckerDimensionedCoverIsomorphisms
attribute [local instance] Classical.decEq Classical.propDecidable

def bridge (Q : TypedQuiver) (n : ℕ) : ImageSupported (embedding Q n) ≃
    SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n) :=
  supportedEquiv (embedding Q n) (embedding_injective Q n).1
    (embedding_injective Q n).2 (embedding_locallySurjective Q n)

def push (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    SupportedRepresentation (Q.iterate n) := ((bridge Q n).symm S).val

theorem push_image (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    InImage (embedding Q n).vertex (push Q n S).1 := ((bridge Q n).symm S).property

theorem push_dimension (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    (push Q n S).1 = pushDimension Q n S.1 := supportedEquiv_inverse_dimension _ _ _ _ S

theorem descend_push (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    bridge Q n ⟨push Q n S,push_image Q n S⟩ = S := (bridge Q n).apply_symm_apply S

theorem push_descend (Q : TypedQuiver) (n : ℕ) (S : ImageSupported (embedding Q n)) :
    push Q n (bridge Q n S) = S.val := congrArg Subtype.val ((bridge Q n).symm_apply_apply S)

theorem push_injective (Q : TypedQuiver) (n : ℕ) : Function.Injective (push Q n) := by
  intro S T h
  apply (bridge Q n).symm.injective
  exact Subtype.ext h

theorem push_across_iff (Q : TypedQuiver) (n : ℕ)
    (S T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    Nonempty (AcrossIso (push Q n S) (push Q n T)) ↔ Nonempty (AcrossIso S T) := by
  have h := KroneckerEmbeddedAcrossIsomorphisms.supported_across_iff (embedding Q n)
    (embedding_injective Q n).1 (embedding_injective Q n).2 (embedding_locallySurjective Q n)
    ((bridge Q n).symm S) ((bridge Q n).symm T)
  change Nonempty (AcrossIso (bridge Q n ((bridge Q n).symm S))
    (bridge Q n ((bridge Q n).symm T))) ↔ Nonempty (AcrossIso (push Q n S) (push Q n T)) at h
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at h
  exact h.symm

end KroneckerDirectSumSupportedBridge
end
end

section

/- Original module: KroneckerDirectSumSupportedNaturality -/
section
/-! Component descent commutes exactly with compatible accumulated quiver
pullbacks on dimensioned representations. The proof checks all arrow matrices
with their endpoint transports; no gauge equivalence is substituted for equality. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumSupportedNaturality
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportInducedQuiver
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumEmbeddingLocalLifts
open KroneckerDirectSumDeckCompatibility KroneckerDirectSumDimensionNaturality
open KroneckerDirectSumSupportedBridge KroneckerEmbeddedSupportedRepresentations
attribute [local instance] Classical.decEq Classical.propDecidable

theorem supported_ext {P : TypedQuiver} (S T : SupportedRepresentation P)
    (hd : S.1 = T.1) (ha : ∀ a, S.2.arrow a ≍ T.2.arrow a) : S = T := by
  rcases S with ⟨d,R⟩
  rcases T with ⟨e,T⟩
  dsimp only at hd ha
  cases hd
  have he : R = T := by
    apply representation_ext
    funext a
    exact eq_of_heq (ha a)
  cases he
  rfl

def pullImage (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F)
    (S : ImageSupported (embedding Q n)) : ImageSupported (embedding Q n) :=
  ⟨pullSupported F S.val,image_pull Q n f F h S.val.1 S.property⟩

theorem bridge_pull (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F)
    (S : ImageSupported (embedding Q n)) :
    bridge Q n (pullImage Q n f F h S) = pullSupported f (bridge Q n S) := by
  apply supported_ext
  · exact descend_pull Q n f F h S.val.1
  · intro a
    have hl := KroneckerEmbeddedRestrictionArrowFormula.representation_arrow_heq (embedding Q n)
      (embedding_injective Q n).1 (embedding_injective Q n).2 (embedding_locallySurjective Q n)
      (pullDimension F S.val.1) (image_pull Q n f F h S.val.1 S.property)
      (pullRepresentation F S.val.1 S.val.2) a
    have hr := KroneckerEmbeddedRestrictionArrowFormula.representation_arrow_heq (embedding Q n)
      (embedding_injective Q n).1 (embedding_injective Q n).2 (embedding_locallySurjective Q n)
      S.val.1 S.property S.val.2 (f.arrowEquiv a)
    exact (hl.trans (pull_arrow_heq F S.val.1 S.val.2 ((embedding Q n).arrow a))).trans
      ((dependent_apply_heq S.val.2.arrow (h.2 a)).trans
        ((pull_arrow_heq f (bridge Q n S).1 (bridge Q n S).2 a).trans hr).symm)

theorem push_pull (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (KroneckerDirectSumIteratedGirth.iterate Q n) (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (h : Compatible Q n f F)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    push Q n (pullSupported f S) = pullSupported F (push Q n S) := by
  have hh := bridge_pull Q n f F h ((bridge Q n).symm S)
  rw [Equiv.apply_symm_apply] at hh
  rw [← hh,push_descend]
  rfl

end KroneckerDirectSumSupportedNaturality
end
end

/- Original module: KroneckerDirectSumNonzeroRestriction -/
section
/-! A nonzero image-supported target dimension forces a product accumulated
map to restrict to the genuine direct-sum action. The complementary zero
case has a unique actual coordinate representation, so it introduces no
exception in the subsequent gauge/deck class comparison. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumNonzeroRestriction
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerDirectSumIteratedEmbedding
open KroneckerDirectSumDimensionNaturality KroneckerDirectSumDeckCompatibility
attribute [local instance] Classical.decEq Classical.propDecidable

theorem nonzero_dimension_restriction (Q : TypedQuiver) (n : ℕ)
    (F : KroneckerAccumulatedCoverDeckActions.Deck Q n)
    (d e : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) (he : e ≠ 0)
    (hF : pullDimension F.val (pushDimension Q n d) = pushDimension Q n e) :
    ∃ f : KroneckerDirectSumAccumulatedActions.Deck Q n, Compatible Q n f.val F.val := by
  obtain ⟨v,hv⟩ := Finsupp.support_nonempty_iff.mpr he
  have hpos : pushDimension Q n d (F.val.vertexEquiv ((embedding Q n).vertex v)) ≠ 0 := by
    have h := congrArg (fun δ => δ ((embedding Q n).vertex v)) hF
    rw [pullDimension_apply,pushDimension_apply] at h
    rw [h]
    exact Finsupp.mem_support_iff.mp hv
  obtain ⟨w,hw⟩ := pushDimension_in_image Q n d (Finsupp.mem_support_iff.mpr hpos)
  exact KroneckerDirectSumAccumulatedRestriction.exists_restriction Q n F.val F.property v w hw.symm

theorem zero_supported_unique (P : TypedQuiver) (S T : SupportedRepresentation P)
    (hS : S.1 = 0) (hT : T.1 = 0) : S = T := by
  rcases S with ⟨d,R⟩
  rcases T with ⟨e,T⟩
  dsimp only at hS hT
  subst d
  subst e
  have h : R = T := by
    apply KroneckerFiniteSupportInducedQuiver.representation_ext
    funext a
    apply LinearMap.ext
    intro x
    funext i
    exact Fin.elim0 i
  cases h
  rfl

end KroneckerDirectSumNonzeroRestriction
end
end
end

section

/-! Genuine direct-sum accumulated pullback preserves ALL-subrepresentation
King stability and the full original dimension vector. Generic total-size
and zero-vector pullback formulas make nonzero bounded-size restrictions
explicit, including arbitrary infinite ambient vertex types. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumStablePullback
open KroneckerAbelianCover KroneckerFiniteQuiverHom KroneckerFiniteSupportStability
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerDirectSumAccumulatedActions KroneckerDirectSumDeckRootTorsor
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumBaseDimensions
attribute [local instance] Classical.decEq Classical.propDecidable

theorem pull_zero_iff {P R : TypedQuiver} (f : TypedQuiverIso P R) (d : R.V →₀ ℕ) :
    pullDimension f d = 0 ↔ d = 0 := by
  constructor
  · intro h
    ext v
    have hh := congrArg (fun e => e (f.vertexEquiv.symm v)) h
    simpa only [pullDimension_apply,Equiv.apply_symm_apply,Finsupp.zero_apply] using hh
  · rintro rfl
    ext v
    simp only [pullDimension_apply,Finsupp.zero_apply]

theorem pull_sum {P R : TypedQuiver} (f : TypedQuiverIso P R) (d : R.V →₀ ℕ) :
    (pullDimension f d).sum (fun _ k => k) = d.sum (fun _ k => k) := by
  rw [KroneckerAccumulatedDeckBaseDimensions.pullDimension_eq_mapDomain]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem stable_pull_iff (Q : TypedQuiver) (n : ℕ) (f : Deck Q n)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) (θ : Q.V → ℤ)
    (R : Representation (KroneckerDirectSumIteratedGirth.iterate Q n).source
      (KroneckerDirectSumIteratedGirth.iterate Q n).target (fun v => d v)) :
    FiniteSupportStable (pullDimension f.val d) (θ ∘ baseVertex Q n) (pullRepresentation f.val d R) ↔
      FiniteSupportStable d (θ ∘ baseVertex Q n) R := by
  have hθ : (fun v => (θ ∘ baseVertex Q n) (f.val.vertexEquiv v)) = θ ∘ baseVertex Q n := by
    funext v
    exact congrArg θ (vertex_base_invariant Q n f v)
  simpa only [hθ] using KroneckerQuiverPullbackStability.pull_stable_iff f.val d (θ ∘ baseVertex Q n) R

def StableOver (Q : TypedQuiver) (n : ℕ) (D : Q.V →₀ ℕ) (θ : Q.V → ℤ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) : Prop :=
  baseDimension Q n S.1 = D ∧ FiniteSupportStable S.1 (θ ∘ baseVertex Q n) S.2

theorem stableOver_pull_iff (Q : TypedQuiver) (n : ℕ) (f : Deck Q n)
    (D : Q.V →₀ ℕ) (θ : Q.V → ℤ) (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    StableOver Q n D θ (pullSupported f.val S) ↔ StableOver Q n D θ S := by
  unfold StableOver pullSupported
  rw [baseDimension_pull,stable_pull_iff]

end KroneckerDirectSumStablePullback
end
end

section

/-! The representation bridge preserves original dimensions, total size,
nonvanishing, self-Euler form, and all-subrepresentation King stability. The
base character is pulled from the actual original quiver at every stage. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumSupportedStatistics
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumEmbeddingLocalLifts
open KroneckerDirectSumDimensionNaturality KroneckerDirectSumSupportedBridge
open KroneckerEmbeddedSupportedRepresentations KroneckerFiniteSupportStability
open KroneckerAccumulatedSupportEuler
attribute [local instance] Classical.decEq Classical.propDecidable

theorem push_zero_iff (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    (push Q n S).1 = 0 ↔ S.1 = 0 := by
  rw [push_dimension]
  have hz : pushDimension Q n 0 = 0 := Finsupp.mapDomain_zero
  rw [← hz]
  exact (pushDimension_injective Q n).eq_iff

theorem push_sum (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    (push Q n S).1.sum (fun _ k => k) = S.1.sum (fun _ k => k) := by
  rw [push_dimension]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem push_base (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    KroneckerAccumulatedDeckBaseDimensions.baseDimension Q n (push Q n S).1 =
      KroneckerDirectSumBaseDimensions.baseDimension Q n S.1 := by
  rw [push_dimension,KroneckerDirectSumBaseDimensions.baseDimension_push]

theorem push_euler (Q : TypedQuiver) [Finite Q.A] (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    iteratedEuler Q n (push Q n S).1 = directEuler Q n S.1 := by
  rw [push_dimension]
  exact (directEuler_push Q n S.1).symm

theorem push_stable_iff (Q : TypedQuiver) (n : ℕ) (θ : Q.V → ℤ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    FiniteSupportStable (push Q n S).1 (θ ∘ TypedQuiver.baseVertex Q n) (push Q n S).2 ↔
      FiniteSupportStable S.1 (θ ∘ baseVertex Q n) S.2 := by
  have h := supportedEquiv_stable (embedding Q n) (embedding_injective Q n).1
    (embedding_injective Q n).2 (embedding_locallySurjective Q n) ((bridge Q n).symm S)
    (θ ∘ TypedQuiver.baseVertex Q n)
  change FiniteSupportStable (bridge Q n ((bridge Q n).symm S)).1
    ((θ ∘ TypedQuiver.baseVertex Q n) ∘ (embedding Q n).vertex)
    (bridge Q n ((bridge Q n).symm S)).2 ↔
    FiniteSupportStable (push Q n S).1 (θ ∘ TypedQuiver.baseVertex Q n) (push Q n S).2 at h
  rw [Equiv.apply_symm_apply] at h
  have hb : (θ ∘ TypedQuiver.baseVertex Q n) ∘ (embedding Q n).vertex = θ ∘ baseVertex Q n := by
    funext v
    exact congrArg θ (embedding_base_vertex Q n v)
  rw [hb] at h
  exact h.symm

end KroneckerDirectSumSupportedStatistics
end
end

section

/- Original module: KroneckerAccumulatedRepresentationClasses -/
section
/-! Orbit classes of actual dimensioned representations retain their dimension
class and all-subrepresentation stability over a fixed original dimension.
These are deck orbit classes only; no gauge or GIT identification is asserted. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedRepresentationClasses
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerAccumulatedCoverDeckActions KroneckerAccumulatedDeckStablePullback
open KroneckerAccumulatedDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

def Related (Q : TypedQuiver) (n : ℕ)
    (S T : SupportedRepresentation (Q.iterate n)) : Prop :=
  ∃ f : Deck Q n, pullSupported f.val S = T

def representationSetoid (Q : TypedQuiver) (n : ℕ) : Setoid (SupportedRepresentation (Q.iterate n)) where
  r := Related Q n
  iseqv := ⟨fun S => ⟨identity Q n,pullSupported_refl _ S⟩,by
    rintro S T ⟨f,rfl⟩
    refine ⟨inverse f,?_⟩
    change pullSupported f.val.symm (pullSupported f.val S) = S
    rw [← pullSupported_trans,quiverIso_symm_trans,pullSupported_refl],by
    rintro S T U ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨compose g f,pullSupported_trans g.val f.val S⟩⟩

abbrev RepresentationClass (Q : TypedQuiver) (n : ℕ) := Quotient (representationSetoid Q n)

def dimensionClass (Q : TypedQuiver) (n : ℕ) : RepresentationClass Q n → DimensionClass Q n :=
  Quotient.lift (fun S => Quotient.mk (dimensionSetoid Q n) S.1) (by
    rintro S T ⟨f,rfl⟩
    exact Quotient.sound ⟨f,rfl⟩)



theorem same_class_iff (Q : TypedQuiver) (n : ℕ) (S T : SupportedRepresentation (Q.iterate n)) :
    Quotient.mk (representationSetoid Q n) S = Quotient.mk (representationSetoid Q n) T ↔
      ∃ f : Deck Q n, pullSupported f.val S = T := Quotient.eq

end KroneckerAccumulatedRepresentationClasses
end
end

/- Original module: KroneckerAccumulatedGaugeDeckClasses -/
section
/-! Actual representation classes modulo accumulated deck pullback AND
commuting vertexwise linear isomorphism. This correct gauge/deck relation is
strictly richer than equality of coordinate matrices after deck pullback. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedGaugeDeckClasses
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerDimensionedCoverIsomorphisms
open KroneckerAccumulatedCoverDeckActions KroneckerAccumulatedDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

def DeckIso (Q : TypedQuiver) (n : ℕ) (S T : SupportedRepresentation (Q.iterate n)) : Prop :=
  ∃ f : Deck Q n, Nonempty (AcrossIso (pullSupported f.val S) T)

theorem deckIso_refl (Q : TypedQuiver) (n : ℕ) (S : SupportedRepresentation (Q.iterate n)) :
    DeckIso Q n S S := by
  refine ⟨identity Q n,?_⟩
  change Nonempty (AcrossIso (pullSupported (TypedQuiverIso.refl _) S) S)
  rw [pullSupported_refl]
  exact ⟨AcrossIso.refl S⟩

theorem deckIso_symm (Q : TypedQuiver) (n : ℕ) {S T : SupportedRepresentation (Q.iterate n)}
    (h : DeckIso Q n S T) : DeckIso Q n T S := by
  obtain ⟨f,⟨e⟩⟩ := h
  refine ⟨inverse f,?_⟩
  have ep := pullAcrossIso f.val.symm e.symm
  rw [← pullSupported_trans,quiverIso_symm_trans,pullSupported_refl] at ep
  exact ⟨ep⟩

theorem deckIso_trans (Q : TypedQuiver) (n : ℕ) {S T U : SupportedRepresentation (Q.iterate n)}
    (h : DeckIso Q n S T) (k : DeckIso Q n T U) : DeckIso Q n S U := by
  obtain ⟨f,⟨e⟩⟩ := h
  obtain ⟨g,⟨k⟩⟩ := k
  refine ⟨compose g f,?_⟩
  have ep := pullAcrossIso g.val e
  rw [← pullSupported_trans] at ep
  exact ⟨ep.trans k⟩

def gaugeDeckSetoid (Q : TypedQuiver) (n : ℕ) : Setoid (SupportedRepresentation (Q.iterate n)) where
  r := DeckIso Q n
  iseqv := ⟨deckIso_refl Q n,deckIso_symm Q n,deckIso_trans Q n⟩

abbrev GaugeDeckClass (Q : TypedQuiver) (n : ℕ) := Quotient (gaugeDeckSetoid Q n)

theorem deckIso_dimension_relation (Q : TypedQuiver) (n : ℕ)
    {S T : SupportedRepresentation (Q.iterate n)} (h : DeckIso Q n S T) : Related Q n S.1 T.1 := by
  obtain ⟨f,⟨e⟩⟩ := h
  exact ⟨f,e.dimension_eq⟩

def dimensionClass (Q : TypedQuiver) (n : ℕ) : GaugeDeckClass Q n → DimensionClass Q n :=
  Quotient.lift (fun S => Quotient.mk (dimensionSetoid Q n) S.1)
    (fun _ _ h => Quotient.sound (deckIso_dimension_relation Q n h))

end KroneckerAccumulatedGaugeDeckClasses
end
end

/- Original module: KroneckerConnectedDimensionTransport -/
section
/-! Nonempty finite dimensions connected by actual ambient typed walks are
preserved by quiver pullback. Direct-sum pushforward preserves and reflects
this property because all walks in the embedded component lift exactly. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerConnectedDimensionTransport
open KroneckerAbelianCover LabeledWalk KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerAccumulatedDimensionNormalization KroneckerDirectSumDimensionNaturality
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumEmbeddingLocalLifts
open KroneckerQuiverImageWalkLifting
attribute [local instance] Classical.decEq Classical.propDecidable

theorem connected_pull {P Q : TypedQuiver} (f : TypedQuiverIso P Q) (d : Q.V →₀ ℕ)
    (h : ConnectedDimension Q d) : ConnectedDimension P (pullDimension f d) := by
  obtain ⟨r,hc⟩ := h
  have hr : f.vertexEquiv.symm r.val ∈ (pullDimension f d).support := by
    simpa only [Finsupp.mem_support_iff,pullDimension_apply,Equiv.apply_symm_apply] using r.property
  refine ⟨⟨f.vertexEquiv.symm r.val,hr⟩,?_⟩
  intro v
  have hv : f.vertexEquiv v.val ∈ d.support := by
    simpa only [Finsupp.mem_support_iff,pullDimension_apply] using v.property
  obtain ⟨p⟩ := hc ⟨f.vertexEquiv v.val,hv⟩
  exact ⟨castEndpoints rfl (f.vertexEquiv.symm_apply_apply v.val)
    (transport f.symm.vertexEquiv f.symm.arrowEquiv f.symm.map_source f.symm.map_target p)⟩

theorem connected_pull_iff {P Q : TypedQuiver} (f : TypedQuiverIso P Q) (d : Q.V →₀ ℕ) :
    ConnectedDimension P (pullDimension f d) ↔ ConnectedDimension Q d := by
  constructor
  · intro h
    have hh := connected_pull f.symm (pullDimension f d) h
    rwa [← pullDimension_trans,quiverIso_symm_trans,pullDimension_refl] at hh
  · exact connected_pull f d

theorem connected_push_iff (Q : TypedQuiver) (n : ℕ)
    (d : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) :
    ConnectedDimension (Q.iterate n) (pushDimension Q n d) ↔
      ConnectedDimension (KroneckerDirectSumIteratedGirth.iterate Q n) d := by
  constructor
  · rintro ⟨r,hc⟩
    obtain ⟨u,hu⟩ := pushDimension_in_image Q n d r.property
    have hm : u ∈ d.support := by
      apply Finsupp.mem_support_iff.mpr
      have hh := Finsupp.mem_support_iff.mp r.property
      rw [← hu,pushDimension_apply] at hh
      exact hh
    refine ⟨⟨u,hm⟩,?_⟩
    intro v
    have hv : (embedding Q n).vertex v.val ∈ (pushDimension Q n d).support := by
      rw [Finsupp.mem_support_iff,pushDimension_apply]
      exact Finsupp.mem_support_iff.mp v.property
    obtain ⟨p⟩ := hc ⟨(embedding Q n).vertex v.val,hv⟩
    exact ⟨(walkEquiv (embedding Q n) (embedding_locallySurjective Q n)
      (embedding_injective Q n).1 (embedding_injective Q n).2 u v.val).symm (castEndpoints hu.symm rfl p)⟩
  · rintro ⟨r,hc⟩
    have hr : (embedding Q n).vertex r.val ∈ (pushDimension Q n d).support := by
      rw [Finsupp.mem_support_iff,pushDimension_apply]
      exact Finsupp.mem_support_iff.mp r.property
    refine ⟨⟨(embedding Q n).vertex r.val,hr⟩,?_⟩
    intro v
    obtain ⟨w,hw⟩ := pushDimension_in_image Q n d v.property
    have hm : w ∈ d.support := by
      apply Finsupp.mem_support_iff.mpr
      have hh := Finsupp.mem_support_iff.mp v.property
      rw [← hw,pushDimension_apply] at hh
      exact hh
    obtain ⟨p⟩ := hc ⟨w,hm⟩
    exact ⟨castEndpoints rfl hw ((embedding Q n).walk p)⟩

end KroneckerConnectedDimensionTransport
end
end

/- Original module: KroneckerConnectedDimensionClassEquivalence -/
section
/-! The direct-sum/product bridge is an exact equivalence on accumulated
classes of nonempty connected finite dimension supports. Faithfulness uses
the one-root restriction theorem; surjectivity uses actual root normalization. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerConnectedDimensionClassEquivalence
open KroneckerAbelianCover KroneckerAccumulatedDimensionNormalization
open KroneckerConnectedDimensionTransport KroneckerDirectSumDimensionNaturality
open KroneckerDirectSumDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

def ProductConnected (Q : TypedQuiver) (n : ℕ) : KroneckerAccumulatedDimensionClasses.DimensionClass Q n → Prop :=
  Quotient.lift (ConnectedDimension (Q.iterate n)) (by
    rintro d e ⟨f,rfl⟩
    exact propext (connected_pull_iff f.val d).symm)

def DirectConnected (Q : TypedQuiver) (n : ℕ) : DimensionClass Q n → Prop :=
  Quotient.lift (ConnectedDimension (KroneckerDirectSumIteratedGirth.iterate Q n)) (by
    rintro d e ⟨f,rfl⟩
    exact propext (connected_pull_iff f.val d).symm)

theorem connected_class_iff (Q : TypedQuiver) (n : ℕ) (q : DimensionClass Q n) :
    ProductConnected Q n (productClass Q n q) ↔ DirectConnected Q n q := by
  induction q using Quotient.inductionOn with | h d =>
    exact connected_push_iff Q n d

theorem connected_class_surjective (Q : TypedQuiver) (n : ℕ)
    (q : KroneckerAccumulatedDimensionClasses.DimensionClass Q n) (hq : ProductConnected Q n q) :
    ∃ c : DimensionClass Q n, DirectConnected Q n c ∧ productClass Q n c = q := by
  induction q using Quotient.inductionOn with | h d =>
    obtain ⟨δ,hδ⟩ := class_has_direct_sum_representative Q n d hq
    have he : Quotient.mk (KroneckerAccumulatedDimensionClasses.dimensionSetoid Q n) d =
        productClass Q n (Quotient.mk (dimensionSetoid Q n) δ) := Quotient.sound hδ
    refine ⟨Quotient.mk (dimensionSetoid Q n) δ,?_,he.symm⟩
    apply (connected_class_iff Q n _).mp
    rw [← he]
    exact hq


end KroneckerConnectedDimensionClassEquivalence
end
end

/- Original module: KroneckerDirectSumGaugeDeckClasses -/
section
/-! Gauge/deck classes for the genuine direct-sum iterate use recursively
finite-character transformations and actual commuting vertexwise linear
isomorphisms. Reflexivity, symmetry, transitivity and the dimension projection
are checked on the representation pullbacks. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumGaugeDeckClasses
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerDimensionedCoverIsomorphisms
open KroneckerDirectSumAccumulatedActions KroneckerDirectSumDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

def DeckIso (Q : TypedQuiver) (n : ℕ)
    (S T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) : Prop :=
  ∃ f : Deck Q n, Nonempty (AcrossIso (pullSupported f.val S) T)

theorem deckIso_refl (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) : DeckIso Q n S S := by
  refine ⟨identity Q n,?_⟩
  change Nonempty (AcrossIso (pullSupported (TypedQuiverIso.refl _) S) S)
  rw [pullSupported_refl]
  exact ⟨AcrossIso.refl S⟩

theorem deckIso_symm (Q : TypedQuiver) (n : ℕ)
    {S T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)}
    (h : DeckIso Q n S T) : DeckIso Q n T S := by
  obtain ⟨f,⟨e⟩⟩ := h
  refine ⟨inverse f,?_⟩
  have ep := pullAcrossIso f.val.symm e.symm
  rw [← pullSupported_trans,quiverIso_symm_trans,pullSupported_refl] at ep
  exact ⟨ep⟩

theorem deckIso_trans (Q : TypedQuiver) (n : ℕ)
    {S T U : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)}
    (h : DeckIso Q n S T) (k : DeckIso Q n T U) : DeckIso Q n S U := by
  obtain ⟨f,⟨e⟩⟩ := h
  obtain ⟨g,⟨k⟩⟩ := k
  refine ⟨compose g f,?_⟩
  have ep := pullAcrossIso g.val e
  rw [← pullSupported_trans] at ep
  exact ⟨ep.trans k⟩

def gaugeDeckSetoid (Q : TypedQuiver) (n : ℕ) :
    Setoid (SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) where
  r := DeckIso Q n
  iseqv := ⟨deckIso_refl Q n,deckIso_symm Q n,deckIso_trans Q n⟩

abbrev GaugeDeckClass (Q : TypedQuiver) (n : ℕ) := Quotient (gaugeDeckSetoid Q n)

theorem deckIso_dimension_relation (Q : TypedQuiver) (n : ℕ)
    {S T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)}
    (h : DeckIso Q n S T) : Related Q n S.1 T.1 := by
  obtain ⟨f,⟨e⟩⟩ := h
  exact ⟨f,e.dimension_eq⟩

def dimensionClass (Q : TypedQuiver) (n : ℕ) : GaugeDeckClass Q n → DimensionClass Q n :=
  Quotient.lift (fun S => Quotient.mk (dimensionSetoid Q n) S.1)
    (fun _ _ h => Quotient.sound (deckIso_dimension_relation Q n h))

end KroneckerDirectSumGaugeDeckClasses
end
end

/- Original module: KroneckerDirectSumGaugeDeckFaithfulness -/
section
/-! Genuine direct-sum representations are gauge/deck-isomorphic exactly when
their embedded product representations are. This includes empty support and
uses the SAME restricted accumulated map whenever support is nonzero. Hence
the entire direct-sum gauge/deck quotient embeds faithfully. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumGaugeDeckFaithfulness
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerDirectSumSupportedBridge
open KroneckerDirectSumSupportedNaturality KroneckerDirectSumDeckExtension
open KroneckerDirectSumGaugeDeckClasses KroneckerDirectSumNonzeroRestriction
open KroneckerDirectSumDimensionNaturality KroneckerDirectSumSupportedStatistics
attribute [local instance] Classical.decEq Classical.propDecidable

theorem deckIso_iff_product (Q : TypedQuiver) (n : ℕ)
    (S T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)) :
    DeckIso Q n S T ↔ KroneckerAccumulatedGaugeDeckClasses.DeckIso Q n (push Q n S) (push Q n T) := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨extension f,?_⟩
    have hh := (push_across_iff Q n (pullSupported f.val S) T).mpr hf
    rwa [KroneckerDirectSumSupportedNaturality.push_pull Q n f.val (extension f).val (extension_compatible f)] at hh
  · rintro ⟨F,⟨a⟩⟩
    have hd := a.dimension_eq
    change pullDimension F.val (push Q n S).1 = (push Q n T).1 at hd
    rw [push_dimension,push_dimension] at hd
    by_cases hT : T.1 = 0
    · have hs : S.1 = 0 := by
        have hr : KroneckerDirectSumDimensionClasses.Related Q n S.1 T.1 :=
          (KroneckerDirectSumDimensionClasses.related_iff_product Q n S.1 T.1).mpr ⟨F,hd⟩
        obtain ⟨f,hf⟩ := hr
        ext v
        have hh := congrArg (fun δ => δ (f.val.vertexEquiv.symm v)) hf
        rw [pullDimension_apply,Equiv.apply_symm_apply,hT,Finsupp.zero_apply] at hh
        exact hh
      rw [zero_supported_unique _ S T hs hT]
      exact deckIso_refl Q n T
    · obtain ⟨f,hf⟩ := nonzero_dimension_restriction Q n F S.1 T.1 hT hd
      refine ⟨f,(push_across_iff Q n (pullSupported f.val S) T).mp ?_⟩
      rw [KroneckerDirectSumSupportedNaturality.push_pull Q n f.val F.val hf]
      exact ⟨a⟩

def productClass (Q : TypedQuiver) (n : ℕ) : GaugeDeckClass Q n →
    KroneckerAccumulatedGaugeDeckClasses.GaugeDeckClass Q n :=
  Quotient.lift (fun S => Quotient.mk (KroneckerAccumulatedGaugeDeckClasses.gaugeDeckSetoid Q n) (push Q n S))
    (fun S T h => Quotient.sound ((deckIso_iff_product Q n S T).mp h))

theorem productClass_injective (Q : TypedQuiver) (n : ℕ) : Function.Injective (productClass Q n) := by
  intro x y
  induction x using Quotient.inductionOn with | h S =>
    induction y using Quotient.inductionOn with | h T =>
      intro h
      exact Quotient.sound ((deckIso_iff_product Q n S T).mpr (Quotient.exact h))

end KroneckerDirectSumGaugeDeckFaithfulness
end
end

/- Original module: KroneckerConnectedGaugeClassEquivalence -/
section
/-! Accumulated gauge/deck classes of actual representations with nonempty
connected dimension support are equivalent in the product and direct-sum
models. Surjectivity normalizes a root and descends the very same pulled
representation; faithfulness is the checked one-root restriction theorem. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerConnectedGaugeClassEquivalence
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerConnectedDimensionClassEquivalence KroneckerAccumulatedDimensionNormalization
open KroneckerDirectSumSupportedBridge KroneckerDirectSumGaugeDeckFaithfulness
open KroneckerDirectSumDimensionNaturality KroneckerDimensionedCoverIsomorphisms
attribute [local instance] Classical.decEq Classical.propDecidable

def ProductConnected (Q : TypedQuiver) (n : ℕ) (c : KroneckerAccumulatedGaugeDeckClasses.GaugeDeckClass Q n) : Prop :=
  KroneckerConnectedDimensionClassEquivalence.ProductConnected Q n (KroneckerAccumulatedGaugeDeckClasses.dimensionClass Q n c)

def DirectConnected (Q : TypedQuiver) (n : ℕ) (c : KroneckerDirectSumGaugeDeckClasses.GaugeDeckClass Q n) : Prop :=
  KroneckerConnectedDimensionClassEquivalence.DirectConnected Q n (KroneckerDirectSumGaugeDeckClasses.dimensionClass Q n c)

theorem product_dimension (Q : TypedQuiver) (n : ℕ) (c : KroneckerDirectSumGaugeDeckClasses.GaugeDeckClass Q n) :
    KroneckerAccumulatedGaugeDeckClasses.dimensionClass Q n (productClass Q n c) =
      KroneckerDirectSumDimensionClasses.productClass Q n (KroneckerDirectSumGaugeDeckClasses.dimensionClass Q n c) := by
  induction c using Quotient.inductionOn with | h S =>
    change Quotient.mk _ (push Q n S).1 = Quotient.mk _ (pushDimension Q n S.1)
    rw [push_dimension]

theorem connected_class_iff (Q : TypedQuiver) (n : ℕ) (c : KroneckerDirectSumGaugeDeckClasses.GaugeDeckClass Q n) :
    ProductConnected Q n (productClass Q n c) ↔ DirectConnected Q n c := by
  unfold ProductConnected DirectConnected
  rw [product_dimension]
  exact KroneckerConnectedDimensionClassEquivalence.connected_class_iff Q n _

theorem connected_class_surjective (Q : TypedQuiver) (n : ℕ)
    (c : KroneckerAccumulatedGaugeDeckClasses.GaugeDeckClass Q n) (hc : ProductConnected Q n c) :
    ∃ b : KroneckerDirectSumGaugeDeckClasses.GaugeDeckClass Q n, DirectConnected Q n b ∧ productClass Q n b = c := by
  induction c using Quotient.inductionOn with | h S =>
    obtain ⟨F,hF,_⟩ := exists_normalized_dimension Q n S.1 hc
    let T := bridge Q n ⟨pullSupported F.val S,hF⟩
    let b := Quotient.mk (KroneckerDirectSumGaugeDeckClasses.gaugeDeckSetoid Q n) T
    have hp : push Q n T = pullSupported F.val S := push_descend Q n _
    have he : Quotient.mk (KroneckerAccumulatedGaugeDeckClasses.gaugeDeckSetoid Q n) S = productClass Q n b := by
      apply Quotient.sound
      refine ⟨F,?_⟩
      change Nonempty (AcrossIso (pullSupported F.val S) (push Q n T))
      rw [hp]
      exact ⟨AcrossIso.refl _⟩
    refine ⟨b,?_,he.symm⟩
    apply (connected_class_iff Q n b).mp
    rw [← he]
    exact hc


end KroneckerConnectedGaugeClassEquivalence
end
end

/- Original module: KroneckerExactDirectSumNormalForm -/
section
/-! Every connected product representation has a direct-sum normal form whose
push is EXACTLY its accumulated pullback. Nonzero support, total size, base
multiplicities, stability and self-Euler form are preserved by this same
normalization, so later quotient comparisons do not choose unrelated matrices. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExactDirectSumNormalForm
open KroneckerAbelianCover KroneckerQuiverPullbackComposition
open KroneckerAccumulatedDimensionNormalization KroneckerDirectSumSupportedBridge
open KroneckerDirectSumSupportedStatistics KroneckerDirectSumStablePullback
open KroneckerFiniteSupportStability KroneckerAccumulatedSupportEuler
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_exact_normal_form (Q : TypedQuiver) (n : ℕ)
    (S : SupportedRepresentation (Q.iterate n)) (hc : ConnectedDimension (Q.iterate n) S.1) :
    ∃ (F : KroneckerAccumulatedCoverDeckActions.Deck Q n)
      (T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n)),
      push Q n T = pullSupported F.val S := by
  obtain ⟨F,hF,_⟩ := exists_normalized_dimension Q n S.1 hc
  exact ⟨F,bridge Q n ⟨pullSupported F.val S,hF⟩,push_descend Q n _⟩

theorem normal_form_statistics (Q : TypedQuiver) (n : ℕ) (θ : Q.V → ℤ)
    (S : SupportedRepresentation (Q.iterate n))
    (T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate Q n))
    (F : KroneckerAccumulatedCoverDeckActions.Deck Q n) (h : push Q n T = pullSupported F.val S) :
    (T.1 ≠ 0 ↔ S.1 ≠ 0) ∧
    KroneckerDirectSumBaseDimensions.baseDimension Q n T.1 =
      KroneckerAccumulatedDeckBaseDimensions.baseDimension Q n S.1 ∧
    T.1.sum (fun _ k => k) = S.1.sum (fun _ k => k) ∧
    (FiniteSupportStable T.1 (θ ∘ KroneckerDirectSumIteratedEmbedding.baseVertex Q n) T.2 ↔
      FiniteSupportStable S.1 (θ ∘ TypedQuiver.baseVertex Q n) S.2) := by
  refine ⟨?_,?_,?_,?_⟩
  · apply not_congr
    rw [← push_zero_iff Q n T,h]
    exact pull_zero_iff F.val S.1
  · rw [← push_base Q n T,h]
    exact KroneckerAccumulatedDeckBaseDimensions.baseDimension_pull Q n F S.1
  · rw [← push_sum Q n T,h]
    exact pull_sum F.val S.1
  · rw [← push_stable_iff Q n θ T,h]
    exact KroneckerAccumulatedDeckStablePullback.accumulated_stable_iff Q n F S.1 θ S.2


end KroneckerExactDirectSumNormalForm
end
end
end

