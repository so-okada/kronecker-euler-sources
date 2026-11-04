import KroneckerCoprimeKingNumerator
import KroneckerGlobalCoverKingBridge
import KroneckerUniversalStableIndexBounds

/- Original module: KroneckerBipartiteCoprimeSemistability -/
section
set_option autoImplicit false
namespace KroneckerBipartiteCoprimeSemistability
open Module KroneckerPositiveSupportRestriction
open KroneckerBipartiteSubrepresentationRestriction KroneckerCoprimeKingNumerator
open scoped BigOperators

/-- Intrinsic semistability tests all nonzero proper vertexwise subrepresentations. -/
def KingSemistable {I J : Type} [Fintype I] [Fintype J] (R : Representation I J) : Prop :=
  ∀ U : Subrep R, 0 < sourceSize U + sinkSize U →
    sourceSize U + sinkSize U < sourceDimension R + sinkDimension R →
    sinkDimension R * sourceSize U ≤ sourceDimension R * sinkSize U







end KroneckerBipartiteCoprimeSemistability
end

/- Original module: KroneckerCoverCoprimeGenericity -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KroneckerCoverCoprimeGenericity
open Module KroneckerReducedColorWords KroneckerWordParity
open KroneckerCoverSupportRadius KroneckerStableCoverIndexFinite
open KroneckerGlobalCoverCoordinates KroneckerPositiveSupportRestriction
open KroneckerBipartiteSubrepresentationRestriction
open KroneckerBipartiteCoprimeSemistability KroneckerCoprimeKingNumerator
open scoped BigOperators



end KroneckerCoverCoprimeGenericity
end

/- Original module: KroneckerManuscriptCoverParameters -/
section
/-! Exact source/sink dimensions and stability signs for the manuscript cover.
These lemmas concern the genuine colored universal cover and all vertexwise
subrepresentations. They do not identify its moduli with a topological space.
`negativeWeight a b` equals `KroneckerCanonicalKroneckerModuli.character a b`.
Its value on dimensions (u,v) is b*u - a*v, the negative of the manuscript's
stability functional a*v - b*u. Thus negative weight is the manuscript's
strict positive stability condition, not the negative of `character`. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptCoverParameters
open KroneckerReducedColorWords KroneckerWordParity
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportStability KroneckerFiniteQuiverHom
open KroneckerUniversalWordBaseProjection KroneckerGlobalCoverCoordinates
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

def pairDimension (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

def negativeWeight (a b : ℕ) (i : Fin 2) : ℤ := if i = 0 then b else -(a : ℤ)

@[simp] theorem pairDimension_zero (a b : ℕ) : pairDimension a b 0 = a := by
  simp [pairDimension]
@[simp] theorem pairDimension_one (a b : ℕ) : pairDimension a b 1 = b := by
  simp [pairDimension]

theorem pairDimension_total (a b : ℕ) :
    (pairDimension a b).sum (fun _ n => n) = a + b := by
  simp [pairDimension, Finsupp.sum_add_index]

theorem base_component (d : Word →₀ ℕ) (i : Fin 2) :
    d.mapDomain baseVertex i = d.sum (fun w n => if parity w = i.val then n else 0) := by
  simp only [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
  apply Finsupp.sum_congr
  intro w _
  congr 1
  exact propext (by simp [baseVertex, Fin.ext_iff, eq_comm])

theorem compatible_iff (d : Word →₀ ℕ) (a b : ℕ) :
    d.mapDomain baseVertex = pairDimension a b ↔
      d.sum (fun w n => if parity w = 0 then n else 0) = a ∧
      d.sum (fun w n => if parity w = 1 then n else 0) = b := by
  constructor
  · intro h
    constructor
    · simpa only [base_component, pairDimension_zero, Fin.val_zero] using congrArg (fun D : Fin 2 →₀ ℕ => D 0) h
    · simpa only [base_component, pairDimension_one, Fin.val_one] using congrArg (fun D : Fin 2 →₀ ℕ => D 1) h
  · rintro ⟨h0,h1⟩
    ext i
    fin_cases i <;> simp [base_component, h0, h1]

theorem compatible_cast_totals (d : Word →₀ ℕ) (a b : ℕ)
    (hD : d.mapDomain baseVertex = pairDimension a b) :
    d.sum (fun w n => if parity w = 0 then (n : ℤ) else 0) = a ∧
    d.sum (fun w n => if parity w = 1 then (n : ℤ) else 0) = b := by
  obtain ⟨hs,ht⟩ := (compatible_iff d a b).mp hD
  constructor
  · simpa [Finsupp.sum] using congrArg (fun n : ℕ => (n : ℤ)) hs
  · simpa [Finsupp.sum] using congrArg (fun n : ℕ => (n : ℤ)) ht

theorem compatible_total (d : Word →₀ ℕ) (a b : ℕ)
    (hD : d.mapDomain baseVertex = pairDimension a b) :
    d.sum (fun _ n => n) = a+b := by
  exact (KroneckerFixedDimensionStableRealizationDictionary.total_of_original_dimension d _ _ hD).trans
    (pairDimension_total a b)

theorem compatible_nonzero (d : Word →₀ ℕ) (a b : ℕ) (ha : 0<a)
    (hD : d.mapDomain baseVertex = pairDimension a b) : d ≠ 0 := by
  intro hz
  have h := compatible_total d a b hD
  simp [hz] at h
  omega

theorem character_on_support (d : Word →₀ ℕ) (a b : ℕ)
    (hD : d.mapDomain baseVertex = pairDimension a b) (v : SupportVertex d) :
    negativeWeight a b (baseVertex v.val) =
      KroneckerStableCoverIndexFinite.coverKingWeight d v := by
  obtain ⟨hs,ht⟩ := compatible_cast_totals d a b hD
  simp only [negativeWeight, KroneckerStableCoverIndexFinite.coverKingWeight, hs, ht]
  congr 1
  simp [baseVertex, Fin.ext_iff]

theorem weight_formula (d : Word →₀ ℕ) (a b : ℕ)
    (hD : d.mapDomain baseVertex = pairDimension a b) (f : SupportVertex d → ℕ) :
    (∑ v, negativeWeight a b (baseVertex v.val) * (f v : ℤ)) =
      (b : ℤ) * paritySum d 0 f - (a : ℤ) * paritySum d 1 f := by
  simp_rw [character_on_support d a b hD]
  rw [coordinate_king_weight_sum]
  obtain ⟨hs,ht⟩ := compatible_cast_totals d a b hD
  rw [hs,ht]

theorem compatible_balance (d : Word →₀ ℕ) (a b : ℕ)
    (hD : d.mapDomain baseVertex = pairDimension a b) :
    supportBalance d (negativeWeight a b ∘ baseVertex) = 0 := by
  change (∑ v : SupportVertex d, negativeWeight a b (baseVertex v.val) * (d v.val : ℤ)) = 0
  simp_rw [character_on_support d a b hD]
  exact coordinate_full_king_weight_zero d

/-- The manuscript's positive numerator, applied to ALL subrepresentations. -/
def ManuscriptStable (d : Word →₀ ℕ) (a b : ℕ)
    (R : Representation coloredCoverQuiver.source coloredCoverQuiver.target (fun w => d w)) : Prop :=
  ∀ U : Subrep R, 0 < supportSize d U → supportSize d U < supportTotalDimension d →
    0 < (a : ℤ) * paritySum d 1 (fun v => Module.finrank ℂ (U.space v.val)) -
        (b : ℤ) * paritySum d 0 (fun v => Module.finrank ℂ (U.space v.val))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem stability_sign_dictionary (d : Word →₀ ℕ) (a b : ℕ)
    (hD : d.mapDomain baseVertex = pairDimension a b)
    (R : Representation coloredCoverQuiver.source coloredCoverQuiver.target (fun w => d w)) :
    FiniteSupportStable d (negativeWeight a b ∘ baseVertex) R ↔ ManuscriptStable d a b R := by
  have hw (U : Subrep R) : supportWeight d (negativeWeight a b ∘ baseVertex) U =
      (b : ℤ) * paritySum d 0 (fun v => Module.finrank ℂ (U.space v.val)) -
      (a : ℤ) * paritySum d 1 (fun v => Module.finrank ℂ (U.space v.val)) :=
    weight_formula d a b hD _
  constructor
  · intro h U hn hp
    have hU := h.2 U hn hp
    rw [hw] at hU
    linarith
  · intro h
    refine ⟨compatible_balance d a b hD,fun U hn hp => ?_⟩
    rw [hw]
    have hU := h U hn hp
    linarith



end KroneckerManuscriptCoverParameters
end
end
