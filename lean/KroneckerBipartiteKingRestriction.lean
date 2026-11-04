import KroneckerFixedCoverReconstruction

/- Original module: KroneckerBipartiteSubrepresentationRestriction -/
section
/- DEVELOPMENT SOURCE: certification status is recorded separately. -/
set_option autoImplicit false
namespace KroneckerBipartiteSubrepresentationRestriction
open Module KroneckerPositiveSupportRestriction

/-- All vertexwise invariant submodule families of an arbitrary bipartite
representation, with no coordinate-subspace restriction. -/
structure Subrep {I J : Type} (R : Representation I J) where
  source : ∀ i, Submodule ℂ (R.SourceSpace i)
  sink : ∀ j, Submodule ℂ (R.SinkSpace j)
  invariant : ∀ i j x, x ∈ source i → R.arrow i j x ∈ sink j

theorem subrep_ext {I J : Type} {R : Representation I J} {U W : Subrep R}
    (hs : U.source = W.source) (ht : U.sink = W.sink) : U = W := by
  cases U
  cases W
  cases hs
  cases ht
  rfl

theorem submodule_eq_bot_of_finrank_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (P : Submodule ℂ V) (h : finrank ℂ V = 0) : P = ⊥ := by
  let : Subsingleton V := Module.finrank_zero_iff.mp h
  apply le_antisymm
  · intro x _
    exact Subsingleton.elim x 0
  · exact bot_le

def restrictSubrep {I J : Type} {R : Representation I J} (U : Subrep R) :
    Subrep (restriction R) where
  source i := U.source i.val
  sink j := U.sink j.val
  invariant i j x hx := U.invariant i.val j.val x hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend a restricted subrepresentation at the original vertex labels. -/
noncomputable def extendSubrep {I J : Type} {R : Representation I J}
    (U : Subrep (restriction R)) : Subrep R where
  source i := if h : 0 < finrank ℂ (R.SourceSpace i) then U.source ⟨i,h⟩ else ⊥
  sink j := if h : 0 < finrank ℂ (R.SinkSpace j) then U.sink ⟨j,h⟩ else ⊥
  invariant := by
    classical
    intro i j x hx
    by_cases hs : 0 < finrank ℂ (R.SourceSpace i)
    · by_cases ht : 0 < finrank ℂ (R.SinkSpace j)
      · simp only [dite_eq_left hs] at hx
        rw [dite_eq_left ht]
        exact U.invariant ⟨i,hs⟩ ⟨j,ht⟩ x hx
      · have hzero : finrank ℂ (R.SinkSpace j) = 0 := Nat.eq_zero_of_not_pos ht
        rw [arrow_zero_of_sink R i j hzero, LinearMap.zero_apply]
        exact Submodule.zero_mem _
    · simp only [dite_eq_right hs, Submodule.mem_bot] at hx
      subst x
      rw [map_zero]
      exact Submodule.zero_mem _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem restrict_extend {I J : Type} {R : Representation I J}
    (U : Subrep (restriction R)) : restrictSubrep (extendSubrep U) = U := by
  apply subrep_ext
  · funext i
    simp only [restrictSubrep, extendSubrep, dite_eq_left i.property]
  · funext j
    simp only [restrictSubrep, extendSubrep, dite_eq_left j.property]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem extend_restrict {I J : Type} {R : Representation I J}
    (U : Subrep R) : extendSubrep (restrictSubrep U) = U := by
  classical
  apply subrep_ext
  · funext i
    by_cases h : 0 < finrank ℂ (R.SourceSpace i)
    · simp only [extendSubrep, dite_eq_left h, restrictSubrep]
    · simp only [extendSubrep, dite_eq_right h]
      exact (submodule_eq_bot_of_finrank_zero (U.source i) (Nat.eq_zero_of_not_pos h)).symm
  · funext j
    by_cases h : 0 < finrank ℂ (R.SinkSpace j)
    · simp only [extendSubrep, dite_eq_left h, restrictSubrep]
    · simp only [extendSubrep, dite_eq_right h]
      exact (submodule_eq_bot_of_finrank_zero (U.sink j) (Nat.eq_zero_of_not_pos h)).symm

/-- The restriction identifies ALL subrepresentations, including all nonzero
proper ones after the dimension comparison. -/
noncomputable def restrictionSubrepEquiv {I J : Type} (R : Representation I J) :
    Subrep R ≃ Subrep (restriction R) where
  toFun := restrictSubrep
  invFun := extendSubrep
  left_inv := extend_restrict
  right_inv := restrict_extend

theorem source_subrep_dimension_zero {I J : Type} {R : Representation I J}
    (U : Subrep R) (i : I) (h : finrank ℂ (R.SourceSpace i) = 0) :
    finrank ℂ (U.source i) = 0 := by
  rw [submodule_eq_bot_of_finrank_zero (U.source i) h]
  simp

theorem sink_subrep_dimension_zero {I J : Type} {R : Representation I J}
    (U : Subrep R) (j : J) (h : finrank ℂ (R.SinkSpace j) = 0) :
    finrank ℂ (U.sink j) = 0 := by
  rw [submodule_eq_bot_of_finrank_zero (U.sink j) h]
  simp

end KroneckerBipartiteSubrepresentationRestriction
end

/- Original module: KroneckerBipartiteKingRestriction -/
section
/- DEVELOPMENT SOURCE: certification status is recorded separately. -/
set_option autoImplicit false
namespace KroneckerBipartiteSubrepresentationRestriction
open Module KroneckerPositiveSupportRestriction
open scoped BigOperators

noncomputable def sourceDimension {I J : Type} [Fintype I] (R : Representation I J) : ℕ :=
  ∑ i, finrank ℂ (R.SourceSpace i)
noncomputable def sinkDimension {I J : Type} [Fintype J] (R : Representation I J) : ℕ :=
  ∑ j, finrank ℂ (R.SinkSpace j)
noncomputable def sourceSize {I J : Type} [Fintype I] {R : Representation I J}
    (U : Subrep R) : ℕ := ∑ i, finrank ℂ (U.source i)
noncomputable def sinkSize {I J : Type} [Fintype J] {R : Representation I J}
    (U : Subrep R) : ℕ := ∑ j, finrank ℂ (U.sink j)

/-- Finite bipartite King stability, with the manuscript sign convention. -/
def KingStable {I J : Type} [Fintype I] [Fintype J] (R : Representation I J) : Prop :=
  ∀ U : Subrep R, 0 < sourceSize U + sinkSize U →
    sourceSize U + sinkSize U < sourceDimension R + sinkDimension R →
    sinkDimension R * sourceSize U < sourceDimension R * sinkSize U

noncomputable def supportSourceSize {I J : Type} {R : Representation I J}
    [Fintype (PositiveSource R)] (U : Subrep R) : ℕ :=
  ∑ i : PositiveSource R, finrank ℂ (U.source i.val)
noncomputable def supportSinkSize {I J : Type} {R : Representation I J}
    [Fintype (PositiveSink R)] (U : Subrep R) : ℕ :=
  ∑ j : PositiveSink R, finrank ℂ (U.sink j.val)

/-- For possibly infinite vertex sets, dimensions are summed over the finite
positive support. All omitted submodule dimensions are proved zero. -/
def SupportKingStable {I J : Type} (R : Representation I J)
    [Fintype (PositiveSource R)] [Fintype (PositiveSink R)] : Prop :=
  ∀ U : Subrep R, 0 < supportSourceSize U + supportSinkSize U →
    supportSourceSize U + supportSinkSize U <
      sourceDimension (restriction R) + sinkDimension (restriction R) →
    sinkDimension (restriction R) * supportSourceSize U <
      sourceDimension (restriction R) * supportSinkSize U

theorem restriction_size {I J : Type} {R : Representation I J}
    [Fintype (PositiveSource R)] [Fintype (PositiveSink R)] (U : Subrep R) :
    sourceSize (restrictSubrep U) = supportSourceSize U ∧
      sinkSize (restrictSubrep U) = supportSinkSize U := ⟨rfl,rfl⟩

theorem support_stability_iff_restriction {I J : Type} (R : Representation I J)
    [Fintype (PositiveSource R)] [Fintype (PositiveSink R)] :
    SupportKingStable R ↔ KingStable (restriction R) := by
  constructor
  · intro h U
    obtain ⟨W,rfl⟩ := (restrictionSubrepEquiv R).surjective U
    exact h W
  · intro h U
    exact h (restrictSubrep U)

/-- Every submodule at a zero-dimensional vertex is omitted without changing
its dimension sum. -/
theorem support_source_size_eq {I J : Type} [Fintype I] {R : Representation I J}
    [Fintype (PositiveSource R)] (U : Subrep R) : supportSourceSize U = sourceSize U := by
  classical
  apply Fintype.sum_of_injective (fun i : PositiveSource R => i.val) Subtype.val_injective
  · intro i hi
    apply source_subrep_dimension_zero U i
    by_contra hn
    exact hi ⟨⟨i,Nat.pos_of_ne_zero hn⟩,rfl⟩
  · intro i
    rfl

theorem support_sink_size_eq {I J : Type} [Fintype J] {R : Representation I J}
    [Fintype (PositiveSink R)] (U : Subrep R) : supportSinkSize U = sinkSize U := by
  classical
  apply Fintype.sum_of_injective (fun j : PositiveSink R => j.val) Subtype.val_injective
  · intro j hj
    apply sink_subrep_dimension_zero U j
    by_contra hn
    exact hj ⟨⟨j,Nat.pos_of_ne_zero hn⟩,rfl⟩
  · intro j
    rfl

theorem restriction_source_dimension {I J : Type} [Fintype I] (R : Representation I J)
    [Fintype (PositiveSource R)] : sourceDimension (restriction R) = sourceDimension R := by
  classical
  apply Fintype.sum_of_injective (fun i : PositiveSource R => i.val) Subtype.val_injective
  · intro i hi
    by_contra hn
    exact hi ⟨⟨i,Nat.pos_of_ne_zero hn⟩,rfl⟩
  · intro i
    rfl

theorem restriction_sink_dimension {I J : Type} [Fintype J] (R : Representation I J)
    [Fintype (PositiveSink R)] : sinkDimension (restriction R) = sinkDimension R := by
  classical
  apply Fintype.sum_of_injective (fun j : PositiveSink R => j.val) Subtype.val_injective
  · intro j hj
    by_contra hn
    exact hj ⟨⟨j,Nat.pos_of_ne_zero hn⟩,rfl⟩
  · intro j
    rfl

/-- The global finite-support definition agrees with the ordinary finite
vertex-set definition, including cases with zero-dimensional vertices. -/
theorem finite_stability_iff_support {I J : Type} [Fintype I] [Fintype J]
    (R : Representation I J) [Fintype (PositiveSource R)] [Fintype (PositiveSink R)] :
    KingStable R ↔ SupportKingStable R := by
  simp only [KingStable, SupportKingStable, support_source_size_eq, support_sink_size_eq,
    restriction_source_dimension, restriction_sink_dimension]

end KroneckerBipartiteSubrepresentationRestriction
end
