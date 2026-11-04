import KroneckerStableCoverIndexFinite
import KroneckerBipartiteIsoSubrepresentations

/- Original module: KroneckerGlobalCoverCoordinates -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KroneckerGlobalCoverCoordinates
open Module KroneckerReducedColorWords KroneckerWordParity KroneckerColorWordCover
open KroneckerBlockCoverExtension KroneckerCoverSupportRadius
open KroneckerStableCoverIndexFinite

abbrev GlobalRepresentation := KroneckerFixedCoverReconstruction.CoverRepresentation

noncomputable def sourceCoordinates (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val) (i : CoverSource) :
    R.SourceSpace i ≃ₗ[ℂ] KroneckerFiniteQuiverHom.Space (d i.val) :=
  (Module.finBasisOfFinrankEq ℂ (R.SourceSpace i) (hs i)).equivFun

noncomputable def sinkCoordinates (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val) (j : CoverSink) :
    R.SinkSpace j ≃ₗ[ℂ] KroneckerFiniteQuiverHom.Space (d j.val) :=
  (Module.finBasisOfFinrankEq ℂ (R.SinkSpace j) (ht j)).equivFun

def arrowSource {d : Word →₀ ℕ} (a : CoverArrow d) : CoverSource :=
  ⟨a.val.1.val,a.property.1⟩

def arrowSink {d : Word →₀ ℕ} (a : CoverArrow d) : CoverSink :=
  ⟨a.val.2.val, by
    have h := cover_opposite_parity a.property.2
    have hp : parity a.val.2.val < 2 := Nat.mod_lt _ (by decide)
    have hs := a.property.1
    omega⟩

/-- Actual global arrow maps, restricted to the finite positive support and put
in coordinates. Every cover edge is retained. -/
noncomputable def toCoordinates (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val) : CoverRepresentation d where
  arrow a := (sinkCoordinates R d ht (arrowSink a)).toLinearMap.comp
    ((R.arrow (arrowSource a) (arrowSink a)).comp
      (sourceCoordinates R d hs (arrowSource a)).symm.toLinearMap)

theorem coordinate_arrow_commutes (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val) (a : CoverArrow d)
    (x : R.SourceSpace (arrowSource a)) :
    (toCoordinates R d hs ht).arrow a (sourceCoordinates R d hs (arrowSource a) x) =
      sinkCoordinates R d ht (arrowSink a) (R.arrow (arrowSource a) (arrowSink a) x) := by
  change sinkCoordinates R d ht (arrowSink a)
    (R.arrow (arrowSource a) (arrowSink a)
      ((sourceCoordinates R d hs (arrowSource a)).symm
        (sourceCoordinates R d hs (arrowSource a) x))) = _
  rw [LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pull back an arbitrary coordinate subrepresentation, with zero spaces off support. -/
noncomputable def pullSubrep (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    (U : KroneckerFiniteQuiverHom.Subrep (toCoordinates R d hs ht)) :
    KroneckerBipartiteSubrepresentationRestriction.Subrep R.toRepresentation where
  source i := if h : i.val ∈ d.support then
    (U.space ⟨i.val,h⟩).comap (sourceCoordinates R d hs i).toLinearMap else ⊥
  sink j := if h : j.val ∈ d.support then
    (U.space ⟨j.val,h⟩).comap (sinkCoordinates R d ht j).toLinearMap else ⊥
  invariant := by
    classical
    intro i j x hx
    by_cases hi : i.val ∈ d.support
    · by_cases hj : j.val ∈ d.support
      · by_cases ha : cover.Adj i.val j.val
        · let a : CoverArrow d := ⟨(⟨i.val,hi⟩,⟨j.val,hj⟩),i.property,ha⟩
          simp only [dite_eq_left hi, Submodule.mem_comap] at hx
          simp only [dite_eq_left hj, Submodule.mem_comap]
          have hh := U.invariant a (sourceCoordinates R d hs i x) hx
          change (toCoordinates R d hs ht).arrow a
            (sourceCoordinates R d hs (arrowSource a) x) ∈ U.space a.val.2 at hh
          rw [coordinate_arrow_commutes] at hh
          exact hh
        · rw [R.nonedge_zero i j ha, LinearMap.zero_apply]
          exact Submodule.zero_mem _
      · have hz : finrank ℂ (R.SinkSpace j) = 0 :=
          (ht j).trans (Finsupp.notMem_support_iff.mp hj)
        rw [KroneckerPositiveSupportRestriction.arrow_zero_of_sink R.toRepresentation i j hz,
          LinearMap.zero_apply]
        exact Submodule.zero_mem _
    · simp only [dite_eq_right hi, Submodule.mem_bot] at hx
      subst x
      rw [map_zero]
      exact Submodule.zero_mem _

/-- Pullback preserves the dimension of every positive source subspace. -/
theorem pull_source_finrank (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    (U : KroneckerFiniteQuiverHom.Subrep (toCoordinates R d hs ht))
    (i : CoverSource) (hi : i.val ∈ d.support) :
    finrank ℂ ((pullSubrep R d hs ht U).source i) = finrank ℂ (U.space ⟨i.val,hi⟩) := by
  rw [show (pullSubrep R d hs ht U).source i =
    (U.space ⟨i.val,hi⟩).comap (sourceCoordinates R d hs i).toLinearMap from dite_eq_left hi]
  exact KroneckerBipartiteSubrepresentationRestriction.finrank_comap_equiv _ _

/-- Pullback preserves the dimension of every positive sink subspace. -/
theorem pull_sink_finrank (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    (U : KroneckerFiniteQuiverHom.Subrep (toCoordinates R d hs ht))
    (j : CoverSink) (hj : j.val ∈ d.support) :
    finrank ℂ ((pullSubrep R d hs ht U).sink j) = finrank ℂ (U.space ⟨j.val,hj⟩) := by
  rw [show (pullSubrep R d hs ht U).sink j =
    (U.space ⟨j.val,hj⟩).comap (sinkCoordinates R d ht j).toLinearMap from dite_eq_left hj]
  exact KroneckerBipartiteSubrepresentationRestriction.finrank_comap_equiv _ _

end KroneckerGlobalCoverCoordinates
end

/- Original module: KroneckerGlobalCoverDimensionSums -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KroneckerGlobalCoverCoordinates
open Module KroneckerReducedColorWords KroneckerWordParity KroneckerColorWordCover
open KroneckerBlockCoverExtension KroneckerCoverSupportRadius
open KroneckerPositiveSupportRestriction
open scoped BigOperators

noncomputable def paritySum (d : Word →₀ ℕ) (p : ℕ) (f : SupportVertex d → ℕ) : ℕ :=
  ∑ v, if parity v.val = p then f v else 0

theorem paritySum_split (d : Word →₀ ℕ) (f : SupportVertex d → ℕ) :
    paritySum d 0 f + paritySum d 1 f = ∑ v, f v := by
  classical
  rw [paritySum, paritySum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hp : parity v.val < 2 := Nat.mod_lt _ (by decide)
  by_cases h : parity v.val = 0
  · have h1 : parity v.val ≠ 1 := by omega
    simp [h]
  · have h1 : parity v.val = 1 := by omega
    simp [h1]

theorem paritySum_dimension (d : Word →₀ ℕ) (p : ℕ) :
    paritySum d p (fun v => d v.val) = d.sum (fun w n => if parity w = p then n else 0) := by
  classical
  exact Finset.sum_coe_sort d.support (fun w => if parity w = p then d w else 0)

def positiveSourceVertex (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (i : PositiveSource R.toRepresentation) : SupportVertex d :=
  ⟨i.val.val,Finsupp.mem_support_iff.mpr (by rw [← hs i.val]; exact Nat.ne_of_gt i.property)⟩

def positiveSinkVertex (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    (j : PositiveSink R.toRepresentation) : SupportVertex d :=
  ⟨j.val.val,Finsupp.mem_support_iff.mpr (by rw [← ht j.val]; exact Nat.ne_of_gt j.property)⟩

theorem sum_positive_sources (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    [Fintype (PositiveSource R.toRepresentation)] (f : SupportVertex d → ℕ) :
    (∑ i, f (positiveSourceVertex R d hs i)) = paritySum d 0 f := by
  classical
  apply Fintype.sum_of_injective (positiveSourceVertex R d hs)
    (fun i j h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun v : SupportVertex d => v.val) h)
  · intro v hv
    by_cases hp : parity v.val = 0
    · exfalso
      apply hv
      refine ⟨⟨⟨v.val,hp⟩, ?_⟩, rfl⟩
      rw [hs]
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp v.property)
    · simp [hp]
  · intro i
    simp [positiveSourceVertex, i.val.property]

theorem sum_positive_sinks (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    [Fintype (PositiveSink R.toRepresentation)] (f : SupportVertex d → ℕ) :
    (∑ j, f (positiveSinkVertex R d ht j)) = paritySum d 1 f := by
  classical
  apply Fintype.sum_of_injective (positiveSinkVertex R d ht)
    (fun i j h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun v : SupportVertex d => v.val) h)
  · intro v hv
    by_cases hp : parity v.val = 1
    · exfalso
      apply hv
      refine ⟨⟨⟨v.val,hp⟩, ?_⟩, rfl⟩
      rw [ht]
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp v.property)
    · simp [hp]
  · intro i
    simp [positiveSinkVertex, i.val.property]

theorem pull_source_size (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    [Fintype (PositiveSource R.toRepresentation)]
    (U : KroneckerFiniteQuiverHom.Subrep (toCoordinates R d hs ht)) :
    KroneckerBipartiteSubrepresentationRestriction.supportSourceSize (pullSubrep R d hs ht U) =
      paritySum d 0 (fun v => finrank ℂ (U.space v)) := by
  classical
  calc
    _ = ∑ i, finrank ℂ (U.space (positiveSourceVertex R d hs i)) :=
      Finset.sum_congr rfl (fun i _ => pull_source_finrank R d hs ht U i.val _)
    _ = _ := sum_positive_sources R d hs (fun v => finrank ℂ (U.space v))

theorem pull_sink_size (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    [Fintype (PositiveSink R.toRepresentation)]
    (U : KroneckerFiniteQuiverHom.Subrep (toCoordinates R d hs ht)) :
    KroneckerBipartiteSubrepresentationRestriction.supportSinkSize (pullSubrep R d hs ht U) =
      paritySum d 1 (fun v => finrank ℂ (U.space v)) := by
  classical
  calc
    _ = ∑ i, finrank ℂ (U.space (positiveSinkVertex R d ht i)) :=
      Finset.sum_congr rfl (fun i _ => pull_sink_finrank R d hs ht U i.val _)
    _ = _ := sum_positive_sinks R d ht (fun v => finrank ℂ (U.space v))

theorem restricted_source_total (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    [Fintype (PositiveSource R.toRepresentation)] :
    KroneckerBipartiteSubrepresentationRestriction.sourceDimension (restriction R.toRepresentation) =
      d.sum (fun w n => if parity w = 0 then n else 0) := by
  classical
  rw [← paritySum_dimension]
  calc
    _ = ∑ i, d (positiveSourceVertex R d hs i).val :=
      Finset.sum_congr rfl (fun i _ => hs i.val)
    _ = _ := sum_positive_sources R d hs (fun v => d v.val)

theorem restricted_sink_total (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    [Fintype (PositiveSink R.toRepresentation)] :
    KroneckerBipartiteSubrepresentationRestriction.sinkDimension (restriction R.toRepresentation) =
      d.sum (fun w n => if parity w = 1 then n else 0) := by
  classical
  rw [← paritySum_dimension]
  calc
    _ = ∑ i, d (positiveSinkVertex R d ht i).val :=
      Finset.sum_congr rfl (fun i _ => ht i.val)
    _ = _ := sum_positive_sinks R d ht (fun v => d v.val)

end KroneckerGlobalCoverCoordinates
end

/- Original module: KroneckerGlobalCoverKingBridge -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KroneckerGlobalCoverCoordinates
open Module KroneckerReducedColorWords KroneckerWordParity
open KroneckerCoverSupportRadius KroneckerStableCoverIndexFinite
open KroneckerPositiveSupportRestriction
open scoped BigOperators

/-- The exact finite vertex weight agrees with the source/sink King numerator. -/
theorem coordinate_king_weight_sum (d : Word →₀ ℕ) (f : SupportVertex d → ℕ) :
    (∑ v, coverKingWeight d v * (f v : ℤ)) =
      (d.sum (fun w n => if parity w = 1 then n else 0) : ℤ) * paritySum d 0 f -
      (d.sum (fun w n => if parity w = 0 then n else 0) : ℤ) * paritySum d 1 f := by
  classical
  simp only [paritySum, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hp : parity v.val < 2 := Nat.mod_lt _ (by decide)
  by_cases h : parity v.val = 0
  · simp [coverKingWeight, h]
  · have h1 : parity v.val = 1 := by omega
    simp [coverKingWeight, h1]

/-- The full representation has zero King weight, without an additional assumption. -/
theorem coordinate_full_king_weight_zero (d : Word →₀ ℕ) :
    (∑ v : SupportVertex d, coverKingWeight d v * (d v.val : ℤ)) = 0 := by
  rw [coordinate_king_weight_sum, paritySum_dimension, paritySum_dimension]
  simp only [Finsupp.sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  ring

/-- Global support stability implies stability of the constructed exact finite
coordinate representation. Every coordinate subrepresentation is pulled back. -/
theorem global_support_stable_coordinates (R : GlobalRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ i, finrank ℂ (R.SourceSpace i) = d i.val)
    (ht : ∀ j, finrank ℂ (R.SinkSpace j) = d j.val)
    [Fintype (PositiveSource R.toRepresentation)] [Fintype (PositiveSink R.toRepresentation)]
    (hR : KroneckerBipartiteSubrepresentationRestriction.SupportKingStable R.toRepresentation) :
    KroneckerFiniteQuiverHom.Stable (coverKingWeight d) (toCoordinates R d hs ht) := by
  classical
  refine ⟨coordinate_full_king_weight_zero d, ?_⟩
  intro U hn hp
  have hsize :
      KroneckerBipartiteSubrepresentationRestriction.supportSourceSize (pullSubrep R d hs ht U) +
      KroneckerBipartiteSubrepresentationRestriction.supportSinkSize (pullSubrep R d hs ht U) =
      KroneckerFiniteQuiverHom.size U := by
    rw [pull_source_size, pull_sink_size]
    exact paritySum_split d (fun v => finrank ℂ (U.space v))
  have htotal :
      KroneckerBipartiteSubrepresentationRestriction.sourceDimension (restriction R.toRepresentation) +
      KroneckerBipartiteSubrepresentationRestriction.sinkDimension (restriction R.toRepresentation) =
      ∑ v : SupportVertex d, d v.val := by
    rw [restricted_source_total R d hs, restricted_sink_total R d ht,
      ← paritySum_dimension, ← paritySum_dimension]
    exact paritySum_split d (fun v => d v.val)
  have hk := hR (pullSubrep R d hs ht U) (by simpa only [hsize] using hn)
    (by simpa only [hsize, htotal] using hp)
  rw [restricted_source_total R d hs, restricted_sink_total R d ht,
    pull_source_size, pull_sink_size] at hk
  change (∑ v, coverKingWeight d v * (finrank ℂ (U.space v) : ℤ)) < 0
  rw [coordinate_king_weight_sum, sub_lt_zero]
  exact_mod_cast hk

end KroneckerGlobalCoverCoordinates
end
