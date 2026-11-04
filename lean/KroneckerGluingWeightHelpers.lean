import KroneckerManuscriptGluingStability

/-! Explicit constituent weights, boundary weights and block-side cut subrepresentations.
The actual manuscript model is related to these vertexwise subspaces by `group` and
`flatten`, which preserve both total dimensions and arbitrary nonzero attachments. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module SimpleGraph
open KroneckerLinearCoverBlocks KroneckerGluedSubrepresentations
open KroneckerPositiveGluingWeight KroneckerPositiveGluedStability
open KroneckerFlowBoundaryIdentity KroneckerBipartiteIncidence
open KroneckerTreeCutComponents KroneckerCutGluedSubobjects
open KroneckerGluedCutStability KroneckerTreeCutFlow KroneckerGluingKingWeight
namespace KroneckerGluingWeightHelpers

lemma block_sink_bound {B : LinearCoverBlock} (W : BlockSubrep B) :
    sinkSize W ≤ Fintype.card B.Sink := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun t _ => (W.sink t).finrank_le)
  simpa [sinkSize] using h

lemma block_eq_full_of_dimensions {B : LinearCoverBlock} (W : BlockSubrep B)
    (hu : sourceSize W = sourceDimension B)
    (ht : sinkSize W = Fintype.card B.Sink) : W = fullBlock B := by
  have hs : ∀ s ∈ (Finset.univ : Finset B.Source),
      finrank ℂ (W.source s) = finrank ℂ (B.Space s) :=
    (Finset.sum_eq_sum_iff_of_le (fun s _ => (W.source s).finrank_le)).mp hu
  have ht' : (∑ t, finrank ℂ (W.sink t)) = ∑ _ : B.Sink, finrank ℂ ℂ := by
    simpa [sinkSize] using ht
  have hk : ∀ t ∈ (Finset.univ : Finset B.Sink),
      finrank ℂ (W.sink t) = finrank ℂ ℂ :=
    (Finset.sum_eq_sum_iff_of_le (fun t _ => (W.sink t).finrank_le)).mp ht'
  apply KroneckerGluedSubrepEquivalence.block_subrep_ext
  · funext s
    exact Submodule.eq_top_of_finrank_eq (hs s (Finset.mem_univ s))
  · funext t
    exact Submodule.eq_top_of_finrank_eq (hk t (Finset.mem_univ t))

/-- The first helper's inequality for an actual nonzero block subrepresentation. -/
theorem zero_sum_weight_lower {B : LinearCoverBlock} (hdef : PositiveDefect B)
    (W : BlockSubrep B) (hW : 0 < sourceSize W + sinkSize W)
    (y : ℝ) (hy : 0 ≤ y) :
    y - (sourceDimension B : ℝ) ≤ blockWeight y (sourceSize W) (sinkSize W) :=
  block_weight_lower y _ _ _ hy (hdef W hW) (block_source_bound W)

/-- Equality in the constituent weight bound is equivalent to equality of every
vertex subspace with the ambient space; this includes source dimension zero. -/
theorem zero_sum_weight_eq_iff_full {B : LinearCoverBlock} (hdef : PositiveDefect B)
    (hdim : Fintype.card B.Sink = sourceDimension B + 1)
    (W : BlockSubrep B) (hW : 0 < sourceSize W + sinkSize W)
    (y : ℝ) (hy : 0 ≤ y) :
    blockWeight y (sourceSize W) (sinkSize W) = y - (sourceDimension B : ℝ) ↔
      W = fullBlock B := by
  constructor
  · intro he
    have hu : sourceSize W = sourceDimension B := by
      apply Nat.le_antisymm (block_source_bound W)
      by_contra h
      have hs := block_weight_strict y (sourceSize W) (sinkSize W)
        (sourceDimension B) hy (hdef W hW) (by omega)
      linarith
    have ht : sinkSize W = Fintype.card B.Sink := by
      have hd := hdef W hW
      have hb := block_sink_bound W
      omega
    exact block_eq_full_of_dimensions W hu ht
  · rintro rfl
    rw [(full_block_dimensions B).1, (full_block_dimensions B).2, hdim]
    simp [blockWeight]

variable {I J : Type} [Fintype I] [Fintype J]
variable {B : J → LinearCoverBlock} {R : I → J → Prop}
variable {attach : ∀ i j, R i j → (B j).Sink}

/-- Lemma 7.29: the row and column flow equations imply total balance. -/
theorem flow_equations_balance (f : I → J → ℝ) (x : ℝ)
    (hrow : ∀ i, ∑ j, f i j = x + 1)
    (hcol : ∀ j, ∑ i, f i j = x - sourceDimension (B j)) :
    (∑ j, (x - (sourceDimension (B j) : ℝ))) = ∑ _ : I, (x + 1) := by
  calc
    (∑ j, (x - (sourceDimension (B j) : ℝ))) = ∑ j, ∑ i, f i j :=
      Finset.sum_congr rfl (fun j _ => (hcol j).symm)
    _ = ∑ i, ∑ j, f i j := Finset.sum_comm
    _ = ∑ _ : I, (x + 1) := Finset.sum_congr rfl (fun i _ => hrow i)

/-- Summing the two flow equations cancels exactly the edges whose connector is chosen. -/
theorem boundary_flow (W : GluedSubrep B R attach) (f : I → J → ℝ)
    (hoff : ∀ i j, ¬ R i j → f i j = 0) (x : ℝ)
    (hrow : ∀ i, ∑ j, f i j = x + 1)
    (hcol : ∀ j, ∑ i, f i j = x - sourceDimension (B j)) :
    (∑ j ∈ occupiedBlocks W, (x - (sourceDimension (B j) : ℝ))) -
      (x + 1) * ((chosenConnectors W).card : ℝ) =
      boundaryFlux f (chosenConnectors W) (occupiedBlocks W) := by
  have hc : ∀ i ∈ chosenConnectors W, ∀ j ∉ occupiedBlocks W, f i j = 0 := by
    intro i hi j hj
    exact hoff i j (fun hij => hj (attachment_forces_occupied W hi hij))
  simpa [hrow, hcol, mul_comm, mul_add] using
    boundary_demand_difference f (chosenConnectors W) (occupiedBlocks W) hc

/-- Exact normalized weight: boundary flow plus the indexed constituent defects. -/
theorem glued_weight_boundary_formula (W : GluedSubrep B R attach) (f : I → J → ℝ)
    (hoff : ∀ i j, ¬ R i j → f i j = 0) (x : ℝ)
    (hrow : ∀ i, ∑ j, f i j = x + 1)
    (hcol : ∀ j, ∑ i, f i j = x - sourceDimension (B j)) :
    gluedWeight x W = boundaryFlux f (chosenConnectors W) (occupiedBlocks W) +
      ∑ j ∈ occupiedBlocks W,
        (x * ((sinkSize (W.block j) : ℝ) - (sourceSize (W.block j) : ℝ) - 1) +
          ((sourceDimension (B j) : ℝ) - (sourceSize (W.block j) : ℝ))) := by
  rw [← boundary_flow W f hoff x hrow hcol, glued_weight_decomposition]
  have hs : (∑ j, blockWeight x (sourceSize (W.block j)) (sinkSize (W.block j))) =
      ∑ j ∈ occupiedBlocks W, blockWeight x (sourceSize (W.block j)) (sinkSize (W.block j)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    simp [blockWeight, (empty_block_dimensions W j hj).1, (empty_block_dimensions W j hj).2]
  rw [hs]
  have he : ∀ j, blockWeight x (sourceSize (W.block j)) (sinkSize (W.block j)) =
      (x - (sourceDimension (B j) : ℝ)) +
      (x * ((sinkSize (W.block j) : ℝ) - (sourceSize (W.block j) : ℝ) - 1) +
        ((sourceDimension (B j) : ℝ) - (sourceSize (W.block j) : ℝ))) := by
    intro j
    dsimp [blockWeight]
    ring
  simp_rw [he, Finset.sum_add_distrib]
  ring

/-- Full spaces on the block-side component, zero spaces on its complement. -/
def cutSubrep (hT : (incidenceGraph R).IsTree) {v : I} {i : J} (hw : R v i) :
    GluedSubrep B R attach :=
  closedSubrep B R attach (cutConnectors R v i) (cutBlocks R v i)
    (fun _ hy _ he => cut_is_connector_closed hT hw hy he)

theorem cut_subrep_dimensions (hT : (incidenceGraph R).IsTree)
    (hdim : ∀ j, Fintype.card (B j).Sink = sourceDimension (B j) + 1)
    {v : I} {i : J} (hw : R v i) :
    gluedSourceSize (cutSubrep (B := B) (attach := attach) hT hw) =
      (∑ j ∈ cutBlocks R v i, sourceDimension (B j)) + (cutConnectors R v i).card ∧
    gluedSinkSize (cutSubrep (B := B) (attach := attach) hT hw) =
      ∑ j ∈ cutBlocks R v i, (sourceDimension (B j) + 1) := by
  simpa only [cutSubrep, hdim] using closed_subrep_dimensions B R attach
    (cutConnectors R v i) (cutBlocks R v i)
    (fun _ hy _ he => cut_is_connector_closed hT hw hy he)

theorem cut_subrep_nonzero_proper (hT : (incidenceGraph R).IsTree)
    (hdim : ∀ j, Fintype.card (B j).Sink = sourceDimension (B j) + 1)
    {v : I} {i : J} (hw : R v i) :
    0 < gluedSourceSize (cutSubrep (B := B) (attach := attach) hT hw) +
      gluedSinkSize (cutSubrep (B := B) (attach := attach) hT hw) ∧
    gluedSourceSize (cutSubrep (B := B) (attach := attach) hT hw) +
      gluedSinkSize (cutSubrep (B := B) (attach := attach) hT hw) <
      totalSource (I := I) B + totalSink B := by
  have hv : v ∉ cutConnectors R v i := cut_connector_excluded hT hw
  have hc : (cutConnectors R v i).card < Fintype.card I := by
    have hlt : cutConnectors R v i ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun he => hv (by simp [he])⟩
    simpa using Finset.card_lt_card hlt
  constructor
  · exact closed_subrep_nonzero B R attach _ _ _ hdim ⟨i, cut_block_included R v i⟩
  · exact closed_subrep_proper B R attach _ _ _ hc

theorem cut_subrep_weight (hT : (incidenceGraph R).IsTree)
    (hdim : ∀ j, Fintype.card (B j).Sink = sourceDimension (B j) + 1)
    (f : I → J → ℝ) (hoff : ∀ i j, ¬ R i j → f i j = 0) (x : ℝ)
    (hrow : ∀ i, ∑ j, f i j = x + 1)
    (hcol : ∀ j, ∑ i, f i j = x - sourceDimension (B j))
    {v : I} {i : J} (hw : R v i) :
    gluedWeight x (cutSubrep (B := B) (attach := attach) hT hw) = f v i := by
  rw [cutSubrep, closed_subrep_weight B R attach _ _ _ hdim]
  exact cut_demand_equals_flow hT f hoff x (fun j => sourceDimension (B j)) hrow hcol hw

open KroneckerManuscriptQuiverDefinitions

/-- The exact displayed weight formula for the manuscript representation, with its
actual nonzero attachment maps, rather than an assumed numerical dimension vector. -/
theorem manuscript_weight_formula (D : ZeroSumGlueData)
    (hdim : ∀ j, Fintype.card (D.blocks j).Sink = sourceDimension (D.blocks j) + 1)
    (W : D.Glue.SubRep) (f : D.S.Source → D.S.Sink → ℝ)
    (hoff : ∀ v i, ¬ D.S.incidence v i → f v i = 0)
    (hrow : ∀ v, ∑ i, f v i = slopeParameter (I := D.S.Source) D.blocks + 1)
    (hcol : ∀ i, ∑ v, f v i = slopeParameter (I := D.S.Source) D.blocks - sourceDimension (D.blocks i)) :
    ((D.FullSrcDim : ℝ) * (D.SnkDim W : ℝ) -
      ((D.FullSrcDim : ℝ) + ((Fintype.card D.S.Source : ℝ) + 1)) * (D.SrcDim W : ℝ)) /
      ((Fintype.card D.S.Source : ℝ) + 1) =
      boundaryFlux f (chosenConnectors (D.group W)) (occupiedBlocks (D.group W)) +
      ∑ i ∈ occupiedBlocks (D.group W),
        (slopeParameter (I := D.S.Source) D.blocks *
          ((sinkSize ((D.group W).block i) : ℝ) - (sourceSize ((D.group W).block i) : ℝ) - 1) +
          ((sourceDimension (D.blocks i) : ℝ) - (sourceSize ((D.group W).block i) : ℝ))) := by
  have he := king_weight_identity D.blocks D.S.incidence D.attach
    (glued_total_dimension D.blocks D.S.incidence D.S.tree D.source_degree_card hdim) (D.group W)
  rw [D.group_source_dimension, D.group_sink_dimension,
    ← D.full_source_dimension, ← D.full_sink_dimension, D.total_dimension_pair hdim] at he
  rw [glued_weight_boundary_formula (D.group W) f hoff _ hrow hcol] at he
  have hk : (Fintype.card D.S.Source : ℝ) + 1 ≠ 0 := by positivity
  apply (div_eq_iff hk).mpr
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using he.symm

/-- The cut object in the actual glued quiver; no arbitrary choice of subspaces. -/
def manuscriptCutSubrep (D : ZeroSumGlueData) {v : D.S.Source} {i : D.S.Sink}
    (hw : D.S.incidence v i) : D.Glue.SubRep :=
  D.flatten (cutSubrep (B := D.blocks) (attach := D.attach) D.S.tree hw)

lemma group_manuscript_cut (D : ZeroSumGlueData) {v : D.S.Source} {i : D.S.Sink}
    (hw : D.S.incidence v i) :
    D.group (manuscriptCutSubrep D hw) =
      cutSubrep (B := D.blocks) (attach := D.attach) D.S.tree hw :=
  D.subrepEquiv.apply_symm_apply _

theorem manuscript_cut_dimensions (D : ZeroSumGlueData)
    (hdim : ∀ j, Fintype.card (D.blocks j).Sink = sourceDimension (D.blocks j) + 1)
    {v : D.S.Source} {i : D.S.Sink} (hw : D.S.incidence v i) :
    D.SrcDim (manuscriptCutSubrep D hw) =
      (∑ j ∈ cutBlocks D.S.incidence v i, sourceDimension (D.blocks j)) +
        (cutConnectors D.S.incidence v i).card ∧
    D.SnkDim (manuscriptCutSubrep D hw) =
      ∑ j ∈ cutBlocks D.S.incidence v i, (sourceDimension (D.blocks j) + 1) := by
  rw [← D.group_source_dimension, ← D.group_sink_dimension, group_manuscript_cut]
  exact cut_subrep_dimensions D.S.tree hdim hw

theorem manuscript_cut_nonzero_proper (D : ZeroSumGlueData)
    (hdim : ∀ j, Fintype.card (D.blocks j).Sink = sourceDimension (D.blocks j) + 1)
    {v : D.S.Source} {i : D.S.Sink} (hw : D.S.incidence v i) :
    0 < D.SrcDim (manuscriptCutSubrep D hw) + D.SnkDim (manuscriptCutSubrep D hw) ∧
    D.SrcDim (manuscriptCutSubrep D hw) + D.SnkDim (manuscriptCutSubrep D hw) <
      D.FullSrcDim + D.FullSnkDim := by
  rw [← D.group_source_dimension, ← D.group_sink_dimension, group_manuscript_cut,
    D.full_source_dimension, D.full_sink_dimension]
  exact cut_subrep_nonzero_proper D.S.tree hdim hw

theorem manuscript_cut_weight (D : ZeroSumGlueData)
    (hdim : ∀ j, Fintype.card (D.blocks j).Sink = sourceDimension (D.blocks j) + 1)
    (f : D.S.Source → D.S.Sink → ℝ)
    (hoff : ∀ v i, ¬ D.S.incidence v i → f v i = 0)
    (hrow : ∀ v, ∑ i, f v i = slopeParameter (I := D.S.Source) D.blocks + 1)
    (hcol : ∀ i, ∑ v, f v i = slopeParameter (I := D.S.Source) D.blocks - sourceDimension (D.blocks i))
    {v : D.S.Source} {i : D.S.Sink} (hw : D.S.incidence v i) :
    (D.FullSrcDim : ℝ) * (D.SnkDim (manuscriptCutSubrep D hw) : ℝ) -
      ((D.FullSrcDim : ℝ) + ((Fintype.card D.S.Source : ℝ) + 1)) *
        (D.SrcDim (manuscriptCutSubrep D hw) : ℝ) =
      ((Fintype.card D.S.Source : ℝ) + 1) * f v i := by
  have he := king_weight_identity D.blocks D.S.incidence D.attach
    (glued_total_dimension D.blocks D.S.incidence D.S.tree D.source_degree_card hdim)
      (D.group (manuscriptCutSubrep D hw))
  rw [D.group_source_dimension, D.group_sink_dimension,
    ← D.full_source_dimension, ← D.full_sink_dimension, D.total_dimension_pair hdim,
    group_manuscript_cut, cut_subrep_weight D.S.tree hdim f hoff _ hrow hcol hw] at he
  simpa only [Nat.cast_add, Nat.cast_one] using he.symm

end KroneckerGluingWeightHelpers
