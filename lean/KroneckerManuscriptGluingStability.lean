import KroneckerManuscriptArrowOperators
import KroneckerRetainedSubrepresentations

noncomputable section
open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions
open KroneckerLinearCoverBlocks KroneckerRetainedReflectionKernels
open KroneckerGluedSubrepresentations KroneckerPositiveGluedStability
open KroneckerGluingKingWeight

lemma nonzero_complex_map_mem (f : ℂ →ₗ[ℂ] ℂ) (hf : f ≠ 0)
    (U : Submodule ℂ ℂ) (x : ℂ) : f x ∈ U ↔ x ∈ U := by
  have he (z : ℂ) : f z = f 1 • z := by
    simpa [smul_eq_mul, mul_comm] using f.map_smul z (1 : ℂ)
  have hn : f 1 ≠ 0 := by
    intro h
    apply hf
    apply LinearMap.ext
    intro z
    change f z = 0
    rw [he, h, zero_smul]
  rw [he]
  exact U.smul_mem_iff hn

namespace ZeroSumGlueData
variable (D : ZeroSumGlueData)
abbrev blocks (b : D.S.Sink) := retainedBlock (D.T b).incidence
abbrev Edge := D.toGlueData.NewArrow
lemma vertex_is_sink (e : D.Edge) : ∃ t : (D.T e.val.2).Source, D.vertex e = Sum.inr t := by
  have h := (D.vacant e).1
  obtain ⟨t,ht⟩ := h
  exact ⟨t,ht.symm⟩

def sink (e : D.Edge) : (D.T e.val.2).Source := Classical.choose (D.vertex_is_sink e)
lemma vertex_eq (e : D.Edge) : D.vertex e = Sum.inr (D.sink e) :=
  Classical.choose_spec (D.vertex_is_sink e)
def attach (i : D.S.Source) (b : D.S.Sink) (h : D.S.incidence i b) : (D.blocks b).Sink :=
  D.sink ⟨(i,b),h⟩

/-- The old identity-arrow condition and the actual nonzero-arrow condition coincide. -/
lemma added_invariant_iff (e : D.Edge)
    (U : ∀ v, Submodule ℂ (D.Glue.Space v)) (x : ℂ) :
    D.Glue.arrow (.inr e) x ∈ U (.inr ⟨e.val.2,D.vertex e⟩) ↔
      x ∈ U (.inr ⟨e.val.2,Sum.inr (D.sink e)⟩) := by
  change D.map e x ∈ U (.inr ⟨e.val.2,D.vertex e⟩) ↔ _
  have aux (v : (D.T e.val.2).Q.1.Vert) (hv : v = Sum.inr (D.sink e))
      (f : ℂ →ₗ[ℂ] (D.T e.val.2).ZS.Space v) (hn : f ≠ 0) :
      f x ∈ U (.inr ⟨e.val.2,v⟩) ↔ x ∈ U (.inr ⟨e.val.2,Sum.inr (D.sink e)⟩) := by
    subst v
    exact nonzero_complex_map_mem f hn _ x
  exact aux _ (D.vertex_eq e) (D.map e) (D.nonzero e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of an actual manuscript subrepresentation to each old block. -/
def group (W : D.Glue.SubRep) : GluedSubrep D.blocks D.S.incidence D.attach where
  block b := {
    source := fun s => W.space (.inr ⟨b,Sum.inl s⟩)
    sink := fun t => W.space (.inr ⟨b,Sum.inr t⟩)
    invariant := by
      intro s t x hx
      by_cases h : (D.T b).incidence t s.val
      · have hw := W.invariant (.inl ⟨b,⟨(s,t),h⟩⟩) x hx
        change KroneckerReflectionKernel.projection ⟨t,h⟩ x ∈
          W.space (.inr ⟨b,Sum.inr t⟩) at hw
        simpa only [blocks, retainedBlock, dite_eq_left h] using hw
      · simp [h] }
  connector i := W.space (.inl i)
  attachment := by
    intro i b h x hx
    exact (D.added_invariant_iff ⟨(i,b),h⟩ W.space x).mp (W.invariant (.inr ⟨(i,b),h⟩) x hx)

def flatSpace (W : GluedSubrep D.blocks D.S.incidence D.attach)
    (v : D.toGlueData.quiver.1.Vert) : Submodule ℂ (D.Glue.Space v) :=
  match v with
  | .inl i => W.connector i
  | .inr ⟨b,.inl j⟩ => (W.block b).source j
  | .inr ⟨b,.inr t⟩ => (W.block b).sink t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def flatten (W : GluedSubrep D.blocks D.S.incidence D.attach) : D.Glue.SubRep where
  space := D.flatSpace W
  invariant := by
    intro a x hx
    cases a with
    | inl a =>
      obtain ⟨b,⟨⟨j,t⟩,h⟩⟩ := a
      have hw := (W.block b).invariant j t x hx
      change KroneckerReflectionKernel.projection ⟨t,h⟩ x ∈ (W.block b).sink t
      simpa only [blocks, retainedBlock, dite_eq_left h] using hw
    | inr e =>
      apply (D.added_invariant_iff e (D.flatSpace W) x).mpr
      exact W.attachment e.val.1 e.val.2 e.property x hx

@[ext] lemma subrep_ext {W Z : D.Glue.SubRep} (h : ∀ v, W.space v = Z.space v) : W = Z := by
  cases W; cases Z
  congr
  exact funext h

def subrepEquiv : D.Glue.SubRep ≃ GluedSubrep D.blocks D.S.incidence D.attach where
  toFun := D.group
  invFun := D.flatten
  left_inv W := by
    apply D.subrep_ext
    intro v
    cases v with
    | inl i => rfl
    | inr p => obtain ⟨b,v⟩ := p; cases v <;> rfl
  right_inv W := by
    apply KroneckerGluedSubrepEquivalence.glued_subrep_ext
    · funext b
      exact KroneckerGluedSubrepEquivalence.block_subrep_ext rfl rfl
    · rfl

/-- Sum of dimensions at the actual source vertices of the manuscript quiver. -/
def SrcDim (W : D.Glue.SubRep) : ℕ :=
  (∑ i, Module.finrank ℂ (W.space (.inl i))) +
  ∑ b, ∑ j : (D.T b).InternalSink, Module.finrank ℂ (W.space (.inr ⟨b,.inl j⟩))
/-- Sum of dimensions at the actual sink vertices of the manuscript quiver. -/
def SnkDim (W : D.Glue.SubRep) : ℕ :=
  ∑ b, ∑ t : (D.T b).Source, Module.finrank ℂ (W.space (.inr ⟨b,.inr t⟩))

theorem group_source_dimension (W : D.Glue.SubRep) :
    gluedSourceSize (D.group W) = D.SrcDim W := by
  rw [gluedSourceSize, ← connector_dimension_sum]
  exact Nat.add_comm _ _
theorem group_sink_dimension (W : D.Glue.SubRep) :
    gluedSinkSize (D.group W) = D.SnkDim W := rfl

def FullSrcDim : ℕ :=
  (∑ i : D.S.Source, Module.finrank ℂ (D.Glue.Space (.inl i))) +
  ∑ b, ∑ j : (D.T b).InternalSink, Module.finrank ℂ (D.Glue.Space (.inr ⟨b,.inl j⟩))
def FullSnkDim : ℕ :=
  ∑ b, ∑ t : (D.T b).Source, Module.finrank ℂ (D.Glue.Space (.inr ⟨b,.inr t⟩))
theorem full_source_dimension : D.FullSrcDim = totalSource (I := D.S.Source) D.blocks := by
  change (∑ _ : D.S.Source, Module.finrank ℂ ℂ) +
    (∑ b, sourceDimension (D.blocks b)) = _
  simp [totalSource, Nat.add_comm]
theorem full_sink_dimension : D.FullSnkDim = totalSink D.blocks := by
  change (∑ b, ∑ _ : (D.T b).Source, Module.finrank ℂ ℂ) = _
  simp [totalSink, blocks, retainedBlock]

/-- King stability, quantified over all actual vertexwise subrepresentations of Glue. -/
def GlueKingStable : Prop := ∀ W : D.Glue.SubRep,
  0 < D.SrcDim W + D.SnkDim W →
  D.SrcDim W + D.SnkDim W < D.FullSrcDim + D.FullSnkDim →
  D.FullSnkDim * D.SrcDim W < D.FullSrcDim * D.SnkDim W

theorem stability_iff_old_model : D.GlueKingStable ↔ KingStable D.blocks D.S.incidence D.attach := by
  unfold GlueKingStable
  rw [D.full_source_dimension, D.full_sink_dimension]
  constructor
  · intro hs W hn hp
    obtain ⟨U,hu⟩ := D.subrepEquiv.surjective W
    change D.group U = W at hu
    subst W
    simpa only [D.group_source_dimension, D.group_sink_dimension] using
      hs U (by simpa only [D.group_source_dimension,D.group_sink_dimension] using hn)
        (by simpa only [D.group_source_dimension,D.group_sink_dimension] using hp)
  · intro hs W hn hp
    simpa only [D.group_source_dimension,D.group_sink_dimension] using
      hs (D.group W) (by simpa only [D.group_source_dimension,D.group_sink_dimension] using hn)
        (by simpa only [D.group_source_dimension,D.group_sink_dimension] using hp)

lemma block_positive_defect (b : D.S.Sink) : PositiveDefect (D.blocks b) := by
  apply (KroneckerRetainedSubrepresentations.retained_defect_iff (D.T b).incidence).mpr
  apply KroneckerReflectedLinearBlock.reflected_positive_defect (D.T b).tree
  intro i
  simpa only [Nat.card_eq_fintype_card] using (D.T b).source_degree i
lemma source_degree_card (i : D.S.Source) : Fintype.card {b // D.S.incidence i b} = 3 := by
  simpa only [Nat.card_eq_fintype_card] using D.S.source_degree i

/-- Stability of the actual Glue representation is equivalent to positivity of a flow
satisfying the manuscript's row and column equations. -/
theorem stability_iff_positive_flow
    (hdim : ∀ b, Fintype.card (D.blocks b).Sink = sourceDimension (D.blocks b) + 1)
    (flow : D.S.Source → D.S.Sink → ℝ)
    (hoff : ∀ i b, ¬ D.S.incidence i b → flow i b = 0)
    (hrow : ∀ i, ∑ b, flow i b = slopeParameter (I := D.S.Source) D.blocks + 1)
    (hcol : ∀ b, ∑ i, flow i b = slopeParameter (I := D.S.Source) D.blocks - sourceDimension (D.blocks b)) :
    D.GlueKingStable ↔ ∀ i b, D.S.incidence i b → 0 < flow i b := by
  rw [D.stability_iff_old_model,
    king_stable_iff_normalized D.blocks D.S.incidence D.attach
      (glued_total_dimension D.blocks D.S.incidence D.S.tree D.source_degree_card hdim)]
  constructor
  · intro hs
    exact KroneckerGluedCutStability.stability_implies_positive_flows
      D.blocks D.S.incidence D.attach D.S.tree hdim flow hoff _ hrow hcol hs
  · intro hp
    apply positive_flows_imply_stability D.blocks D.S.incidence D.attach
      D.S.tree.connected _ D.block_positive_defect hdim flow _ hp hoff _ _ hrow hcol
    · intro i
      have hn : 0 < Fintype.card {b // D.S.incidence i b} := by rw [D.source_degree_card]; omega
      obtain ⟨b,hb⟩ := Fintype.card_pos_iff.mp hn
      exact ⟨b,hb⟩
    · intro i b
      by_cases h : D.S.incidence i b
      · exact le_of_lt (hp i b h)
      · rw [hoff i b h]
    · unfold slopeParameter
      positivity

/-- Composed equivalence to the old flattened linear-block model. -/
def coordinateSubrepEquiv : D.Glue.SubRep ≃
    BlockSubrep (KroneckerGluedLinearRepresentation.gluedBlock D.blocks D.S.incidence D.attach) :=
  D.subrepEquiv.trans (KroneckerGluedSubrepEquivalence.gluedSubrepEquiv D.blocks D.S.incidence D.attach)

theorem stability_iff_coordinate_block : D.GlueKingStable ↔
    KroneckerGluedSubrepEquivalence.BlockKingStable
      (KroneckerGluedLinearRepresentation.gluedBlock D.blocks D.S.incidence D.attach) :=
  D.stability_iff_old_model.trans
    (KroneckerGluedSubrepEquivalence.global_stability_iff D.blocks D.S.incidence D.attach).symm

def edgeFlow (φ : D.Edge → ℝ) (i : D.S.Source) (b : D.S.Sink) : ℝ :=
  if h : D.S.incidence i b then φ ⟨(i,b),h⟩ else 0

/-- The final criterion uses a function on edges, as in the PDF. -/
theorem stability_iff_positive_edge_flow
    (hdim : ∀ b, Fintype.card (D.blocks b).Sink = sourceDimension (D.blocks b) + 1)
    (φ : D.Edge → ℝ)
    (hrow : ∀ i, ∑ b, D.edgeFlow φ i b = slopeParameter (I := D.S.Source) D.blocks + 1)
    (hcol : ∀ b, ∑ i, D.edgeFlow φ i b = slopeParameter (I := D.S.Source) D.blocks - sourceDimension (D.blocks b)) :
    D.GlueKingStable ↔ ∀ e, 0 < φ e := by
  rw [D.stability_iff_positive_flow hdim (D.edgeFlow φ)
    (by intro i b h; simp [edgeFlow,h]) hrow hcol]
  constructor
  · intro h e
    rcases e with ⟨⟨i,b⟩,hib⟩
    have he : D.edgeFlow φ i b = φ ⟨(i,b),hib⟩ := dite_eq_left hib
    rw [← he]
    exact h i b hib
  · intro h i b hib
    rw [show D.edgeFlow φ i b = φ ⟨(i,b),hib⟩ from dite_eq_left hib]
    exact h ⟨(i,b),hib⟩

/-- The slope in the flow equations is the actual total source dimension divided by c+1. -/
theorem slope_matches_manuscript : slopeParameter (I := D.S.Source) D.blocks =
    (D.FullSrcDim : ℝ) / ((Fintype.card D.S.Source : ℝ) + 1) := by
  rw [D.full_source_dimension]
  rfl

theorem total_dimension_pair
    (hdim : ∀ b, Fintype.card (D.blocks b).Sink = sourceDimension (D.blocks b) + 1) :
    D.FullSnkDim = D.FullSrcDim + (Fintype.card D.S.Source + 1) := by
  rw [D.full_source_dimension,D.full_sink_dimension]
  exact glued_total_dimension D.blocks D.S.incidence D.S.tree D.source_degree_card hdim

end ZeroSumGlueData
end KroneckerManuscriptQuiverDefinitions
