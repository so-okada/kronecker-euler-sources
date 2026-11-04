import KroneckerManuscriptFiniteSupportDimensions
import KroneckerManuscriptGluingStability

/-! Positive bipartite King weights, including dimensions (0,1).
The coordinate model uses the negative of the manuscript's weight. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Classical

namespace KroneckerManuscriptBipartiteStability
def positiveWeight (a b u v : ℕ) : ℤ := (a : ℤ)*v-(b : ℤ)*u

theorem positiveWeight_pos_iff (a b u v : ℕ) :
    0 < positiveWeight a b u v ↔ b*u < a*v := by
  unfold positiveWeight
  rw [sub_pos]
  exact_mod_cast (Iff.rfl : b*u < a*v ↔ b*u < a*v)

open KroneckerManuscriptQuiverDefinitions
open KroneckerManuscriptQuiverDefinitions.Representation

theorem subrep_support_subset {Q : Quiver} {R : Representation Q} (W : R.SubRep) :
    (SubRep.toRepresentation W).support ⊆ R.support := by
  intro v hv
  rw [mem_support_iff_dimension_pos] at hv ⊢
  exact lt_of_lt_of_le hv (Submodule.finrank_le (W.space v))

def subrepFiniteSupport {Q : Quiver} {R : Representation Q}
    (hR : R.support.Finite) (W : R.SubRep) : (SubRep.toRepresentation W).support.Finite :=
  hR.subset (subrep_support_subset W)

def weight {Q : Quiver} (B : Q.Bipartition) (a b : ℕ)
    (R : Representation Q) (hR : R.support.Finite) : ℤ :=
  positiveWeight a b (R.finiteSrcDim B hR) (R.finiteSnkDim B hR)

def Stable {Q : Quiver} (B : Q.Bipartition) (R : Representation Q)
    (hR : R.support.Finite) : Prop :=
  0 < R.finiteSrcDim B hR + R.finiteSnkDim B hR ∧
  ∀ W : R.SubRep,
    let hW := subrepFiniteSupport hR W
    0 < (SubRep.toRepresentation W).finiteSrcDim B hW + (SubRep.toRepresentation W).finiteSnkDim B hW →
    (SubRep.toRepresentation W).finiteSrcDim B hW + (SubRep.toRepresentation W).finiteSnkDim B hW <
      R.finiteSrcDim B hR + R.finiteSnkDim B hR →
    0 < weight B (R.finiteSrcDim B hR) (R.finiteSnkDim B hR) (SubRep.toRepresentation W) hW

def negativeVertexWeight {Q : Quiver} (B : Q.Bipartition) (a b : ℕ) (v : Q.Vert) : ℤ :=
  if v ∈ B.sources then (b : ℤ) else -(a : ℤ)

theorem sink_iff_not_source {Q : Quiver} (B : Q.Bipartition) (v : Q.Vert) :
    v ∈ B.sinks ↔ v ∉ B.sources := by
  have he : v ∈ B.sources ∪ B.sinks := B.exhaustive.symm ▸ Set.mem_univ v
  have hd := Set.disjoint_left.mp B.disjoint
  exact ⟨fun hs hi => hd hi hs, fun hi => he.resolve_left hi⟩

theorem part_sum {Q : Quiver} [Fintype Q.Vert] (B : Q.Bipartition) (d : Q.Vert → ℕ) :
    (∑ v, if v ∈ B.sources then d v else 0) +
      (∑ v, if v ∈ B.sinks then d v else 0) = ∑ v, d v := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : v ∈ B.sources <;> simp [h,sink_iff_not_source]

theorem total_dimension_sum {Q : Quiver} [Fintype Q.Vert] (B : Q.Bipartition)
    (R : Representation Q) : R.SrcDim B + R.SnkDim B = ∑ v, R.dimension v :=
  part_sum B R.dimension

theorem negative_weight_sum {Q : Quiver} [Fintype Q.Vert] (B : Q.Bipartition)
    (a b : ℕ) (d : Q.Vert → ℕ) :
    (∑ v, negativeVertexWeight B a b v * (d v : ℤ)) =
      -positiveWeight a b (∑ v, if v ∈ B.sources then d v else 0)
        (∑ v, if v ∈ B.sinks then d v else 0) := by
  unfold positiveWeight
  rw [neg_sub, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum, ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : v ∈ B.sources <;> simp [negativeVertexWeight,h,sink_iff_not_source]

theorem weightOn_eq {Q : Quiver} [Fintype Q.Vert] (B : Q.Bipartition)
    (a b : ℕ) {R : Representation Q} (W : R.SubRep) :
    KroneckerFiniteQuiverHom.weightOn (negativeVertexWeight B a b) W =
      -positiveWeight a b ((SubRep.toRepresentation W).SrcDim B) ((SubRep.toRepresentation W).SnkDim B) :=
  negative_weight_sum B a b (fun v => Module.finrank ℂ (W.space v))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem stable_iff_coordinate {Q : Quiver} [Fintype Q.Vert] (B : Q.Bipartition)
    (R : Representation Q) (hR : R.support.Finite) :
    Stable B R hR ↔ 0 < R.SrcDim B + R.SnkDim B ∧
      KroneckerFiniteQuiverHom.Stable (negativeVertexWeight B (R.SrcDim B) (R.SnkDim B)) R.toCoordinates := by
  have hw : (∑ v, negativeVertexWeight B (R.SrcDim B) (R.SnkDim B) v *
      (Module.finrank ℂ (R.Space v) : ℤ)) = 0 := by
    have h := negative_weight_sum B (R.SrcDim B) (R.SnkDim B) R.dimension
    change _ = -positiveWeight (R.SrcDim B) (R.SnkDim B) (R.SrcDim B) (R.SnkDim B) at h
    have hz : positiveWeight (R.SrcDim B) (R.SnkDim B) (R.SrcDim B) (R.SnkDim B) = 0 := by
      unfold positiveWeight; ring
    simpa only [dimension,hz,neg_zero] using h
  change Stable B R hR ↔ _ ∧ KroneckerFiniteQuiverHom.Stable _
    (KroneckerFiniteQuiverHom.inCoordinates R.coordinates R.toRepresentationOn)
  rw [KroneckerFiniteQuiverHom.coordinate_stability_iff]
  unfold Stable weight
  simp only [finiteSrcDim_eq,finiteSnkDim_eq]
  constructor
  · rintro ⟨hn,h⟩
    refine ⟨hn,hw,?_⟩
    intro W hW hp
    have hn' : 0 < (SubRep.toRepresentation W).SrcDim B + (SubRep.toRepresentation W).SnkDim B := by
      simpa only [total_dimension_sum,dimension,SubRep.toRepresentation,
        KroneckerFiniteQuiverHom.sizeOn] using hW
    have hp' : (SubRep.toRepresentation W).SrcDim B + (SubRep.toRepresentation W).SnkDim B < R.SrcDim B + R.SnkDim B := by
      simpa only [total_dimension_sum,dimension,SubRep.toRepresentation,
        KroneckerFiniteQuiverHom.sizeOn] using hp
    rw [weightOn_eq]
    exact neg_neg_of_pos (h W hn' hp')
  · rintro ⟨hn,h⟩
    refine ⟨hn,?_⟩
    intro W hW hp
    have hn' : 0 < KroneckerFiniteQuiverHom.sizeOn W := by
      simpa only [total_dimension_sum,dimension,SubRep.toRepresentation,
        KroneckerFiniteQuiverHom.sizeOn] using hW
    have hp' : KroneckerFiniteQuiverHom.sizeOn W < ∑ v, Module.finrank ℂ (R.Space v) := by
      simpa only [total_dimension_sum,dimension,SubRep.toRepresentation,
        KroneckerFiniteQuiverHom.sizeOn] using hp
    have hh := h.2 W hn' hp'
    rw [weightOn_eq] at hh
    exact neg_neg_iff_pos.mp hh

theorem block_stability_weight_iff (B : KroneckerLinearCoverBlocks.LinearCoverBlock) :
    KroneckerGluedSubrepEquivalence.BlockKingStable B ↔
      ∀ W : KroneckerLinearCoverBlocks.BlockSubrep B,
        0 < KroneckerLinearCoverBlocks.sourceSize W + KroneckerLinearCoverBlocks.sinkSize W →
        KroneckerLinearCoverBlocks.sourceSize W + KroneckerLinearCoverBlocks.sinkSize W <
          KroneckerLinearCoverBlocks.sourceDimension B + Fintype.card B.Sink →
        0 < positiveWeight (KroneckerLinearCoverBlocks.sourceDimension B) (Fintype.card B.Sink)
          (KroneckerLinearCoverBlocks.sourceSize W) (KroneckerLinearCoverBlocks.sinkSize W) := by
  simp only [KroneckerGluedSubrepEquivalence.BlockKingStable,positiveWeight_pos_iff]

theorem glue_stability_weight_iff (D : ZeroSumGlueData) :
    D.GlueKingStable ↔ ∀ W : D.Glue.SubRep,
      0 < D.SrcDim W + D.SnkDim W →
      D.SrcDim W + D.SnkDim W < D.FullSrcDim + D.FullSnkDim →
      0 < positiveWeight D.FullSrcDim D.FullSnkDim (D.SrcDim W) (D.SnkDim W) := by
  simp only [ZeroSumGlueData.GlueKingStable,positiveWeight_pos_iff]

end KroneckerManuscriptBipartiteStability

set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.positiveWeight
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.positiveWeight_pos_iff
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.subrep_support_subset
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.subrepFiniteSupport
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.weight
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.Stable
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.negativeVertexWeight
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.total_dimension_sum
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.weightOn_eq
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.stable_iff_coordinate
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.block_stability_weight_iff
set_option pp.fullNames true in
#print axioms KroneckerManuscriptBipartiteStability.glue_stability_weight_iff
