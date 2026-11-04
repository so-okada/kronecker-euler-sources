import KroneckerManuscriptGluingStability
import KroneckerGluedSupportTree
import KroneckerGluedProperColoring

/-! Proper gluing data and the separate dimension, flow and stability statements.
The dimension hypothesis is retained from the input manuscript. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerSplitGluingLemmas
open KroneckerManuscriptQuiverDefinitions
open KroneckerLinearCoverBlocks KroneckerGluingKingWeight
open KroneckerIncidenceDivergence KroneckerSkeletonFlowExistence

structure ProperGluingData extends ZeroSumGlueData where
  dimension : ∀ b, Fintype.card (toZeroSumGlueData.blocks b).Sink =
    sourceDimension (toZeroSumGlueData.blocks b) + 1
  slot_injective : ∀ b, Function.Injective
    (fun i : {i // S.incidence i b} =>
      (show (T b).Q.1.Vert × Fin 3 from
        (vertex ⟨(i.val,b),i.property⟩, color ⟨(i.val,b),i.property⟩)))
  source_color_injective : ∀ i, Function.Injective
    (fun b : {b // S.incidence i b} => color ⟨(i,b.val),b.property⟩)

namespace ProperGluingData
variable (D : ProperGluingData)

def sourceDimensionAt (b : D.S.Sink) : ℕ :=
  sourceDimension (D.toZeroSumGlueData.blocks b)
def c : ℕ := Fintype.card D.S.Source
def k : ℕ := D.c + 1
def a : ℕ := (∑ b, D.sourceDimensionAt b) + D.c
def x : ℝ := (D.a : ℝ) / D.k
def alpha (_ : D.S.Source) : ℝ := D.x + 1
def xi (b : D.S.Sink) : ℝ := D.x - D.sourceDimensionAt b
def flows : Set (Edge D.S.incidence → ℝ) :=
  {f | FlowEquations D.x D.sourceDimensionAt f}

theorem a_eq_source_dimension : D.a = D.toZeroSumGlueData.FullSrcDim := by
  rw [D.toZeroSumGlueData.full_source_dimension]
  rfl

theorem x_eq_slope : D.x = slopeParameter (I := D.S.Source) D.toZeroSumGlueData.blocks := by
  simp only [x, k, c, Nat.cast_add, Nat.cast_one]
  rw [D.a_eq_source_dimension, ←D.toZeroSumGlueData.slope_matches_manuscript]

theorem dimensions :
    D.toZeroSumGlueData.FullSrcDim = D.a ∧
    D.toZeroSumGlueData.FullSnkDim = D.a + D.k := by
  refine ⟨D.a_eq_source_dimension.symm, ?_⟩
  rw [D.toZeroSumGlueData.total_dimension_pair D.dimension, ←D.a_eq_source_dimension]
  rfl

theorem flow_exists_unique : ∃! f, f ∈ D.flows := by
  change ∃! f, FlowEquations D.x D.sourceDimensionAt f
  rw [D.x_eq_slope]
  exact unique_skeleton_flow D.S.incidence D.S.tree D.toZeroSumGlueData.source_degree_card
    _ _ (slope_parameter_balance D.toZeroSumGlueData.blocks)

theorem stable_iff_positive (f : Edge D.S.incidence → ℝ) (hf : f ∈ D.flows) :
    D.toZeroSumGlueData.GlueKingStable ↔ ∀ e, 0 < f e := by
  change FlowEquations D.x D.sourceDimensionAt f at hf
  rw [D.x_eq_slope] at hf
  exact D.toZeroSumGlueData.stability_iff_positive_edge_flow D.dimension f hf.1 hf.2

end ProperGluingData
end KroneckerSplitGluingLemmas

#print axioms KroneckerSplitGluingLemmas.ProperGluingData
#print axioms KroneckerSplitGluingLemmas.ProperGluingData.dimensions
#print axioms KroneckerSplitGluingLemmas.ProperGluingData.flow_exists_unique
#print axioms KroneckerSplitGluingLemmas.ProperGluingData.stable_iff_positive
