import KroneckerManuscriptFlowFamily
import KroneckerSplitGluingLemmas
import KroneckerChainTransitionWeights

/-! The four flow-choice lemmas, in manuscript order.
Here c = n+1, k = n+2 and the manuscript index t is i.val+1. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerSplitFlowChoiceLemmas
open KroneckerManuscriptFlowFamily KroneckerFiniteBinLattices

theorem dimensions {n a : ℕ} {x : ℝ} (C : Coordinates n x)
    (hx : 100000 ≤ x) (ha : ((n : ℝ)+2)*x=a) :
    (∀ e, 0 < toFlow C e) ∧
    (∀ b, ∃ z : ℤ, sourceDimension x (toFlow C) b = z) ∧
    (∑ b, sourceDimension x (toFlow C) b) = (a : ℝ)-((n : ℝ)+1) ∧
    (∀ b, 256 < sourceDimension x (toFlow C) b ∧ sourceDimension x (toFlow C) b < x) :=
  ⟨positive C hx, dimensions_integral C ha, dimension_sum C ha, dimension_bounds C hx⟩

theorem lattice_counts (x o : ℝ) (hx : 100000 ≤ x) :
    x/256-1 ≤ (Fintype.card (BinPoint x o 1) : ℝ) ∧
    x/256-1 ≤ (Fintype.card (PositiveBinPoint x (-o) 0) : ℝ) :=
  ⟨bin_point_lower x o 1 (by linarith), positive_bin_point_lower x (-o) 0 (by linarith)⟩

theorem dimensions_injective (a n : ℕ) :
    Function.Injective (fun f : Family a n => sourceDimension ((a : ℝ)/((n : ℝ)+2)) f.val) :=
  sourceDimension_injective a n

theorem stable_of_positive
    (D : KroneckerSplitGluingLemmas.ProperGluingData)
    (f : KroneckerIncidenceDivergence.Edge D.S.incidence → ℝ)
    (hf : f ∈ D.flows) (hpos : ∀ e, 0 < f e) :
    D.toZeroSumGlueData.GlueKingStable :=
  (D.stable_iff_positive f hf).mpr hpos

theorem transition_weight (x l r l' : ℝ) (hx : 100000 ≤ x)
    (hl : x/256 ≤ l ∧ l < 2*x/256) (hr : 0 < r ∧ r < x/256)
    (hl' : x/256 ≤ l' ∧ l' < 2*x/256) :
    (256 : ℝ)^2/100*x^(-2 : ℝ) ≤
      (l+r-1)^(-3/2 : ℝ)*(x-r-l')^(-1/2 : ℝ) := by
  obtain ⟨_, _, _, _, hy, hz⟩ :=
    KroneckerManuscriptFlowIntervals.block_dimensions x l r l' hx hl hr hl'
  have h := KroneckerTransitionInversePowers.transition_inverse_lower
    (x/256) 3 255 (l+r-1) (x-r-l') (by linarith) (by norm_num) (by norm_num)
    (by linarith [hy.1]) (by linarith [hz.1]) (by linarith [hl.2,hr.2])
    (by linarith [hl'.1,hr.1])
  rw [KroneckerChainTransitionWeights.bin_scale_inverse x (by linarith)] at h
  have hs : Real.sqrt ((3 : ℝ)^3*255) ≤ 100 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ)^3*255 by norm_num),
      Real.sqrt_nonneg ((3 : ℝ)^3*255)]
  calc
    (256 : ℝ)^2/100*x^(-2 : ℝ) = ((256 : ℝ)^2*x^(-2 : ℝ))/100 := by ring
    _ ≤ ((256 : ℝ)^2*x^(-2 : ℝ))/Real.sqrt ((3 : ℝ)^3*255) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hs
    _ ≤ _ := h

theorem leaf_weight (x u v w : ℝ) (hx : 0 < x)
    (hu : 0 < u ∧ u ≤ x) (hv : 0 < v ∧ v ≤ x) (hw : 0 < w ∧ w ≤ x) :
    x^(-9/2 : ℝ) ≤ u^(-3/2 : ℝ)*v^(-3/2 : ℝ)*w^(-3/2 : ℝ) := by
  have h1 := Real.rpow_le_rpow_of_nonpos hu.1 hu.2 (show (-3/2 : ℝ) ≤ 0 by norm_num)
  have h2 := Real.rpow_le_rpow_of_nonpos hv.1 hv.2 (show (-3/2 : ℝ) ≤ 0 by norm_num)
  have h3 := Real.rpow_le_rpow_of_nonpos hw.1 hw.2 (show (-3/2 : ℝ) ≤ 0 by norm_num)
  have h12 := mul_le_mul h1 h2 (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hu.1.le _)
  have h123 := mul_le_mul h12 h3 (Real.rpow_nonneg hx.le _)
    (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg hv.1.le _))
  convert h123 using 1 <;>
    simp only [←Real.rpow_add hx] <;> norm_num

end KroneckerSplitFlowChoiceLemmas

#print axioms KroneckerSplitFlowChoiceLemmas.dimensions
#print axioms KroneckerSplitFlowChoiceLemmas.lattice_counts
#print axioms KroneckerSplitFlowChoiceLemmas.dimensions_injective
#print axioms KroneckerSplitFlowChoiceLemmas.stable_of_positive
#print axioms KroneckerSplitFlowChoiceLemmas.transition_weight
#print axioms KroneckerSplitFlowChoiceLemmas.leaf_weight
