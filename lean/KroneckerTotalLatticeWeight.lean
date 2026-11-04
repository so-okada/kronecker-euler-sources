import KroneckerParameterWeightLower

set_option autoImplicit false
namespace KroneckerTotalLatticeWeight
open KroneckerLatticeFiberCount KroneckerParameterWeightLower KroneckerFixedFlowWeight
open KroneckerChainLatticeParameters KroneckerFiniteStateBins KroneckerChainSlotProductLower
open KroneckerLatticeDimensionEmbedding KroneckerFiniteChainInputs
open KroneckerEnumeratedStableExistence

/-- Count only the fixed state-one, bin-zero flows used in the revised paper. -/
theorem fixed_lattice_weight_lower {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) :
    (x/256-1)^(2*(n+1))*geometryFactor n x*(1/100 : ℝ)^n≤
      ∑ L : LatticeFor x (canonicalBins n),
        dimensionWeight (dimensions (parameterDimensions hx ha ⟨canonicalBins n,L⟩)) := by
  have hq : 0≤x/256-1 := by linarith
  have hg : 0≤geometryFactor n x := by unfold geometryFactor; positivity
  have hw := word_weight_nonnegative (canonicalBins n)
  calc
    (x/256-1)^(2*(n+1))*geometryFactor n x*(1/100 : ℝ)^n ≤
        (x/256-1)^(2*(n+1))*(geometryFactor n x*wordWeight (canonicalBins n)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (fixed_word_weight_lower n)
        (mul_nonneg (pow_nonneg hq _) hg)
    _ ≤ (Fintype.card (LatticeFor x (canonicalBins n)) : ℝ)*
        (geometryFactor n x*wordWeight (canonicalBins n)) :=
      mul_le_mul_of_nonneg_right (lattice_fiber_lower x (canonicalBins n) (by linarith))
        (mul_nonneg hg hw)
    _ = ∑ _L : LatticeFor x (canonicalBins n),
        geometryFactor n x*wordWeight (canonicalBins n) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum (fun L _ => parameter_weight_lower hx ha ⟨canonicalBins n,L⟩)

/-- The fixed family embeds into the constructed support family. -/
theorem total_lattice_weight_lower {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) :
    (x/256-1)^(2*(n+1))*geometryFactor n x*(1/100 : ℝ)^n≤
      ∑ p : LatticeParameter n x,dimensionWeight (dimensions (parameterDimensions hx ha p)) := by
  apply (fixed_lattice_weight_lower hx ha).trans
  have hs : (∑ p : LatticeParameter n x,
      dimensionWeight (dimensions (parameterDimensions hx ha p))) =
      ∑ P : StateBins n, ∑ L : LatticeFor x P,
        dimensionWeight (dimensions (parameterDimensions hx ha ⟨P,L⟩)) := by
    convert Fintype.sum_sigma (fun p : LatticeParameter n x =>
      dimensionWeight (dimensions (parameterDimensions hx ha p))) using 1
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_univ]
    · intro p _
      rfl
  rw [hs]
  apply Finset.single_le_sum (f := fun P : StateBins n =>
    ∑ L : LatticeFor x P, dimensionWeight (dimensions (parameterDimensions hx ha ⟨P,L⟩)))
    (fun P _ => ?_) (Finset.mem_univ (canonicalBins n))
  apply Finset.sum_nonneg
  intro L _
  unfold dimensionWeight
  exact Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

end KroneckerTotalLatticeWeight
