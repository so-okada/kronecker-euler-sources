import KroneckerChainSlotProductLower
import KroneckerFixedFlowWeight

/- Original module: KroneckerChainDimensionWeight -/
section
set_option autoImplicit false
namespace KroneckerChainDimensionWeight
open KroneckerChainSlotProductLower KroneckerChainUniformSlotBounds KroneckerChainBlockProducts
open KroneckerChainBlockNeighbors KroneckerChainIncidence

theorem dimension_weight_decomposition {n : ℕ} (d : Block n → ℕ) :
    dimensionWeight d=
      (d (leftBlock n) : ℝ)^(-3/2 : ℝ)*(d (rightBlock n) : ℝ)^(-3/2 : ℝ)*
      (d (middleBlock (Fin.last n)) : ℝ)^(-3/2 : ℝ)*
      ∏ t : Fin n,((d (middleBlock t.castSucc) : ℝ)^(-3/2 : ℝ)*
        (d (internalBlock t) : ℝ)^(-1/2 : ℝ)) := by
  rw [dimensionWeight,chain_block_product]
  simp only [blockProfile,leftBlock,rightBlock,middleBlock,internalBlock,
    show Fin.last (n+1)=(Fin.last n).succ by rfl,
    Fin.cases_zero,Fin.cases_succ,Fin.lastCases_last,Fin.lastCases_castSucc]
  rw [Fin.prod_univ_castSucc (fun t : Connector n => (d (Sum.inr t) : ℝ)^(-3/2 : ℝ)),
    Finset.prod_mul_distrib]
  ring

theorem three_leaf_weight_lower (x u v w : ℝ) (hx : 0<x)
    (hu : 0<u) (hv : 0<v) (hw : 0<w) (hux : u≤x) (hvx : v≤x) (hwx : w≤x) :
    x^(-9/2 : ℝ)≤u^(-3/2 : ℝ)*v^(-3/2 : ℝ)*w^(-3/2 : ℝ) := by
  have he : x^(-9/2 : ℝ)=x^(-3/2 : ℝ)*x^(-3/2 : ℝ)*x^(-3/2 : ℝ) := by
    rw [←Real.rpow_add hx,←Real.rpow_add hx]
    norm_num
  rw [he]
  apply mul_le_mul
  · exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hu hux (by norm_num))
      (Real.rpow_le_rpow_of_nonpos hv hvx (by norm_num))
      (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hu.le _)
  · exact Real.rpow_le_rpow_of_nonpos hw hwx (by norm_num)
  · exact Real.rpow_nonneg hx.le _
  · exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _)

end KroneckerChainDimensionWeight
end

/- Original module: KroneckerParameterWeightLower -/
section
set_option autoImplicit false
namespace KroneckerParameterWeightLower
open KroneckerFixedFlowWeight KroneckerChainDimensionWeight KroneckerChainTransitionWeights
open KroneckerLatticeDimensionEmbedding KroneckerChainLatticeParameters KroneckerFiniteStateBins
open KroneckerChainBinFamily KroneckerChainBlockNeighbors KroneckerChainSlotProductLower
open KroneckerFiniteChainInputs KroneckerChainIncidence

noncomputable def geometryFactor (n : ℕ) (x : ℝ) : ℝ :=
  x^(-9/2 : ℝ)*((256 : ℝ)^2*x^(-2 : ℝ))^n

/-- Every lattice point above a state/bin word has this common lower weight. -/
theorem parameter_weight_lower {n a : ℕ} {x : ℝ} (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) (p : LatticeParameter n x) :
    geometryFactor n x*wordWeight p.1≤dimensionWeight (dimensions (parameterDimensions hx ha p)) := by
  let d := dimensions (parameterDimensions hx ha p)
  have D := lattice_parameter_bins p.2
  have hs := (parameter_dimensions_spec hx ha p).1
  have hb := bin_block_size_bounds n x (leftFlow p.2) (rightFlow p.2)
    (stateFunction p.1) (binFunction p.1) hx D
  have hd : ∀ j : Block n,0<(d j : ℝ) ∧ (d j : ℝ)≤x := by
    intro j
    change 0<(dimensions (parameterDimensions hx ha p) j : ℝ) ∧
      (dimensions (parameterDimensions hx ha p) j : ℝ)≤x
    rw [hs j]
    exact ⟨by linarith [(hb j).1],(hb j).2.le⟩
  have hend := three_leaf_weight_lower x (d (leftBlock n)) (d (rightBlock n))
    (d (middleBlock (Fin.last n))) (by linarith)
    (hd _).1 (hd _).1 (hd _).1 (hd _).2 (hd _).2 (hd _).2
  have ht (t : Fin n) :
      (256 : ℝ)^2*x^(-2 : ℝ)*transitionWeight (stateValue (p.1.1 t.castSucc))
        (stateValue (p.1.1 t.succ)) (p.1.2 t).val≤
      (d (middleBlock t.castSucc) : ℝ)^(-3/2 : ℝ)*(d (internalBlock t) : ℝ)^(-1/2 : ℝ) := by
    have he := chain_transition_weight_lower n x (leftFlow p.2) (rightFlow p.2)
      (stateFunction p.1) (binFunction p.1) hx D t
    rw [←hs (middleBlock t.castSucc),←hs (internalBlock t)] at he
    have ei : stateFunction p.1 t=stateValue (p.1.1 t.castSucc) := extend_at _ t.castSucc
    have ej : stateFunction p.1 (t+1)=stateValue (p.1.1 t.succ) := extend_at _ t.succ
    have eh : binFunction p.1 t=(p.1.2 t).val := by
      simpa only [binFunction,rightBin,Fin.lastCases_castSucc,Fin.val_castSucc] using extend_at (rightBin p.1.2) t.castSucc
    simpa only [ei,ej,eh] using he
  have hp := Finset.prod_le_prod₀ (s:=Finset.univ)
    (fun t _ => show 0≤(256 : ℝ)^2*x^(-2 : ℝ)*transitionWeight
      (stateValue (p.1.1 t.castSucc)) (stateValue (p.1.1 t.succ)) (p.1.2 t).val by
        unfold transitionWeight; positivity)
    (fun t _ => ht t)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hp
  rw [dimension_weight_decomposition]
  have he := mul_le_mul hend hp
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (word_weight_nonnegative p.1))
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (hd _).1.le _) (Real.rpow_nonneg (hd _).1.le _))
      (Real.rpow_nonneg (hd _).1.le _))
  simpa only [geometryFactor,wordWeight,Finset.prod_mul_distrib,mul_pow,mul_assoc,d] using he

end KroneckerParameterWeightLower
end
