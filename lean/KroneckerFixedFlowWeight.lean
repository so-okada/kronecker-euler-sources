import KroneckerChainTransitionWeights
import KroneckerEnumeratedStableExistence
import KroneckerLogic

set_option autoImplicit false
namespace KroneckerFixedFlowWeight
open KroneckerChainTransitionWeights KroneckerFiniteStateBins KroneckerEnumeratedStableExistence

noncomputable def wordWeight {n : ℕ} (P : StateBins n) : ℝ :=
  ∏ t : Fin n,transitionWeight (stateValue (P.1 t.castSucc))
    (stateValue (P.1 t.succ)) (P.2 t).val

theorem word_weight_nonnegative {n : ℕ} (P : StateBins n) : 0≤wordWeight P := by
  apply Finset.prod_nonneg
  intro t _
  dsimp [transitionWeight]
  positivity

/-- The paper fixes state one and bin zero at every connector.
The empty product covers the one-connector case. -/
theorem fixed_word_weight (n : ℕ) :
    wordWeight (canonicalBins n)=(1/Real.sqrt (6885 : ℝ))^n := by
  change (∏ _t : Fin n,transitionWeight 1 1 0)=_
  have hz : transitionWeight 1 1 0=1/Real.sqrt (6885 : ℝ) := by
    norm_num [transitionWeight]
  rw [hz]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem fixed_word_weight_lower (n : ℕ) :
    (1/100 : ℝ)^n ≤ wordWeight (canonicalBins n) := by
  rw [fixed_word_weight]
  exact pow_le_pow_left₀ (by norm_num) KroneckerLogic.matrix_entry_constant.le n

end KroneckerFixedFlowWeight
