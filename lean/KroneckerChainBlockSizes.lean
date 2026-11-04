import KroneckerChainBlockNeighbors
import KroneckerChainFlowIntegrality

set_option autoImplicit false
namespace KroneckerChainBlockSizes
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainFlowRecovery
open KroneckerChainDimensionSum
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def blockSize (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) : Block n → ℝ
  | .inl j => Fin.cases (leftEnd x l)
      (Fin.lastCases (rightEnd x n r) (fun t : Fin n => internalSize x l r t)) j
  | .inr i => middleSize l r i

theorem size_left (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) :
    blockSize n x l r (leftBlock n)=leftEnd x l := rfl

theorem size_right (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) :
    blockSize n x l r (rightBlock n)=rightEnd x n r := by
  change blockSize n x l r (.inl (Fin.last n).succ)=_
  simp only [blockSize,Fin.cases_succ,Fin.lastCases_last]

theorem size_middle {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) (i : Connector n) :
    blockSize n x l r (middleBlock i)=middleSize l r i := rfl

theorem size_internal {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) (t : Fin n) :
    blockSize n x l r (internalBlock t)=internalSize x l r t := by
  simp [blockSize,internalBlock]

theorem block_size_sum (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) :
    (∑ j,blockSize n x l r j)=((n : ℝ)+2)*x-((n : ℝ)+1) := by
  have h := chain_dimension_sum x n l r
  simp only [Fintype.sum_sum_type,blockSize]
  rw [Fin.sum_univ_succ,Fin.sum_univ_castSucc]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.lastCases_castSucc,Fin.lastCases_last]
  rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range]
  linarith

theorem block_sizes_recover_flows (n : ℕ) (x : ℝ) (l r L R : ℕ → ℝ)
    (h : blockSize n x l r=blockSize n x L R) :
    ∀ t≤n,l t=L t ∧ r t=R t := by
  apply flow_recovery x n l r L R
  · simpa only [size_left] using congrFun h (leftBlock n)
  · intro t ht
    simpa only [size_middle] using congrFun h (middleBlock (⟨t,by omega⟩ : Connector n))
  · intro t ht
    simpa only [size_internal] using congrFun h (internalBlock (⟨t,ht⟩ : Fin n))

end KroneckerChainBlockSizes
