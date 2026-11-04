import KroneckerChainPositiveBins

section

set_option autoImplicit false
namespace KroneckerChainDimensionSum
open KroneckerChainFlowRecovery
open scoped BigOperators

theorem chain_dimension_sum (x : ℝ) (n : ℕ) (l r : ℕ → ℝ) :
    leftEnd x l+rightEnd x n r+(∑ t∈Finset.range (n+1),middleSize l r t)+
      (∑ t∈Finset.range n,internalSize x l r t)=((n : ℝ)+2)*x-((n : ℝ)+1) := by
  induction n with
  | zero => simp [leftEnd,rightEnd,middleSize]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ (fun t => middleSize l r t),
      Finset.sum_range_succ (fun t => internalSize x l r t)]
    dsimp [leftEnd,rightEnd,middleSize,internalSize] at ih ⊢
    push_cast
    linarith


end KroneckerChainDimensionSum
end

section

set_option autoImplicit false
namespace KroneckerChainFlowIntegrality
open KroneckerChainFlowRecovery

def OnLattice (o y : ℝ) : Prop := ∃ z : ℤ,y=o+(z : ℝ)

theorem chain_left_integral (x : ℝ) (l : ℕ → ℝ) (h : OnLattice x (l 0)) :
    ∃ z : ℤ,leftEnd x l=z := by
  obtain ⟨z,hz⟩ := h
  exact ⟨-z,by simp only [leftEnd,Int.cast_neg]; linarith⟩

theorem chain_middle_integral (x : ℝ) (l r : ℕ → ℝ) (t : ℕ)
    (hl : OnLattice (((t : ℝ)+1)*x) (l t))
    (hr : OnLattice (-((t : ℝ)+1)*x) (r t)) :
    ∃ z : ℤ,middleSize l r t=z := by
  obtain ⟨u,hu⟩ := hl
  obtain ⟨v,hv⟩ := hr
  refine ⟨u+v-1,?_⟩
  simp only [middleSize,Int.cast_sub,Int.cast_add,Int.cast_one]
  linarith

theorem chain_internal_integral (x : ℝ) (l r : ℕ → ℝ) (t : ℕ)
    (hr : OnLattice (-((t : ℝ)+1)*x) (r t))
    (hl : OnLattice ((((t+1 : ℕ) : ℝ)+1)*x) (l (t+1))) :
    ∃ z : ℤ,internalSize x l r t=z := by
  obtain ⟨u,hu⟩ := hr
  obtain ⟨v,hv⟩ := hl
  refine ⟨-u-v,?_⟩
  simp only [internalSize,Int.cast_sub,Int.cast_neg]
  push_cast at hv
  linarith

theorem chain_right_integral (x : ℝ) (n a : ℕ) (r : ℕ → ℝ)
    (ha : ((n : ℝ)+2)*x=a) (hr : OnLattice (-((n : ℝ)+1)*x) (r n)) :
    ∃ z : ℤ,rightEnd x n r=z := by
  obtain ⟨u,hu⟩ := hr
  refine ⟨(a : ℤ)-u,?_⟩
  simp only [rightEnd,Int.cast_sub,Int.cast_natCast]
  linarith

end KroneckerChainFlowIntegrality
end

