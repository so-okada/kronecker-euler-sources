import KroneckerChainFlowWeights
import KroneckerChainBlockSizes

section

set_option autoImplicit false
namespace KroneckerChainBinRecovery
open KroneckerChainPositiveBins KroneckerChainFlowRecovery

theorem bin_index_unique (x y : ℝ) (i j : ℕ) (hx : 0<x)
    (hi : InBin x i y) (hj : InBin x j y) : i=j := by
  dsimp [InBin] at hi hj
  by_contra h
  rcases lt_or_gt_of_ne h with hlt|hgt
  · have hn : (i : ℝ)+1≤j := by exact_mod_cast hlt
    nlinarith
  · have hn : (j : ℝ)+1≤ i := by exact_mod_cast hgt
    nlinarith


end KroneckerChainBinRecovery
end

section

set_option autoImplicit false
namespace KroneckerChainBinFamily
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainBlockSizes
open KroneckerChainFlowWeights KroneckerChainPositiveBins KroneckerChainFlowRecovery
open KroneckerChainBinRecovery

structure BinData (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ) : Prop where
  state_pos : ∀ (t : ℕ), t ≤ n → 1 ≤ i t
  same_bound : ∀ (t : ℕ), t ≤ n → i t + h t ≤ 253
  next_bound : ∀ (t : ℕ), t < n → i (t+1) + h t ≤ 253
  left_bin : ∀ (t : ℕ), t ≤ n → InBin x (i t) (l t)
  right_bin : ∀ (t : ℕ), t ≤ n → InBin x (h t) (r t)
  right_pos : ∀ (t : ℕ), t ≤ n → 0 < r t
  last_zero : h n=0

theorem bin_flows_positive (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ)
    (hx : 100000≤x) (H : BinData n x l r i h) :
    ∀ e : KroneckerIncidenceDivergence.Edge (@incidence n),0<chainFlow x l r e := by
  apply (flow_positive_iff x l r).mpr
  intro t
  have ht : (t : ℕ)≤n := by omega
  exact ⟨bin_positive x (l t) (i t) hx (H.state_pos t ht) (H.left_bin t ht),
    (middle_block_size_bounds x (l t) (r t) (i t) (h t) hx (H.state_pos t ht)
      (H.same_bound t ht) (H.left_bin t ht) (H.right_bin t ht) (H.right_pos t ht)).2.2,
    H.right_pos t ht⟩

theorem bin_block_size_bounds (n : ℕ) (x : ℝ) (l r : ℕ → ℝ) (i h : ℕ → ℕ)
    (hx : 100000≤x) (H : BinData n x l r i h) :
    ∀ j : Block n,256<blockSize n x l r j ∧ blockSize n x l r j<x := by
  intro j
  rcases block_cases j with rfl|rfl|⟨t,rfl⟩|⟨t,rfl⟩
  · rw [size_left]
    have hb := H.same_bound 0 (by omega)
    exact end_block_size_bounds x (l 0) (i 0) hx (by omega) (H.left_bin 0 (by omega))
      (bin_positive x (l 0) (i 0) hx (H.state_pos 0 (by omega)) (H.left_bin 0 (by omega)))
  · rw [size_right]
    have hb := H.same_bound n le_rfl
    exact end_block_size_bounds x (r n) (h n) hx (by omega) (H.right_bin n le_rfl)
      (H.right_pos n le_rfl)
  · rw [size_middle]
    have ht : (t : ℕ)≤n := by omega
    have hb := middle_block_size_bounds x (l t) (r t) (i t) (h t) hx (H.state_pos t ht)
      (H.same_bound t ht) (H.left_bin t ht) (H.right_bin t ht) (H.right_pos t ht)
    exact ⟨hb.1,hb.2.1⟩
  · rw [size_internal]
    exact internal_block_size_bounds x (l (t+1)) (r t) (i (t+1)) (h t) hx
      (H.state_pos (t+1) (by omega)) (H.next_bound t t.isLt)
      (H.left_bin (t+1) (by omega)) (H.right_bin t (by omega)) (H.right_pos t (by omega))


end KroneckerChainBinFamily
end

