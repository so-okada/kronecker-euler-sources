import KroneckerChainLatticeParameters

set_option autoImplicit false
noncomputable section

namespace KroneckerManuscriptFlowIntervals
open KroneckerChainPositiveBins KroneckerFiniteBinLattices

theorem block_dimensions (x l r l' : ℝ) (hx : 100000 ≤ x)
    (hl : x / 256 ≤ l ∧ l < 2 * x / 256)
    (hr : 0 < r ∧ r < x / 256)
    (hl' : x / 256 ≤ l' ∧ l' < 2 * x / 256) :
    0 < l ∧ 0 < x + 1 - l - r ∧
      (256 < x - l ∧ x - l < x) ∧
      (256 < x - r ∧ x - r < x) ∧
      (256 < l + r - 1 ∧ l + r - 1 < x) ∧
      (256 < x - r - l' ∧ x - r - l' < x) := by
  have hL : InBin x 1 l := by norm_num [InBin]; exact hl
  have hR : InBin x 0 r := by simpa [InBin] using And.intro hr.1.le hr.2
  have hL' : InBin x 1 l' := by norm_num [InBin]; exact hl'
  have hp := bin_positive x l 1 hx (by decide) hL
  have hm := middle_block_size_bounds x l r 1 0 hx (by decide) (by decide) hL hR hr.1
  exact ⟨hp, hm.2.2,
    end_block_size_bounds x l 1 hx (by decide) hL hp,
    end_block_size_bounds x r 0 hx (by decide) hR hr.1,
    ⟨hm.1, hm.2.1⟩,
    internal_block_size_bounds x l' r 1 0 hx (by decide) (by decide) hL' hR hr.1⟩

theorem lattice_point_counts (x o : ℝ) (hx : 100000 ≤ x) :
    (1 - 256 / x) * x / 256 ≤ (Fintype.card (BinPoint x o 1) : ℝ) ∧
    (1 - 256 / x) * x / 256 ≤ (Fintype.card (PositiveBinPoint x (-o) 0) : ℝ) := by
  have he : (1 - 256 / x) * x / 256 = x / 256 - 1 := by
    field_simp
  rw [he]
  exact ⟨bin_point_lower x o 1 (by linarith),
    positive_bin_point_lower x (-o) 0 (by linarith)⟩

theorem left_interval (x o : ℝ) (z : ℤ) :
    z ∈ binIndices x o 1 ↔ x / 256 ≤ o + z ∧ o + z < 2 * x / 256 := by
  have h := bin_membership x o 1 z
  norm_num [InBin] at h
  exact h

theorem right_interval (x o : ℝ) (z : ℤ) :
    z ∈ positiveBinIndices x (-o) 0 ↔ 0 < -o + z ∧ -o + z < x / 256 := by
  rw [positive_bin_membership]
  simp only [InBin, Nat.cast_zero, zero_mul, zero_div, zero_add, one_mul]
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · exact fun h => ⟨⟨h.1.le, h.2⟩, h.1⟩

end KroneckerManuscriptFlowIntervals

#print axioms KroneckerManuscriptFlowIntervals.block_dimensions
#print axioms KroneckerManuscriptFlowIntervals.lattice_point_counts
