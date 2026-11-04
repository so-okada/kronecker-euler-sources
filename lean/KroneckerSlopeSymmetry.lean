import KroneckerEndpointRoots

/-! Exact slope and normalization laws for vertex exchange and reflection. -/
set_option autoImplicit false
namespace KroneckerSlopeSymmetry
open KroneckerEndpointRoots

noncomputable def exchange (r : ℝ) : ℝ := 1/r
def reflect (m r : ℝ) : ℝ := m-r
def slopeQuadratic (m r : ℝ) : ℝ := m*r-1-r^2

theorem exchange_involutive {r : ℝ} (hr : r ≠ 0) : exchange (exchange r)=r := by
  simp [exchange]

theorem reflect_involutive (m r : ℝ) : reflect m (reflect m r)=r := by
  simp [reflect]

theorem slopeQuadratic_reflect (m r : ℝ) :
    slopeQuadratic m (reflect m r)=slopeQuadratic m r := by
  simp [slopeQuadratic,reflect]
  ring

theorem slopeQuadratic_exchange {m r : ℝ} (hr : r ≠ 0) :
    slopeQuadratic m (exchange r)=slopeQuadratic m r/r^2 := by
  simp [slopeQuadratic,exchange]
  field_simp
  ring



theorem exchange_lowerRoot {m : ℝ} (hm : 2 < m) :
    exchange (lowerRoot m)=upperRoot m := by
  have hp := root_product hm.le
  have hn := ne_of_gt (lowerRoot_positive hm)
  rw [exchange]
  apply (div_eq_iff hn).2
  simpa [mul_comm] using hp.symm

theorem exchange_upperRoot {m : ℝ} (hm : 2 < m) :
    exchange (upperRoot m)=lowerRoot m := by
  have hp := root_product hm.le
  have hn := ne_of_gt (upperRoot_positive hm)
  rw [exchange]
  apply (div_eq_iff hn).2
  exact hp.symm

theorem reflect_mem_interior {m r : ℝ} (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    reflect m r ∈ Set.Ioo (lowerRoot m) (upperRoot m) := by
  have hs := root_sum m
  constructor <;> simp only [reflect] <;> linarith [hr.1,hr.2]

theorem exchange_mem_interior {m r : ℝ} (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    exchange r ∈ Set.Ioo (lowerRoot m) (upperRoot m) := by
  have hr0 : 0 < r := (lowerRoot_positive hm).trans hr.1
  have hp := root_product hm.le
  constructor
  · rw [exchange,lt_div_iff₀ hr0]
    nlinarith [hr.2]
  · rw [exchange,div_lt_iff₀ hr0]
    have hmul := mul_lt_mul_of_pos_left hr.1 (upperRoot_positive hm)
    nlinarith


theorem upper_tail_combined (m r : ℝ) :
    exchange (reflect m r)=1/(m-r) := rfl

theorem combined_decreases {m r : ℝ} (hq : 0 < slopeQuadratic m r)
    (hden : 0 < m-r) : exchange (reflect m r)<r := by
  rw [upper_tail_combined]
  rw [div_lt_iff₀ hden]
  unfold slopeQuadratic at hq
  nlinarith



theorem root_gap_product {m r : ℝ} (hm : 2 ≤ m) :
    (upperRoot m-r)*(r-lowerRoot m)=slopeQuadratic m r := by
  exact (quadratic_factorization hm).symm

end KroneckerSlopeSymmetry
