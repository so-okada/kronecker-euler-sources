import KroneckerFrameWord

/-! A limit strictly inside the alphabet bounds makes literal frames eventually legal. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualFrameAlphabet
open KroneckerFrameSlope KroneckerFrameSlopeLimit KroneckerFrameBadDensity KroneckerFrameWord

theorem eventual_frame_alphabet (a b d : ℕ → ℕ) (M : ℕ) (r : ℝ)
    (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r))
    (h₁ : 1 < r) (hM : r < (M : ℝ)) :
    ∀ᶠ n in atTop, ∀ x ∈ frameWord (a n) (b n) (d n), 1 ≤ x ∧ x ≤ M := by
  have hs := frame_slope_limit a b d r ha hd hr
  filter_upwards [(tendsto_order.1 hs).1 1 h₁,(tendsto_order.1 hs).2 (M : ℝ) hM] with n hn₁ hnM
  exact frameWord_legal (a n) (b n) (d n) M hn₁.le hnM.le

end KroneckerEventualFrameAlphabet
