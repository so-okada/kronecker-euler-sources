import KroneckerFrameSlopeLimit

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualFrameData
open KroneckerFrameSlope

theorem eventual_frame_data (a b d : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hd : ∀ n, 0 < d n) (r : ℝ)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r))
    (M N : ℕ) (hr1 : 1 < r) (hrM : r < M) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, N ≤ a n ∧ 0 < b n ∧
      1 ≤ frameSlope (a n) (b n) (d n) ∧ frameSlope (a n) (b n) (d n) ≤ M ∧
      |frameSlope (a n) (b n) (d n)-r| < δ := by
  have hf := KroneckerFrameSlopeLimit.frame_slope_limit a b d r ha hd hr
  have habs := (hf.sub_const r).abs
  simp only [sub_self,abs_zero] at habs
  filter_upwards [ha.eventually (eventually_ge_atTop N),
    (tendsto_order.1 hr).1 0 (by linarith),
    (tendsto_order.1 hf).1 1 hr1,(tendsto_order.1 hf).2 M hrM,
    (tendsto_order.1 habs).2 δ hδ] with n hn hb h1 hM hnear
  have hbpos : 0 < b n := by
    by_contra h
    have : b n=0 := by omega
    simp [this] at hb
  exact ⟨hn,hbpos,h1.le,hM.le,hnear⟩

end KroneckerEventualFrameData
