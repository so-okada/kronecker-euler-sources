import KroneckerNearbyShortFactor
import KroneckerFrameSlopeLimit

section

/-! Convergence to a rational slope eventually enters the uniform phase neighborhood. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualPhaseNeighborhood
open KroneckerMechanicalWords KroneckerMechanicalWindows KroneckerRationalWordRotation
open KroneckerNearbyRationalPhase

theorem eventually_phase_neighborhood (s : ℕ → ℝ) (p q : ℕ) (hq : 0 < q)
    (hs : Tendsto s atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    ∀ᶠ n in atTop, |s n-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2 := by
  have he : (0 : ℝ) < 1/(q : ℝ)^2 := by positivity
  simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hs) (1/(q : ℝ)^2) he

theorem eventually_good_phase (s : ℕ → ℝ) (p q : ℕ) (hq : 1 < q) (hc : p.Coprime q)
    (hs : Tendsto s atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    ∀ᶠ n in atTop, ∀ u start, windowSum (s n) u q start=(p : ℤ) →
      ∃ j < q, mechanicalWord (s n) u start q=(rationalPeriod p q).rotate j := by
  filter_upwards [eventually_phase_neighborhood s p q (by omega) hs] with n hn
  intro u start hgood
  exact nearby_good_window_rotation p q hq hc (s n) u start hn hgood

end KroneckerEventualPhaseNeighborhood
end

section

/-! Actual literal frame slopes satisfy the formerly assumed phase classification. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualFramePhase
open KroneckerMechanicalWords KroneckerMechanicalWindows KroneckerFrameSlope
open KroneckerFrameSlopeLimit KroneckerEventualPhaseNeighborhood KroneckerRationalWordRotation

theorem eventual_frame_phase (p q : ℕ) (hq : 1 < q) (hc : p.Coprime q)
    (a b d : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    ∀ᶠ n in atTop, ∀ i,
      windowSum (frameSlope (a n) (b n) (d n)) 0 (rationalPeriod p q).length i=(p : ℤ) →
      ∃ j ≤ (rationalPeriod p q).length,
        mechanicalWord (frameSlope (a n) (b n) (d n)) 0 i (rationalPeriod p q).length =
          (rationalPeriod p q).rotate j := by
  have h := eventually_good_phase (fun n => frameSlope (a n) (b n) (d n)) p q hq hc
    (frame_slope_limit a b d _ ha hd hr)
  filter_upwards [h] with n hn
  intro i hi
  rw [rationalPeriod_length] at hi ⊢
  obtain ⟨j,hj,heq⟩ := hn 0 i hi
  exact ⟨j,hj.le,heq⟩

end KroneckerEventualFramePhase
end

