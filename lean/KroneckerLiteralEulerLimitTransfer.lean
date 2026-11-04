import KroneckerEulerFramePositivity

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerLiteralEulerLimitTransfer
open KroneckerEulerObservables KroneckerFrameBadDensity KroneckerEulerFramePositivity

theorem literal_euler_limit_transfer (m : ℕ) (hm : 3 ≤ m) (x : ℕ → EulerPoint m) (L : ℝ)
    (ha : Tendsto (fun n => (x n).P.a) atTop atTop)
    (hlegal : ∀ᶠ n in atTop, ∀ r ∈ frameWord (x n).P.a (x n).P.b (x n).P.d₁,
      1 ≤ r ∧ r ≤ m-1)
    (hL : Tendsto (fun n => KroneckerFrameObservables.value m (toFrame (x n))) atTop (𝓝 L)) :
    Tendsto (fun n => value (x n)) atTop (𝓝 L) := by
  have hscaled : Tendsto (fun n => Real.log ((m*(x n).E : ℕ) : ℝ)/((x n).P.a : ℝ)) atTop (𝓝 L) := by
    simpa only [KroneckerFrameObservables.value,toFrame,point_dictionary] using hL
  have hd := KroneckerFixedFactor.normalized_scaled_log_difference
    (fun n => (x n).P.a) (fun n => (x n).E) ha m (by omega)
    (eventual_euler_positive m hm x hlegal)
  simpa only [value,sub_sub_cancel,sub_zero] using hscaled.sub hd

end KroneckerLiteralEulerLimitTransfer
