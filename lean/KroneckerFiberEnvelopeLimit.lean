import KroneckerNormalizedFiberBound

/-! For fixed generating parameter, the fiber envelope tends to log(1+t). -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFiberEnvelopeLimit

noncomputable def fiberEnvelope (m : ℕ) (t x : ℝ) : ℝ :=
  (1+x)*Real.log (1+t)+x*(2*(m : ℝ)*Real.log 2-Real.log t)


theorem fiberEnvelope_limit (m : ℕ) (t : ℝ) (x : ℕ → ℝ)
    (hx : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun n => fiberEnvelope m t (x n)) atTop (𝓝 (Real.log (1+t))) := by
  have h := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hx).mul_const (Real.log (1+t))).add
    (hx.mul_const (2*(m : ℝ)*Real.log 2-Real.log t))
  simpa only [fiberEnvelope,add_zero,zero_mul,one_mul] using h

end KroneckerFiberEnvelopeLimit
