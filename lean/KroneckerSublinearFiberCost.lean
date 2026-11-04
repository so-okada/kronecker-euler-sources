import KroneckerSmallLogParameter

/- Original module: KroneckerEventualFiberEnvelope -/
section
/-! The fiber envelope is eventually arbitrarily small under sublinear deletion density. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualFiberEnvelope
open KroneckerFiberEnvelopeLimit KroneckerSmallLogParameter

theorem eventual_small_fiber_envelope (m : ℕ) (x : ℕ → ℝ)
    (hx : Tendsto x atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ t > 0, ∀ᶠ n in atTop, fiberEnvelope m t (x n) < ε := by
  obtain ⟨t,ht,hlog⟩ := exists_small_log_parameter ε hε
  refine ⟨t,ht,?_⟩
  exact (tendsto_order.1 (fiberEnvelope_limit m t x hx)).2 ε (by linarith)

end KroneckerEventualFiberEnvelope
end

/- Original module: KroneckerSublinearFiberCost -/
section
/-! A sublinear number of deletions has sublinear logarithmic fiber cost. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerSublinearFiberCost
open KroneckerNormalizedFiberBound KroneckerFiberEnvelopeLimit KroneckerEventualFiberEnvelope

theorem normalized_fiber_cost_limit (m : ℕ) (a D : ℕ → ℕ)
    (ha : Tendsto a atTop atTop)
    (hD : Tendsto (fun n => (D n : ℝ)/(a n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => normalizedFiberLog m (a n) (D n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨t,ht,hsmall⟩ := eventual_small_fiber_envelope m
    (fun n => (D n : ℝ)/(a n : ℝ)) hD ε hε
  filter_upwards [ha.eventually (eventually_ge_atTop 1),hsmall] with n hn hs
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (normalizedFiberLog_nonneg m (a n) (D n))]
  exact lt_of_le_of_lt (normalizedFiberLog_bound m (a n) (D n) (by omega) t ht) hs

end KroneckerSublinearFiberCost
end
