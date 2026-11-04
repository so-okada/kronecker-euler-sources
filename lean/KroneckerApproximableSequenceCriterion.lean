import KroneckerLogic

/-! A direct sequence criterion for nonvacuity of the manuscript joint-limit
domain, with no source-bearing auxiliary parameter space. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerApproximableSequenceCriterion
open Filter KroneckerLogic
open scoped Topology
variable {X : Type} (height : X → ℕ) (slope : X → ℝ) {r : ℝ}

theorem of_sequence (p : ℕ → X) (ha : Tendsto (fun n => height (p n)) atTop atTop)
    (hs : Tendsto (fun n => slope (p n)) atTop (𝓝 r)) : Approximable height slope r := by
  intro δ hδ N
  obtain ⟨n,hn,hns⟩ := (ha.eventually (eventually_ge_atTop N)).and
    ((Metric.tendsto_nhds.mp hs) δ hδ) |>.exists
  exact ⟨p n,hn,hns⟩
end KroneckerApproximableSequenceCriterion
