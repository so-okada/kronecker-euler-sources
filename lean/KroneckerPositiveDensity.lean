import KroneckerRoundedScaling

set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPositiveDensity

theorem positive_density_atTop (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (c : ℝ) (hc : 0 < c)
    (hb : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 c)) :
    Tendsto b atTop atTop := by
  apply tendsto_atTop.2
  intro K
  have hz : Tendsto (fun n => (K : ℝ)/(a n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  filter_upwards [ha.eventually (eventually_ge_atTop 1),
    (tendsto_order.1 hz).2 (c/2) (by linarith),
    (tendsto_order.1 hb).1 (c/2) (by linarith)] with n hn hK hb'
  have hpos : (0 : ℝ) < a n := by exact_mod_cast (show 0 < a n by omega)
  have h : (K : ℝ) < b n := (div_lt_div_iff_of_pos_right hpos).mp (lt_trans hK hb')
  exact_mod_cast h.le

end KroneckerPositiveDensity
