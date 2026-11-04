import KroneckerFiberEnvelopeLimit

/-! Choose a positive generating parameter with arbitrarily small limiting cost. -/
set_option autoImplicit false
namespace KroneckerSmallLogParameter

theorem log_one_add_le (t : ℝ) (ht : 0 < t) : Real.log (1+t) ≤ t := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1+t by linarith)
  linarith

theorem exists_small_log_parameter (ε : ℝ) (hε : 0 < ε) :
    ∃ t > 0, Real.log (1+t) < ε/2 := by
  refine ⟨ε/4,by positivity,?_⟩
  have h := log_one_add_le (ε/4) (by positivity)
  linarith

end KroneckerSmallLogParameter
