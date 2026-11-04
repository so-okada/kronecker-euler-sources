import KroneckerThreeEntropySequences
import KroneckerFrameLimitBounds

/- Original module: KroneckerThreeEntropyBounds -/
section
/-! Uniform positive and finite bounds for the canonical three-arrow interior entropy. -/
set_option autoImplicit false
namespace KroneckerThreeEntropyBounds
open KroneckerThreeEntropy KroneckerFrameObservables KroneckerLogic

theorem entropy_bounds (r : ℝ) (hr : r ∈ interior) :
    Real.log 3/2 ≤ entropy r ∧ entropy r ≤ 9*Real.log 2 := by
  obtain ⟨x⟩ := approaching_nonempty height slope (frame_approximable r hr.1)
  have hlegal := KroneckerEventualFrameAlphabet.eventual_frame_alphabet
    (fun n => (x.val n).a) (fun n => (x.val n).b) (fun n => (x.val n).d) 2 r
    x.property.1 (fun n => (x.val n).hd) x.property.2 hr.1 hr.2
  have h := KroneckerFrameLimitBounds.frame_limit_bounds 3 (by omega) x.val _ x.property.1 hlegal
    (jointLimit_sequence height slope (value 3) (entropy_joint r hr) x.val x.property.1 x.property.2)
  norm_num at h ⊢
  exact h

end KroneckerThreeEntropyBounds
end

/- Original module: KroneckerThreeEntropyPositive -/
section
/-! Strict positivity and an absolute uniform bound on the three-arrow interior entropy. -/
set_option autoImplicit false
namespace KroneckerThreeEntropyPositive
open KroneckerThreeEntropy

theorem entropy_positive (r : ℝ) (hr : r ∈ interior) : 0 < entropy r := by
  have h := (KroneckerThreeEntropyBounds.entropy_bounds r hr).1
  have hp : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  linarith

theorem entropy_abs_bound (r : ℝ) (hr : r ∈ interior) : |entropy r| ≤ 9*Real.log 2 := by
  rw [abs_of_pos (entropy_positive r hr)]
  exact (KroneckerThreeEntropyBounds.entropy_bounds r hr).2

end KroneckerThreeEntropyPositive
end
