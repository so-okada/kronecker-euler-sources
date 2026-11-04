import KroneckerInteriorSlopeCases
import KroneckerFrameLimitBounds

/- Original module: KroneckerRationalEulerJoint -/
section
/-! The rational Euler limit has a uniform local formulation under the same source interface. -/
set_option autoImplicit false
namespace KroneckerRationalEulerJoint
open KroneckerLogic KroneckerRationalEntropy KroneckerEulerObservables
open KroneckerNonprimitiveLiteratureLimit


end KroneckerRationalEulerJoint
end

/- Original module: KroneckerEulerApproximable -/
section
/-! Euler-domain nonvacuity is isolated precisely as availability of the external Literature data. -/
set_option autoImplicit false
namespace KroneckerEulerApproximable
open KroneckerLogic KroneckerFrameIdentity KroneckerEulerObservables
open KroneckerParameterApproximable

def Covered (m : ℕ) : Prop :=
  ∀ P : ParameterDomain m, ∃ E : ℕ, Nonempty (Literature P.val (E : ℤ))


end KroneckerEulerApproximable
end

/- Original module: KroneckerConcreteLimitUniqueness -/
section
/-! Actual approximation rules out vacuous or conflicting local entropy values. -/
set_option autoImplicit false
namespace KroneckerConcreteLimitUniqueness
open KroneckerLogic KroneckerRationalEntropy KroneckerRationalEulerJoint
open KroneckerEulerApproximable



end KroneckerConcreteLimitUniqueness
end

/- Original module: KroneckerEventualPositiveDimensions -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualPositiveDimensions

theorem eventual_positive_dimensions (a b : ℕ → ℕ) (r : ℝ)
    (ha : Tendsto a atTop atTop) (hr : 0 < r)
    (hs : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r)) :
    ∀ᶠ n in atTop, 0 < a n ∧ 0 < b n := by
  filter_upwards [ha.eventually (eventually_ge_atTop 1),
    (tendsto_order.1 hs).1 0 hr] with n hn hs'
  refine ⟨by omega, ?_⟩
  by_contra hb
  have hz : b n = 0 := by omega
  simp [hz] at hs'

end KroneckerEventualPositiveDimensions
end

/- Original module: KroneckerEventualIntegerEditDensity -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualIntegerEditDensity
open KroneckerFrameBadDensity KroneckerWordEditCost KroneckerFrameEditCost

theorem eventual_integer_edit_density (a b d : ℕ → ℕ) (k : ℕ) (hk : 1 ≤ k)
    (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (k : ℝ))) :
    Tendsto (fun n => (wordEditCost (frameWord (a n) (b n) (d n)) k : ℝ)/(a n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hp := KroneckerEventualPositiveDimensions.eventual_positive_dimensions a b (k : ℝ)
    ha (by exact_mod_cast (show 0 < k by omega)) hr
  have hdim := KroneckerIntegerDeviation.integer_dimension_deviation a b (k : ℝ) ha hr
  have hc : Tendsto (fun n => ((k : ℝ)-1)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  have h := hdim.add hc
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hp] with n hn
  rw [frame_edit_cost_real (a n) (b n) (d n) k hn.1 hn.2 (hd n) hk]
  ring

end KroneckerEventualIntegerEditDensity
end

/- Original module: KroneckerLiteralIntegerLimit -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerLiteralIntegerLimit
open KroneckerWordCounts KroneckerFrameBadDensity KroneckerWordEditCost
open KroneckerSurgeryPadding KroneckerIntegerComparisonLengths
open KroneckerPeriodicTail KroneckerSampledPeriodicLimit

theorem literal_integer_limit (m k : ℕ) (hm : 4 ≤ m) (hk : 1 ≤ k ∧ k ≤ m-2)
    (a b d : ℕ → ℕ) (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 (k : ℝ)))
    (hlegal : ∀ᶠ n in atTop, ∀ r ∈ frameWord (a n) (b n) (d n), 1 ≤ r ∧ r ≤ m-2) :
    Tendsto (fun n => Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/(a n : ℝ))
      atTop (𝓝 (periodicGrowth m [k])) := by
  let D := fun n => wordEditCost (frameWord (a n) (b n) (d n)) k
  let P := fun n => surgeryPadding m (D n)
  have hD := KroneckerEventualIntegerEditDensity.eventual_integer_edit_density a b d k hk.1 ha hd hr
  have hP := surgery_padding_density m a D ha hD
  apply KroneckerPeriodicFiberSandwich.periodic_fiber_sandwich m (by omega) [k]
    (by simp) (by intro r hr'; simp only [List.mem_singleton] at hr'; subst r; exact ⟨hk.1,by omega⟩)
    a (fun n => runCount m (frameWord (a n) (b n) (d n)) 0)
    (fun n => middleLength (a n) (P n)) (fun n => paddedLength (a n) (P n))
    (fun n => a n+1) D ha (middle_length_density a P ha hP)
    (padded_length_density a P ha hP) (successor_length_density a ha) hD
  · filter_upwards [hlegal] with n hn
    exact KroneckerFrameIntegerLower.frame_integer_lower hm (a n) (b n) (d n) hn
  · exact Eventually.of_forall (fun n =>
      KroneckerFrameIntegerUpper.frame_integer_upper hm hk (a n) (b n) (d n))

end KroneckerLiteralIntegerLimit
end

/- Original module: KroneckerInteriorIntegerJoint -/
section
set_option autoImplicit false
namespace KroneckerInteriorIntegerJoint
open KroneckerFrameObservables KroneckerLogic KroneckerPeriodicTail

theorem interior_integer_joint (m k : ℕ) (hm : 4 ≤ m) (hk : 1 < k) (hkM : k < m-2) :
    JointLimit height slope (value m) (k : ℝ) (periodicGrowth m [k]) := by
  apply jointLimit_of_sequences height slope (value m)
  intro x ha hs
  exact KroneckerLiteralIntegerLimit.literal_integer_limit m k hm ⟨by omega,by omega⟩
    (fun n => (x n).a) (fun n => (x n).b) (fun n => (x n).d) ha (fun n => (x n).hd) hs
    (KroneckerEventualFrameAlphabet.eventual_frame_alphabet _ _ _ (m-2) (k : ℝ)
      ha (fun n => (x n).hd) hs (by exact_mod_cast hk) (by exact_mod_cast hkM))

end KroneckerInteriorIntegerJoint
end

/- Original module: KroneckerInteriorLimitExistence -/
section
set_option autoImplicit false
namespace KroneckerInteriorLimitExistence
open KroneckerLogic KroneckerFrameObservables

theorem interior_limit_exists (m : ℕ) (hm : 4 ≤ m) (r : ℝ)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) :
    ∃ L : ℝ, JointLimit height slope (value m) r L := by
  rcases KroneckerInteriorSlopeCases.interior_slope_cases m r hr1
    (hrM.trans_le (by exact_mod_cast (show m-2 ≤ m-1 by omega))) with hi | ⟨k,hk⟩ | hq
  · exact KroneckerIrrationalFrameJoint.irrational_frame_joint m hm r hi hr1 hrM
  · subst r
    exact ⟨_,KroneckerInteriorIntegerJoint.interior_integer_joint m k hm
      (by exact_mod_cast hr1) (by exact_mod_cast hrM)⟩
  · exact ⟨_,KroneckerRationalEntropy.rate_joint m (by omega) r hq⟩

end KroneckerInteriorLimitExistence
end

/- Original module: KroneckerInteriorEntropy -/
section
set_option autoImplicit false
namespace KroneckerInteriorEntropy
open KroneckerLogic KroneckerFrameObservables

def interior (m : ℕ) : Set ℝ := Set.Ioo 1 ((m-2 : ℕ) : ℝ)

noncomputable def entropy (m : ℕ) (r : ℝ) : ℝ := by
  classical
  exact if h : 4 ≤ m ∧ r ∈ interior m then
    Classical.choose (KroneckerInteriorLimitExistence.interior_limit_exists m h.1 r h.2.1 h.2.2)
  else 0

theorem entropy_joint (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    JointLimit height slope (value m) r (entropy m r) := by
  rw [entropy,dite_eq_left ⟨hm,hr⟩]
  exact Classical.choose_spec (KroneckerInteriorLimitExistence.interior_limit_exists m hm r hr.1 hr.2)

end KroneckerInteriorEntropy
end

/- Original module: KroneckerInteriorEntropyUnique -/
section
set_option autoImplicit false
namespace KroneckerInteriorEntropyUnique
open KroneckerLogic KroneckerFrameObservables KroneckerInteriorEntropy



end KroneckerInteriorEntropyUnique
end

/- Original module: KroneckerInteriorEntropyInteger -/
section
set_option autoImplicit false
namespace KroneckerInteriorEntropyInteger
open KroneckerInteriorEntropy KroneckerPeriodicTail


end KroneckerInteriorEntropyInteger
end

/- Original module: KroneckerInteriorEntropyContinuity -/
section
set_option autoImplicit false
namespace KroneckerInteriorEntropyContinuity
open KroneckerInteriorEntropy KroneckerFrameObservables

theorem entropy_continuousOn (m : ℕ) (hm : 4 ≤ m) : ContinuousOn (entropy m) (interior m) :=
  KroneckerLogic.continuousOn_of_jointLimits height slope (value m)
    (entropy_joint m hm) (fun r hr => frame_approximable r hr.1)

theorem entropy_continuousAt (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    ContinuousAt (entropy m) r :=
  (entropy_continuousOn m hm r hr).continuousAt (isOpen_Ioo.mem_nhds hr)

end KroneckerInteriorEntropyContinuity
end

/- Original module: KroneckerInteriorEntropyBounds -/
section
set_option autoImplicit false
namespace KroneckerInteriorEntropyBounds
open KroneckerLogic KroneckerFrameObservables KroneckerInteriorEntropy

theorem entropy_bounds (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    Real.log (m : ℝ)/2 ≤ entropy m r ∧ entropy m r ≤ (m : ℝ)*m*Real.log 2 := by
  obtain ⟨x⟩ := approaching_nonempty height slope (frame_approximable r hr.1)
  have hlegal := KroneckerEventualFrameAlphabet.eventual_frame_alphabet
    (fun n => (x.val n).a) (fun n => (x.val n).b) (fun n => (x.val n).d) (m-1) r
    x.property.1 (fun n => (x.val n).hd) x.property.2 hr.1
    (hr.2.trans_le (by exact_mod_cast (show m-2 ≤ m-1 by omega)))
  exact KroneckerFrameLimitBounds.frame_limit_bounds m (by omega) x.val _ x.property.1 hlegal
    (jointLimit_sequence height slope (value m) (entropy_joint m hm r hr) x.val x.property.1 x.property.2)

end KroneckerInteriorEntropyBounds
end

/- Original module: KroneckerInteriorEntropyPositive -/
section
set_option autoImplicit false
namespace KroneckerInteriorEntropyPositive
open KroneckerInteriorEntropy

theorem entropy_positive (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    0 < entropy m r := by
  have h := (KroneckerInteriorEntropyBounds.entropy_bounds m hm r hr).1
  have hp : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  linarith

theorem entropy_abs_bound (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    |entropy m r| ≤ (m : ℝ)*m*Real.log 2 := by
  rw [abs_of_pos (entropy_positive m hm r hr)]
  exact (KroneckerInteriorEntropyBounds.entropy_bounds m hm r hr).2

end KroneckerInteriorEntropyPositive
end

/- Original module: KroneckerInteriorEntropySequences -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerInteriorEntropySequences
open KroneckerInteriorEntropy KroneckerFrameObservables



end KroneckerInteriorEntropySequences
end
