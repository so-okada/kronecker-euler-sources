import KroneckerFrameObservables

/- Original module: KroneckerRationalFrameJoint -/
section
/-! The established all-sequence rational theorem supplies uniform height/slope neighborhoods. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerRationalFrameJoint
open KroneckerLogic KroneckerFrameObservables KroneckerNonprimitiveFrameLimit
open KroneckerPeriodicTail KroneckerRationalWordRotation

theorem rational_frame_joint (m p q : ℕ) (hm : 3 ≤ m) (hq : 0 < q)
    (hn : ¬ q ∣ p) (hlo : 1 < (p : ℝ)/(q : ℝ))
    (hhi : (p : ℝ)/(q : ℝ) < (m-1 : ℕ)) :
    JointLimit height slope (value m) ((p : ℝ)/(q : ℝ))
      (periodicGrowth m (rationalPeriod p q)/(q : ℝ)) := by
  apply jointLimit_of_sequences
  intro x ha hr
  exact nonprimitive_frame_limit m p q hm hq hn hlo hhi
    (fun n => (x n).a) (fun n => (x n).b) (fun n => (x n).d)
    ha (fun n => (x n).hd) hr

end KroneckerRationalFrameJoint
end

/- Original module: KroneckerRationalEntropy -/
section
/-! A real-valued function on the noninteger rational interior, with proved representation independence. -/
set_option autoImplicit false
namespace KroneckerRationalEntropy
open KroneckerLogic KroneckerFrameObservables KroneckerRationalFrameJoint
open KroneckerPeriodicTail KroneckerRationalWordRotation KroneckerRationalRateInvariant

structure Witness (m : ℕ) (r : ℝ) where
  p : ℕ
  q : ℕ
  hq : 0 < q
  hn : ¬ q ∣ p
  hlo : 1 < r
  hhi : r < (m-1 : ℕ)
  eq_ratio : r = (p : ℝ)/(q : ℝ)

def rationalSlopes (m : ℕ) : Set ℝ := {r | Nonempty (Witness m r)}

noncomputable def rate (m : ℕ) (r : ℝ) : ℝ := by
  classical
  exact if h : r ∈ rationalSlopes m then
    periodicGrowth m (rationalPeriod (Classical.choice h).p (Classical.choice h).q)/
      ((Classical.choice h).q : ℝ)
  else 0

theorem rate_eq (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (w : Witness m r) :
    rate m r = periodicGrowth m (rationalPeriod w.p w.q)/(w.q : ℝ) := by
  have h : r ∈ rationalSlopes m := ⟨w⟩
  rw [rate,dite_eq_left h]
  let v := Classical.choice h
  apply rational_rate_invariant m v.p v.q w.p w.q hm v.hq w.hq
  · rw [←v.eq_ratio]; exact w.hlo.le
  · rw [←v.eq_ratio]; exact w.hhi.le
  · rw [←v.eq_ratio,←w.eq_ratio]

theorem rate_joint (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ rationalSlopes m) :
    JointLimit height slope (value m) r (rate m r) := by
  obtain ⟨w⟩ := hr
  rw [rate_eq m hm r w]
  have h := rational_frame_joint m w.p w.q hm w.hq w.hn
    (by rw [←w.eq_ratio]; exact w.hlo) (by rw [←w.eq_ratio]; exact w.hhi)
  simpa only [←w.eq_ratio] using h

end KroneckerRationalEntropy
end
