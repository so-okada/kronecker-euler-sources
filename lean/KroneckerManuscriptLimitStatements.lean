import KroneckerScopedActualFrameJointTransfer
import KroneckerReadableMain

set_option autoImplicit false
noncomputable section

namespace KroneckerManuscriptLimitStatements
open Filter KroneckerLogic KroneckerPeriodicTail KroneckerRationalWordRotation
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerScopedActualFrameApplication KroneckerScopedActualFrameChoice
open KroneckerScopedActualFrameJointTransfer
open scoped Topology

theorem rational_euler_joint (m p q : ℕ) (hm : 3 ≤ m) (hq : 1 < q)
    (hc : p.Coprime q) (hlo : 1 < (p : ℝ) / q)
    (hhi : (p : ℝ) / q < (m - 1 : ℕ)) :
    JointLimit (KroneckerEulerObservables.height (m := m))
      KroneckerEulerObservables.slope KroneckerEulerObservables.value
      ((p : ℝ) / q) (periodicGrowth m (rationalPeriod p q) / q) := by
  apply jointLimit_of_sequences
  intro x ha hs
  apply KroneckerLiteralEulerLimitTransfer.literal_euler_limit_transfer m hm x _ ha
  · exact KroneckerEventualFrameAlphabet.eventual_frame_alphabet
      (fun n => (x n).P.a) (fun n => (x n).P.b) (fun n => (x n).P.d₁)
      (m - 1) _ ha (fun n => (KroneckerEulerFramePositivity.toFrame (x n)).hd)
      hs hlo hhi
  · exact KroneckerFullFrameLimit.full_frame_limit m p q hm hq hc hlo hhi
      (fun n => (x n).P.a) (fun n => (x n).P.b) (fun n => (x n).P.d₁)
      ha (fun n => (KroneckerEulerFramePositivity.toFrame (x n)).hd) hs

theorem rational_actual_joint (G : Geometry) (A : Application G)
    (m p q : ℕ) (hm : 3 ≤ m) (hq : 1 < q) (hc : p.Coprime q)
    (hlo : 1 < (p : ℝ) / q) (hhi : (p : ℝ) / q < (m - 1 : ℕ)) :
    JointLimit (KroneckerManuscriptTarget.height (M := family G) (m := m))
      KroneckerManuscriptTarget.slope KroneckerManuscriptTarget.value
      ((p : ℝ) / q) (periodicGrowth m (rationalPeriod p q) / q) :=
  joint_to_actual G A m hm _ _ hlo (rational_euler_joint m p q hm hq hc hlo hhi)

theorem integer_euler_sequence (m k : ℕ) (hm : 4 ≤ m)
    (hk : 1 ≤ k ∧ k ≤ m - 2) (x : ℕ → KroneckerEulerObservables.EulerPoint m)
    (ha : Tendsto (fun n => (x n).P.a) atTop atTop)
    (hs : Tendsto (fun n => KroneckerEulerObservables.slope (x n)) atTop (𝓝 (k : ℝ)))
    (hl : ∀ᶠ n in atTop, ∀ r ∈ KroneckerFrameBadDensity.frameWord
      (x n).P.a (x n).P.b (x n).P.d₁, 1 ≤ r ∧ r ≤ m - 2) :
    Tendsto (fun n => KroneckerEulerObservables.value (x n)) atTop
      (𝓝 (periodicGrowth m [k])) := by
  apply KroneckerLiteralEulerLimitTransfer.literal_euler_limit_transfer m (by omega) x _ ha
  · exact hl.mono (fun n hn r hr => ⟨(hn r hr).1, by have := (hn r hr).2; omega⟩)
  · exact KroneckerLiteralIntegerLimit.literal_integer_limit m k hm hk
      (fun n => (x n).P.a) (fun n => (x n).P.b) (fun n => (x n).P.d₁)
      ha (fun n => (KroneckerEulerFramePositivity.toFrame (x n)).hd) hs hl

theorem integer_actual_sequence (G : Geometry) (A : Application G)
    (m k : ℕ) (hm : 4 ≤ m) (hk : 1 ≤ k ∧ k ≤ m - 2) (x : ℕ → Input m)
    (ha : Tendsto (fun n => (x n).a) atTop atTop)
    (hs : Tendsto (fun n => inputSlope (x n)) atTop (𝓝 (k : ℝ)))
    (hl : ∀ᶠ n in atTop, ∀ r ∈ KroneckerFrameBadDensity.frameWord
      (x n).a (x n).b (parameters m (by omega) (x n)).d₁,
      1 ≤ r ∧ r ≤ m - 2) :
    Tendsto (fun n => inputValue G (x n)) atTop (𝓝 (periodicGrowth m [k])) := by
  have h := integer_euler_sequence m k hm hk
    (fun n => toEuler G A m (by omega) (x n))
    (by
      change Tendsto (fun n => KroneckerEulerObservables.height
        (toEuler G A m (by omega) (x n))) atTop atTop
      simpa only [toEuler_height] using ha)
    (by simp only [toEuler_slope]; exact hs) ?_
  · simp only [toEuler_value] at h
    exact h
  · filter_upwards [hl] with n hn
    simpa only [toEuler, (parameters_spec m (by omega) (x n)).2.1,
      (parameters_spec m (by omega) (x n)).2.2] using hn

theorem irrational_actual_joint (G : Geometry) (A : Application G)
    (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : 1 < r ∧ r < (m - 2 : ℕ)) :
    JointLimit (KroneckerManuscriptTarget.height (M := family G) (m := m))
      KroneckerManuscriptTarget.slope KroneckerManuscriptTarget.value r
      (KroneckerClosedAlphabetEntropy.entropy m r) :=
  interior_joint G A m hm r hr

theorem rational_manuscript (m p q : ℕ) (hm : 3 ≤ m) (hq : 1 < q)
    (hc : p.Coprime q) (hlo : 1 < (p : ℝ) / q)
    (hhi : (p : ℝ) / q < (m - 1 : ℕ)) :
    JointLimit
      (KroneckerManuscriptTarget.height (M := family KroneckerReadableMain.geometry) (m := m))
      KroneckerManuscriptTarget.slope KroneckerManuscriptTarget.value
      ((p : ℝ) / q) (periodicGrowth m (rationalPeriod p q) / q) :=
  rational_actual_joint KroneckerReadableMain.geometry KroneckerReadableMain.counting
    m p q hm hq hc hlo hhi

end KroneckerManuscriptLimitStatements

#print axioms KroneckerManuscriptLimitStatements.rational_manuscript
#print axioms KroneckerManuscriptLimitStatements.integer_actual_sequence
#print axioms KroneckerManuscriptLimitStatements.irrational_actual_joint
