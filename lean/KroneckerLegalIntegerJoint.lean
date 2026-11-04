import KroneckerInteriorEntropySequences

/- Original module: KroneckerLegalFrameDomain -/
section
set_option autoImplicit false
namespace KroneckerLegalFrameDomain
open KroneckerFrameBadDensity KroneckerInteriorEntropy

def LegalFramePoint (m : ℕ) :=
  {x : KroneckerFrameObservables.FramePoint // ∀ r ∈ frameWord x.a x.b x.d, 1 ≤ r ∧ r ≤ m-2}

def height {m : ℕ} (x : LegalFramePoint m) : ℕ := x.val.a
noncomputable def slope {m : ℕ} (x : LegalFramePoint m) : ℝ := KroneckerFrameObservables.slope x.val
noncomputable def value {m : ℕ} (x : LegalFramePoint m) : ℝ := KroneckerFrameObservables.value m x.val

theorem interior_legal_frame_joint (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    KroneckerLogic.JointLimit (height (m:=m)) slope value r (entropy m r) := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := entropy_joint m hm r hr ε hε
  exact ⟨δ,hδ,N,fun x hx hs => hN x.val hx hs⟩

end KroneckerLegalFrameDomain
end

/- Original module: KroneckerLegalIntegerJoint -/
section
set_option autoImplicit false
namespace KroneckerLegalIntegerJoint
open KroneckerLegalFrameDomain KroneckerPeriodicTail

theorem legal_integer_joint (m k : ℕ) (hm : 4 ≤ m) (hk : 1 ≤ k ∧ k ≤ m-2) :
    KroneckerLogic.JointLimit (height (m:=m)) slope value (k : ℝ) (periodicGrowth m [k]) := by
  apply KroneckerLogic.jointLimit_of_sequences (height (m:=m)) slope value
  intro x ha hs
  exact KroneckerLiteralIntegerLimit.literal_integer_limit m k hm hk
    (fun n => (x n).val.a) (fun n => (x n).val.b) (fun n => (x n).val.d) ha
    (fun n => (x n).val.hd) hs (Filter.Eventually.of_forall (fun n => (x n).property))

end KroneckerLegalIntegerJoint
end
