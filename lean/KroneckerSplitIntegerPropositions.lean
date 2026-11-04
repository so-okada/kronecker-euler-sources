import KroneckerRestrictedIntegerLimits

/-! Restricted dimensions, the integer limit and the two endpoint limits. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerSplitIntegerPropositions
open Filter KroneckerLogic KroneckerPeriodicTail
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerScopedActualFrameChoice KroneckerScopedActualFrameJointTransfer
open KroneckerManuscriptTarget
open scoped Topology

open KroneckerRestrictedIntegerLimits

theorem integer_joint (m k : ℕ) (hm : 4 ≤ m) (hk : 1 ≤ k ∧ k ≤ m-2) :
    JointLimit (fun x : RestrictedDimension m (by omega) => x.val.1)
      (fun x => (x.val.2 : ℝ)/x.val.1)
      (fun x => Real.log (euler (family KroneckerReadableMain.geometry) m
        x.val.1 x.val.2 : ℝ)/(x.val.1 : ℝ)) (k : ℝ) (periodicGrowth m [k]) :=
  KroneckerRestrictedIntegerLimits.integer_joint m k hm hk

theorem downarrow_one (m : ℕ) (hm : 4 ≤ m) :
    JointLimit (fun x : {x : Dimension (family KroneckerReadableMain.geometry) m //
        1 < slope x} => height x.val)
      (fun x => slope x.val) (fun x => value x.val) 1 (periodicGrowth m [1]) :=
  KroneckerRestrictedIntegerLimits.downarrow_one m hm

theorem uparrow_M (m : ℕ) (hm : 4 ≤ m) :
    JointLimit (fun x : {x : Dimension (family KroneckerReadableMain.geometry) m //
        slope x < (m-2 : ℕ)} => height x.val)
      (fun x => slope x.val) (fun x => value x.val)
      (m-2 : ℕ) (periodicGrowth m [m-2]) :=
  KroneckerRestrictedIntegerLimits.uparrow_M m hm

end KroneckerSplitIntegerPropositions
#print axioms KroneckerSplitIntegerPropositions.integer_joint
#print axioms KroneckerSplitIntegerPropositions.downarrow_one
#print axioms KroneckerSplitIntegerPropositions.uparrow_M
