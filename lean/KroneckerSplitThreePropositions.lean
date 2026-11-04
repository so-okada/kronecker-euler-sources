import KroneckerSplitContinuityLemmas

/-! Positive irrational limits precede the entropy profile and continuity. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerSplitThreePropositions
open KroneckerLogic KroneckerManuscriptTarget KroneckerScopedCanonicalPublishedEuler
open KroneckerReadableMain KroneckerManuscriptCorollaries

theorem irrational_limit (r : ℝ) (hr : r ∈ Set.Ioo 1 2) :
    ∃ L : ℝ, 0 < L ∧ JointLimit (height (M:=family geometry) (m:=3)) slope value r L :=
  KroneckerScopedActualFrameJointTransfer.three_positive geometry counting r hr

def threeProfile : ℝ → ℝ := profile 3 (by decide)

/-- Proposition 9.21, Claim 2: positivity includes rational slopes and slope one. -/
theorem threeProfile_positive (r : ℝ) (hr : r ∈ Set.Icc 1 (3/2 : ℝ)) :
    0 < threeProfile r := by
  apply profile_positive
  exact ⟨(KroneckerEndpointRoots.lowerRoot_lt_one (by norm_num : (2 : ℝ) < 3)).trans_le hr.1,
    hr.2.trans_lt (KroneckerEndpointRoots.upperRoot_gt_half (by norm_num : (2 : ℝ) < 3))⟩

theorem threeProfile_joint (r : ℝ) (hr : r ∈ Set.Icc 1 (3/2 : ℝ)) :
    JointLimit (height (M:=family geometry) (m:=3)) slope value r (threeProfile r) := by
  apply profile_joint
  exact ⟨(KroneckerEndpointRoots.lowerRoot_lt_one (by norm_num : (2 : ℝ)<3)).le.trans hr.1,
    hr.2.trans (KroneckerEndpointRoots.upperRoot_gt_half (by norm_num : (2 : ℝ)<3)).le⟩

theorem threeProfile_continuous : ContinuousOn threeProfile (Set.Icc 1 (3/2 : ℝ)) := by
  apply KroneckerSplitContinuityLemmas.continuous 3 (Set.Icc 1 (3/2 : ℝ)) threeProfile
  · intro r hr
    exact (KroneckerSplitContinuityLemmas.sequential_iff_joint 3 r _).mpr
      (threeProfile_joint r hr)
  · intro r hr
    apply slope_approximable 3 (by decide) r
    exact ⟨(KroneckerEndpointRoots.lowerRoot_lt_one (by norm_num : (2 : ℝ)<3)).le.trans hr.1,
      hr.2.trans (KroneckerEndpointRoots.upperRoot_gt_half (by norm_num : (2 : ℝ)<3)).le⟩

end KroneckerSplitThreePropositions

#print axioms KroneckerSplitThreePropositions.irrational_limit
#print axioms KroneckerSplitThreePropositions.threeProfile_positive
#print axioms KroneckerSplitThreePropositions.threeProfile_joint
#print axioms KroneckerSplitThreePropositions.threeProfile_continuous
