import KroneckerSplitContinuityLemmas

/-! The positive interior limit is checked before continuity. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerSplitInteriorPropositions
open KroneckerLogic KroneckerManuscriptTarget KroneckerScopedCanonicalPublishedEuler
open KroneckerReadableMain KroneckerManuscriptCorollaries

def interiorProfile (m : ℕ) (hm : 3 ≤ m) : ℝ → ℝ := profile m hm

theorem interior_limit (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    0 < interiorProfile m hm r ∧
    JointLimit (height (M:=family geometry) (m:=m)) slope value r (interiorProfile m hm r) :=
  ⟨profile_positive m hm r hr,profile_joint m hm r ⟨hr.1.le,hr.2.le⟩⟩

theorem interior_unique (m : ℕ) (hm : 3 ≤ m) (r L : ℝ) (hr : r ∈ interior m)
    (hL : JointLimit (height (M:=family geometry) (m:=m)) slope value r L) :
    L=interiorProfile m hm r := by
  by_contra hn
  have hd : 0 < dist L (interiorProfile m hm r) := dist_pos.mpr hn
  obtain ⟨d₁,hd₁,N₁,h₁⟩ := hL (dist L (interiorProfile m hm r)/3) (by positivity)
  obtain ⟨d₂,hd₂,N₂,h₂⟩ := (interior_limit m hm r hr).2
    (dist L (interiorProfile m hm r)/3) (by positivity)
  obtain ⟨x,hx,hs⟩ := slope_approximable m hm r ⟨hr.1.le,hr.2.le⟩
    (min d₁ d₂) (lt_min hd₁ hd₂) (max N₁ N₂)
  have h₁x := h₁ x ((le_max_left _ _).trans hx) (hs.trans_le (min_le_left _ _))
  have h₂x := h₂ x ((le_max_right _ _).trans hx) (hs.trans_le (min_le_right _ _))
  have ht := dist_triangle L (value x) (interiorProfile m hm r)
  rw [dist_comm L (value x)] at ht
  linarith

/-- Equation (10.7): vertex exchange on the full open root interval. -/
theorem interior_exchange (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    interiorProfile m hm r = r * interiorProfile m hm r⁻¹ := by
  have hm' : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  have hp : 0 < r := (KroneckerEndpointRoots.lowerRoot_positive hm').trans hr.1
  have hi : r⁻¹ ∈ interior m := by
    simpa [KroneckerManuscriptTarget.interior, KroneckerSlopeSymmetry.exchange] using
      KroneckerSlopeSymmetry.exchange_mem_interior hm' hr
  have h := KroneckerExchangeJointLimit.joint_exchange (finiteHomology geometry) hp
    (interior_limit m hm r hr).2
  have he := interior_unique m hm r⁻¹ _ hi h
  rw [← he]
  field_simp

/-- Equation (10.7): reflection on the full open root interval. -/
theorem interior_reflection (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    interiorProfile m hm r = interiorProfile m hm ((m : ℝ) - r) := by
  have hm' : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  have hd := KroneckerInteriorReflectionObservables.denominator_positive m hm r hr
  have hi : (m : ℝ) - r ∈ interior m := by
    simpa [KroneckerManuscriptTarget.interior, KroneckerSlopeSymmetry.reflect] using
      KroneckerSlopeSymmetry.reflect_mem_interior hm' hr
  have h := KroneckerCanonicalReflectionJointLimit.reflect (finiteHomology geometry)
    m hm r _ hr (interior_limit m hm r hr).2
  have he := KroneckerExchangeJointLimit.joint_exchange (finiteHomology geometry)
    (inv_pos.mpr hd) h
  have hj : JointLimit (height (M:=family geometry) (m:=m)) slope value
      ((m : ℝ) - r) (interiorProfile m hm r) := by
    simpa only [KroneckerScopedCanonicalPublishedEuler.family,
      inv_inv, div_inv_eq_mul, div_mul_cancel₀ _ (ne_of_gt hd)] using he
  exact interior_unique m hm _ _ hi hj

theorem interior_continuous (m : ℕ) (hm : 3 ≤ m) :
    ContinuousOn (interiorProfile m hm) (interior m) := by
  apply KroneckerSplitContinuityLemmas.continuous m (interior m) (interiorProfile m hm)
  · intro r hr
    exact (KroneckerSplitContinuityLemmas.sequential_iff_joint m r _).mpr
      (interior_limit m hm r hr).2
  · intro r hr
    exact slope_approximable m hm r ⟨hr.1.le,hr.2.le⟩

end KroneckerSplitInteriorPropositions

#print axioms KroneckerSplitInteriorPropositions.interior_limit
#print axioms KroneckerSplitInteriorPropositions.interior_continuous

#print axioms KroneckerSplitInteriorPropositions.interior_unique
#print axioms KroneckerSplitInteriorPropositions.interior_exchange
#print axioms KroneckerSplitInteriorPropositions.interior_reflection
