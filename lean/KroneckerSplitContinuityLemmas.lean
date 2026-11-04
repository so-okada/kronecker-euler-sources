import KroneckerManuscriptCorollaries

/-! The sequential condition, its neighborhood formulation and continuity.
ContinuousOn includes both endpoints of a closed interval. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace KroneckerSplitContinuityLemmas
open KroneckerLogic KroneckerManuscriptTarget KroneckerScopedCanonicalPublishedEuler
open KroneckerReadableMain

def SequentialEntropyLimit (m : ℕ) (r L : ℝ) : Prop :=
  ∀ x : ℕ → Dimension (family geometry) m,
    Tendsto (fun n => height (x n)) atTop atTop →
    Tendsto (fun n => slope (x n)) atTop (𝓝 r) →
    Tendsto (fun n => value (x n)) atTop (𝓝 L)

theorem neighborhood (m : ℕ) (r L : ℝ) (h : SequentialEntropyLimit m r L) :
    JointLimit (height (M:=family geometry) (m:=m)) slope value r L :=
  jointLimit_of_sequences _ _ _ h

theorem sequential_iff_joint (m : ℕ) (r L : ℝ) :
    SequentialEntropyLimit m r L ↔
    JointLimit (height (M:=family geometry) (m:=m)) slope value r L :=
  (jointLimit_iff_sequences _ _ _).symm

theorem continuous (m : ℕ) (J : Set ℝ) (F : ℝ → ℝ)
    (h : ∀ r ∈ J, SequentialEntropyLimit m r (F r))
    (hd : ∀ r ∈ J, Approximable (height (M:=family geometry) (m:=m)) slope r) :
    ContinuousOn F J :=
  continuousOn_of_jointLimits _ _ _ (fun r hr => neighborhood m r (F r) (h r hr)) hd

/-- A sequence with the two stated limits supplies every dimension threshold
and every slope neighborhood. -/
theorem approximable_of_sequence (m : ℕ) (r : ℝ)
    (h : ∃ x : ℕ → Dimension (family geometry) m,
      Tendsto (fun n => height (x n)) atTop atTop ∧
      Tendsto (fun n => slope (x n)) atTop (𝓝 r)) :
    Approximable (height (M := family geometry) (m := m)) slope r := by
  obtain ⟨x, ha, hr⟩ := h
  intro δ hδ N
  have hn := ha.eventually (eventually_ge_atTop N)
  have hs := (Metric.tendsto_nhds.mp hr) δ hδ
  obtain ⟨n, hN, hdist⟩ := (hn.and hs).exists
  exact ⟨x n, hN, hdist⟩

/-- Lemma 6.8(1): a positive threshold and the two explicit absolute values. -/
theorem neighborhood_explicit (m : ℕ) (r L : ℝ)
    (h : SequentialEntropyLimit m r L) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 0 < A ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ x : Dimension (family geometry) m,
        A < height x → |slope x - r| < δ → |value x - L| < ε := by
  obtain ⟨δ, hδ, N, hN⟩ := neighborhood m r L h ε hε
  refine ⟨N + 1, by omega, δ, hδ, ?_⟩
  intro x hx hs
  simpa only [Real.dist_eq] using
    hN x (by omega) (by simpa only [Real.dist_eq] using hs)

/-- Lemma 6.8(2), with existence of sequences as the second hypothesis. -/
theorem continuous_of_sequences (m : ℕ) (J : Set ℝ) (F : ℝ → ℝ)
    (h : ∀ r ∈ J, SequentialEntropyLimit m r (F r))
    (hd : ∀ r ∈ J, ∃ x : ℕ → Dimension (family geometry) m,
      Tendsto (fun n => height (x n)) atTop atTop ∧
      Tendsto (fun n => slope (x n)) atTop (𝓝 r)) : ContinuousOn F J := by
  exact continuous m J F h (fun r hr => approximable_of_sequence m r (hd r hr))

/-- Lemma 6.8(3b): the limits are taken from inside the stated closed interval. -/
theorem endpoint_limits (m : ℕ) (h₁ h₂ : ℝ) (hlt : h₁ < h₂) (F : ℝ → ℝ)
    (h : ∀ r ∈ Set.Icc h₁ h₂, SequentialEntropyLimit m r (F r))
    (hd : ∀ r ∈ Set.Icc h₁ h₂, ∃ x : ℕ → Dimension (family geometry) m,
      Tendsto (fun n => height (x n)) atTop atTop ∧
      Tendsto (fun n => slope (x n)) atTop (𝓝 r)) :
    Tendsto F (𝓝[Set.Ioc h₁ h₂] h₁) (𝓝 (F h₁)) ∧
      Tendsto F (𝓝[Set.Ico h₁ h₂] h₂) (𝓝 (F h₂)) := by
  have hF := continuous_of_sequences m (Set.Icc h₁ h₂) F h hd
  constructor
  · exact (hF.continuousWithinAt ⟨le_rfl, hlt.le⟩).mono
      (fun _ hs => ⟨hs.1.le, hs.2⟩)
  · exact (hF.continuousWithinAt ⟨hlt.le, le_rfl⟩).mono
      (fun _ hs => ⟨hs.1, hs.2.le⟩)

end KroneckerSplitContinuityLemmas

#print axioms KroneckerSplitContinuityLemmas.neighborhood
#print axioms KroneckerSplitContinuityLemmas.sequential_iff_joint
#print axioms KroneckerSplitContinuityLemmas.continuous
