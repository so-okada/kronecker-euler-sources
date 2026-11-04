import KroneckerReadableMain

set_option autoImplicit false

namespace KroneckerManuscriptCorollaries
noncomputable section
open KroneckerManuscriptTarget KroneckerLogic KroneckerScopedCanonicalPublishedEuler
open KroneckerReadableMain KroneckerEndpointRoots KroneckerAdjacentFormulaValue Filter
open scoped Topology

def profile (m : ℕ) (hm : 3 ≤ m) : ℝ → ℝ :=
  KroneckerScopedDeleteMainAssembly.profile geometry localization adjacent counting m hm

theorem profile_joint (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interval m) :
    JointLimit (height (M := family geometry) (m := m)) slope value r (profile m hm r) :=
  KroneckerScopedDeleteMainAssembly.joint geometry localization adjacent counting m hm r hr

theorem profile_positive (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    0 < profile m hm r :=
  KroneckerScopedDeleteMainAssembly.positive geometry localization adjacent counting m hm r hr

theorem profile_continuous (m : ℕ) (hm : 3 ≤ m) : ContinuousOn (profile m hm) (interval m) :=
  continuousOn_of_jointLimits _ _ _ (profile_joint m hm) (slope_approximable m hm)

/-- Lemma 6.6: choose a sequence in the manuscript's dimension domain at each slope. -/
theorem dimension_sequence (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interval m) :
    ∃ x : ℕ → Dimension (family geometry) m,
      Tendsto (fun n => height (x n)) atTop atTop ∧
      Tendsto (fun n => slope (x n)) atTop (𝓝 r) := by
  obtain ⟨x⟩ := approaching_nonempty _ _ (slope_approximable m hm r hr)
  exact ⟨x.val, x.property⟩

def adjacentDimension (m : ℕ) (hm : 3 ≤ m) (n : ℕ) : Dimension (family geometry) m :=
  ⟨(n + 1, n + 1 + 1), by
    refine ⟨by omega, by omega, ?_, ?_⟩
    · simp [Nat.coprime_self_add_right]
    · apply (nonempty_domain m hm (n + 1) (n + 1 + 1) (by omega) (by omega)
        (by simp [Nat.coprime_self_add_right])).mpr
      have hm' : (3 : ℤ) ≤ m := by exact_mod_cast hm
      have hn : (0 : ℤ) ≤ n := by positivity
      push_cast
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ m - 3 by omega)
        (show (0 : ℤ) ≤ (n + 1) * (n + 1 + 1) by positivity)]⟩

theorem adjacentDimension_height (m : ℕ) (hm : 3 ≤ m) :
    Tendsto (fun n => height (adjacentDimension m hm n)) atTop atTop :=
  tendsto_add_atTop_nat 1

theorem adjacentDimension_slope (m : ℕ) (hm : 3 ≤ m) :
    Tendsto (fun n => slope (adjacentDimension m hm n)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
    tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [add_zero] at h
  apply h.congr
  intro n
  change 1 + 1 / ((n : ℝ) + 1) = (((n + 1 + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
  push_cast
  field_simp

theorem profile_central_value (m : ℕ) (hm : 3 ≤ m) :
    profile m hm 1 = centralValue m := by
  have hm' : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  have h1 : (1 : ℝ) ∈ interval m :=
    ⟨(lowerRoot_lt_one hm').le, (one_lt_upperRoot hm').le⟩
  have h := jointLimit_sequence _ _ _ (profile_joint m hm 1 h1)
    (adjacentDimension m hm) (adjacentDimension_height m hm) (adjacentDimension_slope m hm)
  have ha := (KroneckerScopedPublishedAdjacent.adjacent_limit geometry adjacent m hm).comp
    (tendsto_add_atTop_nat 1)
  apply tendsto_nhds_unique h
  simpa only [Function.comp_def, value, adjacentDimension] using ha

theorem central_joint_limit (m : ℕ) (hm : 3 ≤ m) :
    JointLimit (height (M := family geometry) (m := m)) slope value 1 (centralValue m) := by
  have hm' : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  rw [← profile_central_value m hm]
  exact profile_joint m hm 1 ⟨(lowerRoot_lt_one hm').le, (one_lt_upperRoot hm').le⟩

/-- Corollary 9.1: the limit for an explicitly indexed sequence in `A₃`. -/
theorem central_sequence (x : ℕ → Dimension (family geometry) 3)
    (ha : Tendsto (fun n => height (x n)) atTop atTop)
    (hr : Tendsto (fun n => slope (x n)) atTop (𝓝 1)) :
    Tendsto (fun n => value (x n)) atTop (𝓝 (Real.log (256 / 27 : ℝ))) := by
  have h := jointLimit_sequence _ _ _ (central_joint_limit 3 (by omega)) x ha hr
  simpa only [KroneckerCentralValueThree.central_value_three] using h

theorem central_value_formula (m : ℕ) (hm : 3 ≤ m) :
    profile m hm 1 =
      ((m : ℝ) - 1) ^ 2 * Real.log (((m : ℝ) - 1) ^ 2) -
      ((m : ℝ) * ((m : ℝ) - 2)) * Real.log ((m : ℝ) * ((m : ℝ) - 2)) := by
  rw [profile_central_value]
  simp only [centralValue, KroneckerAdjacentParameters.binomialSlope]
  have hA : (((m - 1) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - 1) ^ 2 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega), Nat.cast_one]
  rw [hA]
  simp only [Nat.cast_mul, Nat.cast_sub (show 2 ≤ m by omega), Nat.cast_ofNat]

end
end KroneckerManuscriptCorollaries
