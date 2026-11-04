import KroneckerPeriodicWords
import KroneckerWordBounds
import KroneckerAsymptotics

section

/-! Quantitative positive bounds on the actual periodic colored counts. -/
set_option autoImplicit false
namespace KroneckerPeriodicBounds
open KroneckerWordCounts KroneckerWordBounds KroneckerPeriodicWords

theorem periodicCount_lower (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) (hj : 1 ≤ j) :
    m ^ ((j * W.length+1)/2) ≤ periodicCount m W j := by
  simpa only [periodicCount, repeatRuns_length] using
    runCount_lower_bound m hm (repeatRuns W j) (repeatRuns_ne_nil W hne j hj)
      (fun r h => hr r (mem_repeatRuns W j h))

theorem periodicCount_upper (m : ℕ) (hm : 3 ≤ m) (W : List ℕ)
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) :
    periodicCount m W j ≤ 2 ^ (m * m * W.length * j) := by
  have h := runCount_upper_bound m (m-1) 0 (repeatRuns W j)
    (fun r h => (hr r (mem_repeatRuns W j h)).2)
  have he : m-1+1 = m := by omega
  calc
    periodicCount m W j ≤ 2 ^ (m * (m-1+1) * (repeatRuns W j).length) := h
    _ = 2 ^ (m * m * W.length * j) := by
      rw [repeatRuns_length, he]
      congr 1
      ring

theorem m_le_periodicCount (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) (hj : 1 ≤ j) :
    m ≤ periodicCount m W j := by
  have hlen : 0 < W.length := List.length_pos_iff.mpr hne
  have hmul : 0 < j * W.length := Nat.mul_pos (by omega) hlen
  have hexp : 1 ≤ (j * W.length+1)/2 := by omega
  calc
    m = m^1 := by simp
    _ ≤ m ^ ((j * W.length+1)/2) := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ periodicCount m W j := periodicCount_lower m hm W hne hr j hj

theorem periodicCount_pos (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) (hj : 1 ≤ j) :
    0 < periodicCount m W j :=
  lt_of_lt_of_le (by omega : 0 < m) (m_le_periodicCount m hm W hne hr j hj)

end KroneckerPeriodicBounds
end

section

/- Original module: KroneckerPeriodicLog -/
section
/-! Logarithmic inequalities for the actual positive periodic count sequence. -/
set_option autoImplicit false
namespace KroneckerPeriodicLog
open KroneckerPeriodicWords KroneckerPeriodicBounds

noncomputable def periodicLog (m : ℕ) (W : List ℕ) (j : ℕ) : ℝ :=
  Real.log (periodicCount m W j : ℝ)

noncomputable def logUpperConstant (m : ℕ) (W : List ℕ) : ℝ :=
  ((m * m * W.length : ℕ) : ℝ) * Real.log 2

theorem logUpperConstant_nonneg (m : ℕ) (W : List ℕ) :
    0 ≤ logUpperConstant m W := by
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))

theorem periodicLog_pos (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) (hj : 1 ≤ j) :
    0 < periodicLog m W j := by
  apply Real.log_pos
  have h := m_le_periodicCount m hm W hne hr j hj
  exact_mod_cast (show 1 < periodicCount m W j from by omega)

theorem periodicLog_superadditive (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    periodicLog m W i + periodicLog m W j ≤ periodicLog m W (i+j+2) := by
  have hi' : 0 < (periodicCount m W i : ℝ) := by
    exact_mod_cast periodicCount_pos m hm W hne hr i hi
  have hj' : 0 < (periodicCount m W j : ℝ) := by
    exact_mod_cast periodicCount_pos m hm W hne hr j hj
  unfold periodicLog
  rw [← Real.log_mul (ne_of_gt hi') (ne_of_gt hj')]
  apply Real.log_le_log (mul_pos hi' hj')
  exact_mod_cast periodicCount_supermultiplicative m hm W hne hr i j

theorem periodicLog_upper (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) (hj : 1 ≤ j) :
    periodicLog m W j ≤ logUpperConstant m W * (j : ℝ) := by
  have hp : 0 < (periodicCount m W j : ℝ) := by
    exact_mod_cast periodicCount_pos m hm W hne hr j hj
  have hc : (periodicCount m W j : ℝ) ≤ (2 : ℝ) ^ (m * m * W.length * j) := by
    exact_mod_cast periodicCount_upper m hm W hr j
  have h := Real.log_le_log hp hc
  rw [Real.log_pow] at h
  calc
    periodicLog m W j ≤ ((m * m * W.length * j : ℕ) : ℝ) * Real.log 2 := h
    _ = logUpperConstant m W * (j : ℝ) := by
      simp only [logUpperConstant, Nat.cast_mul]
      ring

end KroneckerPeriodicLog
end

/- Original module: KroneckerPeriodicTail -/
section
/-! Verification of every tail-Fekete hypothesis for the concrete periodic counts. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPeriodicTail
open KroneckerPeriodicLog KroneckerAsymptotics

noncomputable def shiftedLog (m : ℕ) (W : List ℕ) (n : ℕ) : ℝ :=
  periodicLog m W (n-2)

noncomputable def growthSet (m : ℕ) (W : List ℕ) : Set ℝ :=
  (fun n : ℕ => shiftedLog m W n / (n : ℝ)) '' Set.Ici 3

noncomputable def periodicGrowth (m : ℕ) (W : List ℕ) : ℝ :=
  sSup (growthSet m W)

theorem shiftedLog_superadditive (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) : TailSuperadditive (shiftedLog m W) := by
  intro i hi j hj
  have h := periodicLog_superadditive m hm W hne hr (i-2) (j-2) (by omega) (by omega)
  have he : i-2+(j-2)+2 = (i+j)-2 := by omega
  simpa only [shiftedLog, he] using h

theorem shiftedLog_nonneg (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ shiftedLog m W n :=
  (periodicLog_pos m hm W hne hr (n-2) (by omega)).le

theorem shiftedLog_upper (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (n : ℕ) (hn : 3 ≤ n) :
    shiftedLog m W n ≤ logUpperConstant m W * (n : ℝ) := by
  have h := periodicLog_upper m hm W hne hr (n-2) (by omega)
  exact h.trans (mul_le_mul_of_nonneg_left
    (by exact_mod_cast Nat.sub_le n 2) (logUpperConstant_nonneg m W))

theorem growthSet_nonempty (m : ℕ) (W : List ℕ) : (growthSet m W).Nonempty := by
  exact ⟨_, 3, by simp, rfl⟩

theorem growthSet_bddAbove (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) : BddAbove (growthSet m W) := by
  refine ⟨logUpperConstant m W, ?_⟩
  rintro x ⟨n, hn, rfl⟩
  have hn' : 3 ≤ n := hn
  exact (div_le_iff₀ (by exact_mod_cast (show 0 < n from by omega))).mpr
    (shiftedLog_upper m hm W hne hr n hn')

theorem shiftedLog_limit (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) :
    Tendsto (fun n : ℕ => shiftedLog m W n / (n : ℝ)) atTop
      (𝓝 (periodicGrowth m W)) := by
  exact tail_fekete (shiftedLog_superadditive m hm W hne hr)
    (shiftedLog_nonneg m hm W hne hr) (logUpperConstant m W)
    (shiftedLog_upper m hm W hne hr)

end KroneckerPeriodicTail
end

/- Original module: KroneckerPeriodicLimit -/
section
/-! Transport the concrete tail limit to the manuscript normalization log A_j / j. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPeriodicLimit
open KroneckerPeriodicLog KroneckerPeriodicTail

theorem periodicLog_shifted_limit (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) :
    Tendsto (fun j : ℕ => periodicLog m W j / ((j : ℝ)+2)) atTop
      (𝓝 (periodicGrowth m W)) := by
  have h := (shiftedLog_limit m hm W hne hr).comp (tendsto_add_atTop_nat 2)
  simpa [Function.comp_def, shiftedLog, Nat.cast_add] using h

theorem denominator_ratio_limit :
    Tendsto (fun j : ℕ => ((j : ℝ)+2)/(j : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have hz : Tendsto (fun j : ℕ => (2 : ℝ)/(j : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h : Tendsto (fun j : ℕ => (1 : ℝ)+2/(j : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hz
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 from by omega)
  field_simp

theorem periodicLog_limit (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) :
    Tendsto (fun j : ℕ => periodicLog m W j / (j : ℝ)) atTop
      (𝓝 (periodicGrowth m W)) := by
  have hb : ∀ᶠ j : ℕ in atTop, (j : ℝ)+2 ≠ 0 :=
    Eventually.of_forall (fun j => by positivity)
  have h := KroneckerLogic.normalization_transport
    (a := fun j : ℕ => (j : ℝ)) (b := fun j : ℕ => (j : ℝ)+2)
    (V := periodicLog m W) 1 (periodicGrowth m W) hb denominator_ratio_limit
    (periodicLog_shifted_limit m hm W hne hr)
  simpa only [one_mul] using h

end KroneckerPeriodicLimit
end
end

