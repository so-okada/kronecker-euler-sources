import KroneckerLowerEntropyKernel

/-! Sorting dimensions removes the one-sided central restriction without
assuming that a sequence eventually stays on either side of the diagonal. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralSortedDimensions
open Filter
open scoped Topology

def lo (a b : ℕ) := min a b
def gap (a b : ℕ) := max a b - min a b

theorem lo_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 0 < lo a b := lt_min ha hb

theorem gap_add (a b : ℕ) : lo a b + gap a b = max a b := by
  unfold lo gap
  omega

theorem coprime_sorted {a b : ℕ} (hc : a.Coprime b) : (lo a b).Coprime (max a b) := by
  rcases le_total a b with h | h
  · simpa [lo, min_eq_left h, max_eq_right h] using hc
  · simpa [lo, min_eq_right h, max_eq_left h] using hc.symm

theorem coprime_gap {a b : ℕ} (hc : a.Coprime b) : (lo a b).Coprime (gap a b) :=
  (Nat.coprime_sub_self_right (min_le_max)).mpr (coprime_sorted hc)

theorem diagonal_coprime {a b : ℕ} (hc : a.Coprime b) (h : a = b) : a = 1 := by
  subst b
  simpa using hc

theorem gap_pos_of_primitive {a b : ℕ} (ha : 1 < a) (hc : a.Coprime b) : 0 < gap a b := by
  have hn : a ≠ b := fun h => by have := diagonal_coprime hc h; omega
  unfold gap
  omega

theorem lo_ratio {a b : ℕ} (ha : 0 < a) :
    (lo a b : ℝ)/a = min 1 ((b : ℝ)/a) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  rcases le_total a b with h | h
  · rw [lo, min_eq_left h, div_self hap.ne', min_eq_left]
    exact (le_div_iff₀ hap).mpr (by simpa using (show (a : ℝ) ≤ b by exact_mod_cast h))
  · rw [lo, min_eq_right h, min_eq_right]
    exact (div_le_one hap).mpr (by exact_mod_cast h)

theorem gap_ratio {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (gap a b : ℝ)/lo a b = |(b : ℝ)/a-1| / min 1 ((b : ℝ)/a) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  rcases le_total a b with h | h
  · have hR : (a : ℝ) ≤ b := by exact_mod_cast h
    have hd : 1 ≤ (b : ℝ)/a := (le_div_iff₀ hap).mpr (by simpa using hR)
    simp only [gap, lo, min_eq_left h, max_eq_right h, Nat.cast_sub h,
      min_eq_left hd, abs_of_nonneg (sub_nonneg.mpr hd), div_one]
    field_simp
  · have hR : (b : ℝ) ≤ a := by exact_mod_cast h
    have hd : (b : ℝ)/a ≤ 1 := (div_le_one hap).mpr hR
    simp only [gap, lo, min_eq_right h, max_eq_left h, Nat.cast_sub h,
      min_eq_right hd, abs_of_nonpos (sub_nonpos.mpr hd)]
    field_simp
    ring

variable {α : Type*} {l : Filter α} (a b : α → ℕ)

theorem lo_ratio_tendsto (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 1)) :
    Tendsto (fun i => (lo (a i) (b i) : ℝ)/a i) l (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).min hs
  simp only [min_self] at h
  apply h.congr'
  exact (KroneckerLowerEntropyKernel.eventually_positive a ha).mono fun i hi => (lo_ratio hi).symm

theorem lo_tendsto (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 1)) :
    Tendsto (fun i => (lo (a i) (b i) : ℝ)) l atTop := by
  have h := ha.atTop_mul_pos (by norm_num : (0:ℝ)<1) (lo_ratio_tendsto a b ha hs)
  apply h.congr'
  filter_upwards [KroneckerLowerEntropyKernel.eventually_positive a ha] with i hi
  have hip : (a i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  field_simp

theorem gap_ratio_tendsto (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 1))
    (hb : ∀ᶠ i in l, 0 < b i) :
    Tendsto (fun i => (gap (a i) (b i) : ℝ)/lo (a i) (b i)) l (𝓝 0) := by
  have hn := (hs.sub_const 1).abs
  have hd := (tendsto_const_nhds : Tendsto (fun _ : α => (1:ℝ)) l (𝓝 1)).min hs
  have h := hn.div hd (by norm_num : min (1:ℝ) 1 ≠ 0)
  simp only [sub_self, abs_zero, min_self, zero_div] at h
  apply h.congr'
  filter_upwards [KroneckerLowerEntropyKernel.eventually_positive a ha, hb] with i hi hbi
  exact (gap_ratio hi hbi).symm

theorem eventually_primitive (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hc : ∀ᶠ i in l, (a i).Coprime (b i)) :
    ∀ᶠ i in l, 0 < gap (a i) (b i) ∧ (lo (a i) (b i)).Coprime (gap (a i) (b i)) := by
  filter_upwards [ha.eventually_gt_atTop 1, hc] with i hi hci
  have hi' : 1 < a i := by exact_mod_cast hi
  exact ⟨gap_pos_of_primitive hi' hci, coprime_gap hci⟩

end KroneckerCentralSortedDimensions
