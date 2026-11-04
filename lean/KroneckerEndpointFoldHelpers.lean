import KroneckerApproachingDimensionReduction

/-! Explicit neighborhoods and formulas for endpoint folding. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace KroneckerEndpointFoldHelpers

def radius (m ρ : ℝ) : ℝ :=
  if ρ = 1 then (m-2)/(2*m)
  else if ρ = m/2 then (m-2)/4
  else min (ρ-1) (m/2-ρ)/2

def scale (ρ t : ℝ) : ℝ := if ρ = 1 then min 1 t else 1

def foldedSlope (m ρ t : ℝ) : ℝ :=
  if ρ = 1 then max t t⁻¹ else if ρ = m/2 then min t (m-t) else t

theorem radius_pos (m ρ : ℝ) (hm : 2 < m) (hρ : ρ ∈ Set.Icc 1 (m/2)) :
    0 < radius m ρ := by
  unfold radius
  split_ifs with h1 h2
  · exact div_pos (by linarith) (by positivity)
  · exact div_pos (by linarith) (by norm_num)
  · have hleft : 0 < ρ-1 := by
      rcases lt_or_eq_of_le hρ.1 with h | h
      · linarith
      · exact (h1 h.symm).elim
    have hright : 0 < m/2-ρ := by
      rcases lt_or_eq_of_le hρ.2 with h | h
      · linarith
      · exact (h2 h).elim
    exact div_pos (lt_min hleft hright) (by norm_num)

theorem lower_neighborhood (m t : ℝ) (hm : 2 < m)
    (ht : |t-1| < (m-2)/(2*m)) :
    2/m < t ∧ t < m/2 := by
  have hm0 : 0 < m := by linarith
  have h := abs_lt.mp ht
  have hd : (m-2)/(2*m)*(2*m) = m-2 := div_mul_cancel₀ _ (by positivity)
  have h₁ := mul_lt_mul_of_pos_right h.1 (show 0 < 2*m by positivity)
  have h₂ := mul_lt_mul_of_pos_right h.2 (show 0 < 2*m by positivity)
  constructor
  · apply (div_lt_iff₀ hm0).mpr
    nlinarith
  · have hp : 0 < (m-1)*(m-2) := mul_pos (by linarith) (by linarith)
    nlinarith

theorem upper_neighborhood (m t : ℝ) (hm : 2 < m)
    (ht : |t-m/2| < (m-2)/4) : 1 < t ∧ t < m-1 := by
  have h := abs_lt.mp ht
  constructor <;> linarith

theorem interior_neighborhood (m ρ t : ℝ) (hρ : 1 < ρ ∧ ρ < m/2)
    (ht : |t-ρ| < min (ρ-1) (m/2-ρ)/2) : 1 < t ∧ t < m/2 := by
  have h := abs_lt.mp ht
  have h₁ := min_le_left (ρ-1) (m/2-ρ)
  have h₂ := min_le_right (ρ-1) (m/2-ρ)
  constructor <;> linarith [hρ.1, hρ.2]

theorem max_inverse_bounds (m t : ℝ) (hm : 2 < m)
    (ht : 2/m < t ∧ t < m/2) : 0 < t ∧ 1 ≤ max t t⁻¹ ∧ max t t⁻¹ < m/2 := by
  have hm0 : 0 < m := by linarith
  have ht0 : 0 < t := (div_pos (by norm_num) hm0).trans ht.1
  have hi : t⁻¹ < m/2 := by
    rw [← one_div]
    apply (div_lt_iff₀ ht0).mpr
    have hmul := (div_lt_iff₀ hm0).mp ht.1
    nlinarith
  refine ⟨ht0, ?_, max_lt ht.2 hi⟩
  by_cases h : 1 ≤ t
  · exact h.trans (le_max_left _ _)
  · exact ((one_le_inv₀ ht0).mpr (by linarith)).trans (le_max_right _ _)

theorem case_bounds_and_formula (m ρ t : ℝ) (hm : 2 < m)
    (hρ : ρ ∈ Set.Icc 1 (m/2)) (ht : |t-ρ| < radius m ρ) :
    0 < t ∧ 1 ≤ foldedSlope m ρ t ∧ foldedSlope m ρ t ≤ m/2 ∧
    min t 1 = scale ρ t ∧
    min (max t t⁻¹) (m-max t t⁻¹) = foldedSlope m ρ t := by
  by_cases h1 : ρ = 1
  · subst ρ
    have hn := lower_neighborhood m t hm (by simpa [radius] using ht)
    obtain ⟨ht0, hq1, hqm⟩ := max_inverse_bounds m t hm hn
    refine ⟨ht0, ?_, ?_, ?_, ?_⟩
    · simpa [foldedSlope] using hq1
    · simpa [foldedSlope] using hqm.le
    · simp [scale, min_comm]
    · simp only [foldedSlope, ↓reduceIte]
      exact min_eq_left (by linarith)
  · by_cases h2 : ρ = m/2
    · subst ρ
      have hn := upper_neighborhood m t hm (by simpa [radius, h1] using ht)
      have ht0 : 0 < t := by linarith [hn.1]
      have hmax : max t t⁻¹ = t := max_eq_left
        (((inv_le_one₀ ht0).mpr hn.1.le).trans hn.1.le)
      refine ⟨ht0, ?_, ?_, ?_, ?_⟩
      · simp only [foldedSlope, ite_eq_right h1, ↓reduceIte]
        exact le_min hn.1.le (by linarith [hn.2])
      · simp only [foldedSlope, ite_eq_right h1, ↓reduceIte]
        by_cases ht' : t ≤ m/2
        · exact (min_le_left _ _).trans ht'
        · exact (min_le_right _ _).trans (by linarith)
      · simp [scale, h1, min_eq_right hn.1.le]
      · simp [foldedSlope, h1, hmax]
    · have hρ' : 1 < ρ ∧ ρ < m/2 := by
        constructor
        · rcases lt_or_eq_of_le hρ.1 with h | h
          · exact h
          · exact (h1 h.symm).elim
        · rcases lt_or_eq_of_le hρ.2 with h | h
          · exact h
          · exact (h2 h).elim
      have hn := interior_neighborhood m ρ t hρ' (by simpa [radius, h1, h2] using ht)
      have ht0 : 0 < t := by linarith [hn.1]
      have hmax : max t t⁻¹ = t := max_eq_left
        (((inv_le_one₀ ht0).mpr hn.1.le).trans hn.1.le)
      refine ⟨ht0, ?_, ?_, ?_, ?_⟩
      · simpa [foldedSlope, h1, h2] using hn.1.le
      · simpa [foldedSlope, h1, h2] using hn.2.le
      · simp [scale, h1, min_eq_right hn.1.le]
      · simp [foldedSlope, h1, h2, hmax, min_eq_left (show t ≤ m-t by linarith [hn.2])]

theorem fold_limits (m ρ : ℝ)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 ρ)) :
    Tendsto (fun n => scale ρ (t n)) atTop (𝓝 1) ∧
    Tendsto (fun n => foldedSlope m ρ (t n)) atTop (𝓝 ρ) := by
  by_cases h1 : ρ = 1
  · subst ρ
    constructor
    · simpa [scale] using (tendsto_const_nhds.min ht :
        Tendsto (fun n => min 1 (t n)) atTop (𝓝 (min 1 1)))
    · simpa [foldedSlope] using ht.max (ht.inv₀ (by norm_num))
  · constructor
    · simpa [scale, h1] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    · by_cases h2 : ρ = m/2
      · have he : min ρ (m-ρ) = ρ := by rw [h2]; ring_nf; simp
        simpa only [foldedSlope, ite_eq_right h1, ite_eq_left h2, he] using
          ht.min ((tendsto_const_nhds : Tendsto (fun _ : ℕ => m) atTop (𝓝 m)).sub ht)
      · simpa [foldedSlope, h1, h2] using ht

open KroneckerApproachingDimensionReduction KroneckerInteriorAllowedReflection
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler

theorem actual_fold_neighborhood (H : ∀ m a b, Admissible (space m a b))
    (m : ℕ) (hm : 3 ≤ m) (ρ : ℝ) (hρ : ρ ∈ Set.Icc 1 ((m : ℝ)/2))
    (p : Interior H m) (ht : |slp H p-ρ| < radius m ρ) :
    slp H (fold H m hm p) ∈ Set.Icc 1 ((m : ℝ)/2) ∧
    eu H (fold H m hm p) = eu H p ∧
    hgt H (fold H m hm p)/hgt H p = scale ρ (slp H p) ∧
    slp H (fold H m hm p) = foldedSlope m ρ (slp H p) := by
  have hmR : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  obtain ⟨_, hlo, hhi, hscale, hslope⟩ := case_bounds_and_formula m ρ (slp H p) hmR hρ ht
  have hs : slp H (fold H m hm p) = foldedSlope m ρ (slp H p) := by
    rw [fold_slope, lower_slope]
    exact hslope
  refine ⟨by rw [hs]; exact ⟨hlo, hhi⟩, fold_euler H m hm p, ?_, hs⟩
  rw [fold_height, lower_ratio]
  exact hscale

end KroneckerEndpointFoldHelpers
