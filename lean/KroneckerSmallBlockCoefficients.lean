import KroneckerNaturalQuotientBound

set_option autoImplicit false
namespace KroneckerSmallBlockCoefficients
open KroneckerNaturalQuotientBound

theorem small_block_coefficients (η : ℝ) (hη : 0 < η) :
    ∃ q : ℕ, 0 < q ∧ ∀ Q : ℕ, ∃ L : ℕ, 0 < L ∧
      (Q : ℝ)/(L : ℝ) < η/4 ∧ ((2*(L/q+1) : ℕ) : ℝ)/(L : ℝ) < η/4 := by
  obtain ⟨q,hq⟩ := exists_nat_gt (16/η)
  have hqR : (0 : ℝ) < q := lt_trans (by positivity) hq
  have hqN : 0 < q := by exact_mod_cast hqR
  have hqη : 16 < (q : ℝ)*η := (div_lt_iff₀ hη).mp hq
  refine ⟨q,hqN,?_⟩
  intro Q
  obtain ⟨L,hL⟩ := exists_nat_gt (max (q : ℝ) (4*(Q : ℝ)/η))
  have hqL : (q : ℝ) < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hLQ : 4*(Q : ℝ)/η < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hLR : (0 : ℝ) < L := hqR.trans hqL
  refine ⟨L,by exact_mod_cast hLR,?_,?_⟩
  · apply (div_lt_iff₀ hLR).mpr
    have h := (div_lt_iff₀ hη).mp hLQ
    nlinarith
  · have hd := natural_quotient_bound L q hqN
    have hd1 : (1 : ℝ) ≤ (L : ℝ)/(q : ℝ) := (le_div_iff₀ hqR).mpr (by linarith)
    have hb : ((2*(L/q+1) : ℕ) : ℝ) ≤ 4*((L : ℝ)/(q : ℝ)) := by
      push_cast
      linarith
    have hfrac : ((2*(L/q+1) : ℕ) : ℝ)/(L : ℝ) ≤ 4/(q : ℝ) := by
      apply (div_le_iff₀ hLR).mpr
      convert hb using 1
      ring
    exact hfrac.trans_lt ((div_lt_iff₀ hqR).mpr (by nlinarith))

end KroneckerSmallBlockCoefficients
