import KroneckerIrrationalIntervals

set_option autoImplicit false
namespace KroneckerBoundedRationalNeighbor
open KroneckerIrrationalIntervals KroneckerMechanicalWords KroneckerPeriodicGrowth

theorem period_rate_bound (m : ℕ) (hm : 3 ≤ m) (t : ℝ) (q : ℕ) (hq : 0 < q)
    (ht : 1 ≤ t) (htM : t ≤ (m-1 : ℕ)) :
    0 ≤ periodRate m t q ∧ periodRate m t q ≤ (m : ℝ)*m*Real.log 2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : mechanicalWord t 0 0 q ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [mechanicalWord_length,List.length_nil] at hh
    omega
  have hlegal := mechanicalWord_legal t 0 0 q (m-1) ht htM
  have hp := periodicGrowth_pos m hm (mechanicalWord t 0 0 q) hne hlegal
  have hu := periodicGrowth_upper m hm (mechanicalWord t 0 0 q) hne hlegal
  constructor
  · exact (div_pos hp hqR).le
  · apply (div_le_iff₀ hqR).mpr
    simpa only [KroneckerPeriodicLog.logUpperConstant,mechanicalWord_length,Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hu

theorem bounded_rational_neighbor (m : ℕ) (hm : 4 ≤ m) (r δ : ℝ)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) (hδ : 0 < δ) :
    ∃ t : ℝ, ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ (q : ℝ)*t=p ∧
      1 ≤ t ∧ t ≤ (m-2 : ℕ) ∧ |t-r| < δ ∧
      0 ≤ periodRate m t q ∧ periodRate m t q ≤ (m : ℝ)*m*Real.log 2 := by
  have hleft : max 1 (r-δ/2) < r := max_lt hr1 (by linarith)
  have hright : r < min ((m-2 : ℕ) : ℝ) (r+δ/2) := lt_min hrM (by linarith)
  obtain ⟨s,hslo,hshi⟩ := exists_rat_btwn (hleft.trans hright)
  have ht1 : 1 ≤ (s : ℝ) := (lt_of_le_of_lt (le_max_left _ _) hslo).le
  have htM : (s : ℝ) ≤ (m-2 : ℕ) := (lt_of_lt_of_le hshi (min_le_left _ _)).le
  have hnear : |(s : ℝ)-r| < δ := by
    have hl := lt_of_le_of_lt (le_max_right _ _) hslo
    have hu := lt_of_lt_of_le hshi (min_le_right _ _)
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hq : 0 < s.den := s.pos
  have hp : (s.den : ℝ)*(s : ℝ)=(s.num : ℝ) := by
    rw [Rat.cast_def]
    have hq0 : (s.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    field_simp
  have hb := period_rate_bound m (by omega) (s : ℝ) s.den hq ht1
    (htM.trans (by exact_mod_cast (show m-2 ≤ m-1 by omega)))
  exact ⟨s,s.num,s.den,hq,hp,ht1,htM,hnear,hb⟩

end KroneckerBoundedRationalNeighbor
