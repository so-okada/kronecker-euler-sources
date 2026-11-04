import KroneckerBinaryRunEncoding
import KroneckerNearbyShortFactor
import KroneckerBinaryFirstOccurrence

section

/-! Binary mechanical words keep their exact run-list values under the bit encoding. -/
set_option autoImplicit false
namespace KroneckerMechanicalBits
open KroneckerBinaryRunEncoding KroneckerBinarySwapRuns KroneckerMechanicalWords
open KroneckerNearbyShortFactor

noncomputable def mechanicalBits (s u : ℝ) (n : ℕ) : List Bool := bits (mechanicalWord s u 0 n)

theorem mechanicalBits_length (s u : ℝ) (n : ℕ) : (mechanicalBits s u n).length=n := by
  simp [mechanicalBits,bits_length,mechanicalWord_length]

theorem mechanicalBits_runs (s u : ℝ) (n : ℕ) (hs : 1 ≤ s ∧ s ≤ 2) :
    bitRuns (mechanicalBits s u n)=mechanicalWord s u 0 n :=
  bitRuns_bits _ (mechanicalWord_legal s u 0 n 2 hs.1 hs.2)

theorem mechanicalBits_take (s u : ℝ) (N n : ℕ) (hn : n ≤ N) :
    (mechanicalBits s u N).take n=mechanicalBits s u n := by
  simp only [mechanicalBits,bits,← List.map_take,word_take s u N n hn]

theorem mechanicalBits_count (s u : ℝ) (n : ℕ) (hs : 1 ≤ s ∧ s ≤ 2) :
    (mechanicalBits s u n).count true+n=(mechanicalWord s u 0 n).sum := by
  have h := bitRuns_sum (mechanicalBits s u n)
  rw [mechanicalBits_runs s u n hs,mechanicalBits_length] at h
  omega

end KroneckerMechanicalBits
end

section

/-! Mechanical bit counts telescope to the literal floor prefixes. -/
set_option autoImplicit false
namespace KroneckerMechanicalBitCounts
open KroneckerMechanicalBits KroneckerMechanicalWords KroneckerMechanicalWordSums KroneckerMechanicalRuns

theorem mechanical_true_count_int (s u : ℝ) (n : ℕ) (hs : 1 ≤ s ∧ s ≤ 2) :
    ((mechanicalBits s u n).count true : ℤ)=mechanicalPrefix s u n-⌊u⌋-(n : ℤ) := by
  have h1 := mechanicalBits_count s u n hs
  have h2 := mechanicalWord_sum_cast s u 0 n (by linarith : 0 ≤ s)
  simp only [Nat.zero_add,mechanicalPrefix,Nat.cast_zero,zero_mul,add_zero] at h2
  unfold mechanicalPrefix
  omega

theorem mechanical_true_count_real (s u : ℝ) (n : ℕ) (hs : 1 ≤ s ∧ s ≤ 2) :
    ((mechanicalBits s u n).count true : ℝ)=
      (mechanicalPrefix s u n : ℝ)-(⌊u⌋ : ℤ)-(n : ℝ) := by
  exact_mod_cast mechanical_true_count_int s u n hs

theorem mechanical_prefix_count_difference (s u t v : ℝ) (n j : ℕ) (hj : j ≤ n)
    (hs : 1 ≤ s ∧ s ≤ 2) (ht : 1 ≤ t ∧ t ≤ 2)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) :
    (((mechanicalBits s u n).take j).count true : ℤ)-
      (((mechanicalBits t v n).take j).count true : ℤ)=
      mechanicalPrefix s u j-mechanicalPrefix t v j := by
  rw [mechanicalBits_take s u n j hj,mechanicalBits_take t v n j hj]
  rw [mechanical_true_count_int s u j hs,mechanical_true_count_int t v j ht]
  rw [Int.floor_eq_zero_iff.mpr hu,Int.floor_eq_zero_iff.mpr hv]
  ring

end KroneckerMechanicalBitCounts
end

section

/-! Both binary letter counts differ from their mechanical frequencies by less than one. -/
set_option autoImplicit false
namespace KroneckerMechanicalLetterBounds
open KroneckerMechanicalBits KroneckerMechanicalBitCounts KroneckerMechanicalRuns
open KroneckerBinaryFirstOccurrence

def frequency (s : ℝ) (b : Bool) : ℝ := if b then s-1 else 2-s

theorem frequency_bounds (s : ℝ) (hs : 1 ≤ s ∧ s ≤ 2) (b : Bool) :
    0 ≤ frequency s b ∧ frequency s b ≤ 1 := by
  cases b <;> simp only [frequency,Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> linarith

theorem mechanical_letter_error (s u : ℝ) (n : ℕ) (hs : 1 ≤ s ∧ s ≤ 2) (b : Bool) :
    |((mechanicalBits s u n).count b : ℝ)-(n : ℝ)*frequency s b| < 1 := by
  have hc := mechanical_true_count_real s u n hs
  have hf := Int.floor_le (u+(n : ℝ)*s)
  have hg := Int.lt_floor_add_one (u+(n : ℝ)*s)
  have hfu := Int.floor_le u
  have hgu := Int.lt_floor_add_one u
  simp only [mechanicalPrefix] at hc
  have htrue : |((mechanicalBits s u n).count true : ℝ)-(n : ℝ)*(s-1)| < 1 := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  cases b with
  | true => exact htrue
  | false =>
    have hsum := count_true_false (mechanicalBits s u n)
    rw [mechanicalBits_length] at hsum
    have hsum' : ((mechanicalBits s u n).count true : ℝ)+
        ((mechanicalBits s u n).count false : ℝ)=(n : ℝ) := by exact_mod_cast hsum
    have he : ((mechanicalBits s u n).count false : ℝ)-(n : ℝ)*(2-s)=
        -(((mechanicalBits s u n).count true : ℝ)-(n : ℝ)*(s-1)) := by nlinarith
    simp only [frequency,Bool.false_eq_true,ite_false,he,abs_neg]
    exact htrue

end KroneckerMechanicalLetterBounds
end

section

/-! A sufficiently long target block contains both letter counts of a nearby source block. -/
set_option autoImplicit false
namespace KroneckerMechanicalCountDomination
open KroneckerMechanicalBits KroneckerMechanicalLetterBounds

theorem frequency_distance (s t : ℝ) (b : Bool) : |frequency s b-frequency t b|=|s-t| := by
  cases b with
  | false =>
    change |(2-s)-(2-t)|=|s-t|
    have he : (2-s)-(2-t)=-(s-t) := by ring
    rw [he,abs_neg]
  | true => simp [frequency]

theorem mechanical_count_domination (s u t v τ e : ℝ) (n C : ℕ)
    (hs : 1 ≤ s ∧ s ≤ 2) (ht : 1 ≤ t ∧ t ≤ 2)
    (hmargin : ∀ b : Bool, τ ≤ frequency t b) (hst : |s-t| ≤ e)
    (hbudget : 2+(n : ℝ)*e ≤ (C : ℝ)*τ) :
    ∀ b : Bool, (mechanicalBits s u n).count b ≤ (mechanicalBits t v (n+C)).count b := by
  intro b
  have ha := (abs_lt.mp (mechanical_letter_error s u n hs b)).2
  have hb := (abs_lt.mp (mechanical_letter_error t v (n+C) ht b)).1
  have hfreq : frequency s b-frequency t b ≤ e := by
    exact (le_abs_self _).trans (by rw [frequency_distance]; exact hst)
  have hm := hmargin b
  have hn : (0 : ℝ) ≤ n := by positivity
  have hC : (0 : ℝ) ≤ C := by positivity
  have hnf := mul_le_mul_of_nonneg_left hfreq hn
  have hCf := mul_le_mul_of_nonneg_left hm hC
  have hreal : ((mechanicalBits s u n).count b : ℝ) ≤
      ((mechanicalBits t v (n+C)).count b : ℝ) := by
    push_cast at hb
    nlinarith
  exact_mod_cast hreal

end KroneckerMechanicalCountDomination
end

