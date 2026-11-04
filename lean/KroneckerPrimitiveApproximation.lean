import KroneckerLogic
import Mathlib.Data.Nat.Prime.Infinite

/- Original module: KroneckerRoundedDimensions -/
section
/-! A one-step adjustment of a rounded dimension retains an explicit error bound. -/
set_option autoImplicit false
namespace KroneckerRoundedDimensions

noncomputable def rounded (r : ℝ) (a : ℕ) : ℕ := ⌊r * a⌋₊ + 1

theorem rounded_bounds (r : ℝ) (a : ℕ) (hr : 0 ≤ r) :
    r * a < (rounded r a : ℝ) ∧ (rounded r a : ℝ) ≤ r * a + 1 := by
  have h := Nat.floor_le (show 0 ≤ r * (a : ℝ) by positivity)
  have h' := Nat.lt_floor_add_one (r * (a : ℝ))
  simpa [rounded, Nat.cast_add, Nat.cast_one] using And.intro h' (by linarith : (⌊r * (a : ℝ)⌋₊ : ℝ) + 1 ≤ r * a + 1)

theorem adjusted_slope_error (r : ℝ) (a b : ℕ) (ha : 0 < a)
    (hb : r * a < (b : ℝ) ∧ (b : ℝ) ≤ r * a + 2) :
    dist ((b : ℝ) / a) r ≤ 2 / (a : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hl : r < (b : ℝ) / a := (lt_div_iff₀ ha').mpr (by nlinarith [hb.1])
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hl)]
  apply (le_div_iff₀ ha').mpr
  field_simp
  nlinarith [hb.2]

end KroneckerRoundedDimensions
end

/- Original module: KroneckerPrimeAdjustment -/
section
/-! Prime first dimensions allow a uniformly bounded coprime correction. -/
set_option autoImplicit false
namespace KroneckerPrimeAdjustment

def adjust (a b : ℕ) : ℕ := if a ∣ b then b+1 else b

theorem adjust_bounds (a b : ℕ) : b ≤ adjust a b ∧ adjust a b ≤ b+1 := by
  unfold adjust
  split_ifs <;> omega

theorem adjust_coprime (a b : ℕ) (ha : a.Prime) : a.Coprime (adjust a b) := by
  rw [ha.coprime_iff_not_dvd]
  unfold adjust
  split_ifs with h
  · intro h'
    have hd : a ∣ 1 := (Nat.dvd_add_iff_right h).mpr h'
    have hle := Nat.le_of_dvd (by decide : 0 < 1) hd
    have := ha.two_le
    omega
  · exact h

end KroneckerPrimeAdjustment
end

/- Original module: KroneckerPrimitiveApproximation -/
section
/-! Primitive dimension pairs of arbitrary height approximate every slope above one. -/
set_option autoImplicit false
namespace KroneckerPrimitiveApproximation
open KroneckerRoundedDimensions KroneckerPrimeAdjustment

theorem primitive_approximation (r : ℝ) (hr : 1 < r) (N : ℕ) :
    ∃ a b : ℕ, N ≤ a ∧ 2 ≤ a ∧ a < b ∧ a.Coprime b ∧
      dist ((b : ℝ) / a) r ≤ 2 / (a : ℝ) := by
  obtain ⟨a,hN,ha⟩ := Nat.exists_infinite_primes N
  let b := adjust a (rounded r a)
  have ha2 := ha.two_le
  have hb := adjust_bounds a (rounded r a)
  have hc := rounded_bounds r a (by linarith)
  have hlo : r * (a : ℝ) < (b : ℝ) :=
    hc.1.trans_le (by exact_mod_cast hb.1)
  have hhi : (b : ℝ) ≤ r * a + 2 := by
    have h := (show (b : ℝ) ≤ (rounded r a : ℝ)+1 by exact_mod_cast hb.2)
    linarith [hc.2]
  refine ⟨a,b,hN,ha2,?_,adjust_coprime a _ ha,adjusted_slope_error r a b (by omega) ⟨hlo,hhi⟩⟩
  have ha' : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have : (a : ℝ) < b := by nlinarith
  exact_mod_cast this

end KroneckerPrimitiveApproximation
end
