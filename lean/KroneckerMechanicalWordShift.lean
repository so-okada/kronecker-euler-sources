import KroneckerMechanicalWords

section

/-! Integer changes of intercept preserve mechanical runs and literal words. -/
set_option autoImplicit false
namespace KroneckerMechanicalTranslation
open KroneckerMechanicalRuns KroneckerMechanicalWords

theorem prefix_add_integer (s u : ℝ) (z : ℤ) (i : ℕ) :
    mechanicalPrefix s (u+(z : ℝ)) i = mechanicalPrefix s u i+z := by
  unfold mechanicalPrefix
  rw [show u+(z : ℝ)+(i : ℝ)*s = (u+(i : ℝ)*s)+(z : ℝ) by ring,
    Int.floor_add_intCast]

theorem run_add_integer (s u : ℝ) (z : ℤ) (i : ℕ) :
    mechanicalRun s (u+(z : ℝ)) i = mechanicalRun s u i := by
  unfold mechanicalRun
  rw [prefix_add_integer, prefix_add_integer]
  ring

theorem natRun_add_integer (s u : ℝ) (z : ℤ) (i : ℕ) :
    natRun s (u+(z : ℝ)) i = natRun s u i := by
  simp only [natRun, run_add_integer]

theorem word_add_integer (s u : ℝ) (z : ℤ) (start n : ℕ) :
    mechanicalWord s (u+(z : ℝ)) start n = mechanicalWord s u start n := by
  simp only [mechanicalWord, natRun_add_integer]

end KroneckerMechanicalTranslation
end

section

/-! Normalize arbitrary mechanical intercepts into the half-open unit interval. -/
set_option autoImplicit false
namespace KroneckerMechanicalFractional
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalTranslation



theorem word_fractional (s u : ℝ) (start n : ℕ) :
    mechanicalWord s (Int.fract u) start n = mechanicalWord s u start n := by
  have h := word_add_integer s (Int.fract u) ⌊u⌋ start n
  have hu : Int.fract u+(⌊u⌋ : ℝ)=u := Int.fract_add_floor u
  rw [hu] at h
  exact h.symm

end KroneckerMechanicalFractional
end

section

/-! Move a finite starting index into the mechanical intercept exactly. -/
set_option autoImplicit false
namespace KroneckerMechanicalWordShift
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalWindows

theorem natRun_shift (s u : ℝ) (start i : ℕ) :
    natRun s u (start+i)=natRun s (u+(start : ℝ)*s) i := by
  simp only [natRun,mechanical_shift]

theorem word_shift (s u : ℝ) (start n : ℕ) :
    mechanicalWord s u start n=mechanicalWord s (u+(start : ℝ)*s) 0 n := by
  simp only [mechanicalWord, Nat.zero_add, natRun_shift]

theorem window_shift (s u : ℝ) (start q : ℕ) :
    windowSum s u q start=windowSum s (u+(start : ℝ)*s) q 0 := by
  simp only [windowSum,Nat.zero_add,mechanical_shift]

end KroneckerMechanicalWordShift
end

