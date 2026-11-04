import KroneckerMechanicalWordShift

set_option autoImplicit false
namespace KroneckerNormalizedWindow
open KroneckerMechanicalWords KroneckerMechanicalWordShift KroneckerMechanicalFractional

theorem normalized_window (s u : ℝ) (i n : ℕ) :
    mechanicalWord s u i n = mechanicalWord s (Int.fract (u + (i : ℝ) * s)) 0 n := by
  rw [word_shift, word_fractional]

theorem nested_window (s u : ℝ) (i j n : ℕ) :
    mechanicalWord s (Int.fract (u + (i : ℝ) * s)) j n =
      mechanicalWord s u (i + j) n := by
  rw [word_fractional, word_shift s (u + (i : ℝ) * s) j n, word_shift s u (i + j) n]
  congr 1
  push_cast
  ring

end KroneckerNormalizedWindow
