import KroneckerMechanicalWordSums

/-! A finite window cut from a literal mechanical word is the mechanical
word with the shifted start index and the same slope and intercept. -/
set_option autoImplicit false
namespace KroneckerMechanicalSlices
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem mechanicalWord_slice (s u : ℝ) (start n i q : ℕ) (h : i+q ≤ n) :
    ((mechanicalWord s u start n).drop i).take q = mechanicalWord s u (start+i) q := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, mechanicalWord_length]
    omega
  · intro k hk hk'
    simp [mechanicalWord, Nat.add_assoc]

theorem mechanical_slice_sum (s u : ℝ) (start n i q : ℕ) (h : i+q ≤ n) (hs : 0 ≤ s) :
    ((((mechanicalWord s u start n).drop i).take q).sum : ℤ) =
      mechanicalPrefix s u (start+i+q)-mechanicalPrefix s u (start+i) := by
  rw [mechanicalWord_slice s u start n i q h]
  exact mechanicalWord_sum_cast s u (start+i) q hs

end KroneckerMechanicalSlices
