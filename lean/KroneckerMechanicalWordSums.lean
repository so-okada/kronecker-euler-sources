import KroneckerMechanicalWords

/-! The literal natural run lists concatenate and telescope exactly. -/
set_option autoImplicit false
namespace KroneckerMechanicalWordSums
open KroneckerMechanicalRuns KroneckerMechanicalWords

theorem mechanicalWord_append (s u : ℝ) (start n k : ℕ) :
    mechanicalWord s u start (n+k) = mechanicalWord s u start n ++ mechanicalWord s u (start+n) k := by
  unfold mechanicalWord
  rw [List.ofFn_add]
  simp [Nat.add_assoc]

theorem mechanicalWord_one (s u : ℝ) (start : ℕ) :
    mechanicalWord s u start 1 = [natRun s u start] := by
  simp [mechanicalWord, List.ofFn_succ]

theorem mechanicalWord_sum_cast (s u : ℝ) (start n : ℕ) (hs : 0 ≤ s) :
    ((mechanicalWord s u start n).sum : ℤ) = mechanicalPrefix s u (start+n)-mechanicalPrefix s u start := by
  induction n with
  | zero => simp [mechanicalWord]
  | succ n ih =>
    rw [mechanicalWord_append, mechanicalWord_one, List.sum_append, List.sum_singleton,
      Nat.cast_add, ih, natRun_cast s u (start+n) hs]
    simp only [mechanicalRun, Nat.add_assoc]
    ring

end KroneckerMechanicalWordSums
