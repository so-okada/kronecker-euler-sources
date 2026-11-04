import KroneckerMechanicalWordSums

/- Original module: KroneckerIntegerRunSigns -/
section
/-! Relative to any fixed integer run type, all mechanical discrepancies have one sign. -/
set_option autoImplicit false
namespace KroneckerIntegerRunSigns
open KroneckerMechanicalRuns KroneckerMechanicalBounds

theorem mechanical_run_ge_integer (s u : ℝ) (i : ℕ) (k : ℤ) (hk : (k : ℝ) ≤ s) :
    k ≤ mechanicalRun s u i := by
  rw [mechanical_run_increment]
  exact (floor_increment_integer_bounds (u+(i : ℝ)*s) s k ⌈s⌉ hk (Int.le_ceil s)).1

theorem mechanical_run_le_integer (s u : ℝ) (i : ℕ) (k : ℤ) (hk : s ≤ (k : ℝ)) :
    mechanicalRun s u i ≤ k := by
  rw [mechanical_run_increment]
  exact (floor_increment_integer_bounds (u+(i : ℝ)*s) s ⌊s⌋ k (Int.floor_le s) hk).2

theorem mechanical_integer_common_sign (s u : ℝ) (k : ℤ) :
    (∀ i, 0 ≤ mechanicalRun s u i-k) ∨ (∀ i, mechanicalRun s u i-k ≤ 0) := by
  rcases le_total (k : ℝ) s with h | h
  · exact Or.inl (fun i => sub_nonneg.mpr (mechanical_run_ge_integer s u i k h))
  · exact Or.inr (fun i => sub_nonpos.mpr (mechanical_run_le_integer s u i k h))

end KroneckerIntegerRunSigns
end

/- Original module: KroneckerSignedAbsoluteSum -/
section
/-! A finite common-sign sum has no cancellation in absolute value. -/
set_option autoImplicit false
namespace KroneckerSignedAbsoluteSum

theorem sum_abs_of_nonnegative (d : ℕ → ℤ) (N : ℕ) (hd : ∀ i ∈ Finset.range N, 0 ≤ d i) :
    (∑ i ∈ Finset.range N, |d i|) = |∑ i ∈ Finset.range N, d i| := by
  rw [abs_of_nonneg (Finset.sum_nonneg hd)]
  exact Finset.sum_congr rfl (fun i hi => abs_of_nonneg (hd i hi))

theorem sum_abs_of_nonpositive (d : ℕ → ℤ) (N : ℕ) (hd : ∀ i ∈ Finset.range N, d i ≤ 0) :
    (∑ i ∈ Finset.range N, |d i|) = |∑ i ∈ Finset.range N, d i| := by
  rw [abs_of_nonpos (Finset.sum_nonpos hd), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i hi => abs_of_nonpos (hd i hi))

theorem sum_abs_common_sign (d : ℕ → ℤ) (N : ℕ)
    (hd : (∀ i ∈ Finset.range N, 0 ≤ d i) ∨ (∀ i ∈ Finset.range N, d i ≤ 0)) :
    (∑ i ∈ Finset.range N, |d i|) = |∑ i ∈ Finset.range N, d i| := by
  rcases hd with h | h
  · exact sum_abs_of_nonnegative d N h
  · exact sum_abs_of_nonpositive d N h

end KroneckerSignedAbsoluteSum
end

/- Original module: KroneckerMechanicalEditCost -/
section
/-! Exact vertical edit cost of a mechanical block relative to a constant integer run. -/
set_option autoImplicit false
namespace KroneckerMechanicalEditCost
open KroneckerMechanicalRuns KroneckerMechanicalWindows KroneckerIntegerRunSigns KroneckerSignedAbsoluteSum

noncomputable def mechanicalEditCost (s u : ℝ) (start n : ℕ) (k : ℤ) : ℤ :=
  ∑ i ∈ Finset.range n, |mechanicalRun s u (start+i)-k|

theorem mechanical_edit_cost (s u : ℝ) (start n : ℕ) (k : ℤ) :
    mechanicalEditCost s u start n k = |windowSum s u n start-(n : ℤ)*k| := by
  have hs : (∀ i ∈ Finset.range n, 0 ≤ mechanicalRun s u (start+i)-k) ∨
      (∀ i ∈ Finset.range n, mechanicalRun s u (start+i)-k ≤ 0) := by
    rcases mechanical_integer_common_sign s u k with h | h
    · exact Or.inl (fun i _ => h (start+i))
    · exact Or.inr (fun i _ => h (start+i))
  unfold mechanicalEditCost
  rw [sum_abs_common_sign _ _ hs]
  simp [Finset.sum_sub_distrib, windowSum]

theorem mechanical_edit_cost_prefix (s u : ℝ) (n : ℕ) (k : ℤ) :
    mechanicalEditCost s u 0 n k = |mechanicalPrefix s u n-⌊u⌋-(n : ℤ)*k| := by
  rw [mechanical_edit_cost, windowSum]
  simpa only [Nat.zero_add] using congrArg (fun z : ℤ => |z-(n : ℤ)*k|) (mechanical_prefix_sum s u n)

end KroneckerMechanicalEditCost
end

/- Original module: KroneckerWordEditCost -/
section
/-! The natural-number sum of vertical length differences for literal run words. -/
set_option autoImplicit false
namespace KroneckerWordEditCost
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalWordSums KroneckerMechanicalEditCost

def wordEditCost (X : List ℕ) (k : ℕ) : ℕ := (X.map (fun r => ((r : ℤ)-(k : ℤ)).natAbs)).sum

theorem wordEditCost_append (X Y : List ℕ) (k : ℕ) :
    wordEditCost (X++Y) k = wordEditCost X k+wordEditCost Y k := by
  simp [wordEditCost, List.sum_append]

theorem wordEditCost_singleton (r k : ℕ) : wordEditCost [r] k = ((r : ℤ)-(k : ℤ)).natAbs := by
  simp [wordEditCost]

theorem wordEditCost_mechanical (s u : ℝ) (start n k : ℕ) (hs : 0 ≤ s) :
    (wordEditCost (mechanicalWord s u start n) k : ℤ) = mechanicalEditCost s u start n (k : ℤ) := by
  induction n with
  | zero => simp [wordEditCost, mechanicalWord, mechanicalEditCost]
  | succ n ih =>
    rw [mechanicalWord_append s u start n 1, mechanicalWord_one, wordEditCost_append,
      Nat.cast_add, ih, wordEditCost_singleton, Int.natCast_natAbs, natRun_cast s u (start+n) hs]
    unfold mechanicalEditCost
    rw [Finset.sum_range_succ]

end KroneckerWordEditCost
end
