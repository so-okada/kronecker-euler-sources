import KroneckerMechanicalWindows

/- Original module: KroneckerWindowDiscrepancy -/
section
/-! Near an integral q-window slope, every nonzero discrepancy has the same
sign and absolute value one. -/
set_option autoImplicit false
namespace KroneckerWindowDiscrepancy
open KroneckerMechanicalWindows

noncomputable def discrepancy (s u : ℝ) (p : ℤ) (q i : ℕ) : ℤ := windowSum s u q i-p

theorem discrepancy_above (s u : ℝ) (p : ℤ) (q i : ℕ)
    (hlo : (p : ℝ) ≤ (q : ℝ)*s) (hhi : (q : ℝ)*s ≤ (p : ℝ)+1) :
    discrepancy s u p q i = 0 ∨ discrepancy s u p q i = 1 := by
  have h := window_integer_bounds s u q i p (p+1) hlo (by simpa using hhi)
  unfold discrepancy
  omega

theorem discrepancy_below (s u : ℝ) (p : ℤ) (q i : ℕ)
    (hlo : (p : ℝ)-1 ≤ (q : ℝ)*s) (hhi : (q : ℝ)*s ≤ (p : ℝ)) :
    discrepancy s u p q i = -1 ∨ discrepancy s u p q i = 0 := by
  have h := window_integer_bounds s u q i (p-1) p (by simpa using hlo) hhi
  unfold discrepancy
  omega


end KroneckerWindowDiscrepancy
end

/- Original module: KroneckerBadWindowCount -/
section
/-! Count nonzero discrepancies exactly when they all have unit size and
the same sign. Occurrences are indexed by their start positions. -/
set_option autoImplicit false
namespace KroneckerBadWindowCount

noncomputable def nonzeroCount (d : ℕ → ℤ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun i => d i ≠ 0)).card

theorem count_eq_sum_nonnegative (d : ℕ → ℤ) (N : ℕ)
    (hd : ∀ i ∈ Finset.range N, d i = 0 ∨ d i = 1) :
    (nonzeroCount d N : ℤ) = ∑ i ∈ Finset.range N, d i := by
  classical
  calc
    (nonzeroCount d N : ℤ) = ∑ i ∈ (Finset.range N).filter (fun i => d i ≠ 0), (1 : ℤ) := by
      simp [nonzeroCount]
    _ = ∑ i ∈ Finset.range N, d i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rcases hd i hi with h | h <;> simp [h]

theorem count_eq_neg_sum_nonpositive (d : ℕ → ℤ) (N : ℕ)
    (hd : ∀ i ∈ Finset.range N, d i = -1 ∨ d i = 0) :
    (nonzeroCount d N : ℤ) = -(∑ i ∈ Finset.range N, d i) := by
  have h := count_eq_sum_nonnegative (fun i => -d i) N (by
    intro i hi
    rcases hd i hi with h | h <;> simp [h])
  simpa [nonzeroCount, Finset.sum_neg_distrib] using h

end KroneckerBadWindowCount
end

/- Original module: KroneckerFloorError -/
section
/-! The rounding error of a floor increment is strictly less than one. -/
set_option autoImplicit false
namespace KroneckerFloorError
open KroneckerMechanicalWindows KroneckerWindowDiscrepancy

theorem floor_increment_error (x t : ℝ) :
    |((⌊x+t⌋-⌊x⌋ : ℤ) : ℝ)-t| < 1 := by
  have hxlo := Int.floor_le x
  have hxhi := Int.lt_floor_add_one x
  have htlo := Int.floor_le (x+t)
  have hthi := Int.lt_floor_add_one (x+t)
  rw [Int.cast_sub]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem window_rounding_error (s u : ℝ) (q i : ℕ) :
    |(windowSum s u q i : ℝ)-(q : ℝ)*s| < 1 := by
  rw [window_floor]
  exact floor_increment_error _ _


end KroneckerFloorError
end

/- Original module: KroneckerWindowTelescoping -/
section
/-! Summing all overlapping q-windows leaves only q boundary increments. -/
set_option autoImplicit false
namespace KroneckerWindowTelescoping
open KroneckerMechanicalRuns KroneckerMechanicalWindows

theorem range_shift_balance (f : ℕ → ℤ) (q N : ℕ) :
    (∑ i ∈ Finset.range N, (f (i+q)-f i)) =
      ∑ i ∈ Finset.range q, (f (N+i)-f i) := by
  have heq := congrArg (fun k : ℕ => ∑ i ∈ Finset.range k, f i) (Nat.add_comm N q)
  rw [Finset.sum_range_add, Finset.sum_range_add] at heq
  have hcomm : (∑ i ∈ Finset.range N, f (i+q)) = ∑ i ∈ Finset.range N, f (q+i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hcomm]
  linarith

theorem window_total_symmetry (s u : ℝ) (q N : ℕ) :
    (∑ i ∈ Finset.range N, windowSum s u q i) = ∑ i ∈ Finset.range q, windowSum s u N i := by
  simp only [windowSum, mechanical_block_sum]
  simpa only [Nat.add_comm N] using range_shift_balance (mechanicalPrefix s u) q N

end KroneckerWindowTelescoping
end

/- Original module: KroneckerWindowTotalError -/
section
/-! The total error over N overlapping q-windows is bounded by q, not by N. -/
set_option autoImplicit false
namespace KroneckerWindowTotalError
open KroneckerMechanicalWindows KroneckerWindowDiscrepancy KroneckerWindowTelescoping KroneckerFloorError

theorem total_window_error (s u : ℝ) (q N : ℕ) :
    |((∑ i ∈ Finset.range N, windowSum s u q i : ℤ) : ℝ)-(N : ℝ)*(q : ℝ)*s| ≤ (q : ℝ) := by
  have heq : ((∑ i ∈ Finset.range N, windowSum s u q i : ℤ) : ℝ)-(N : ℝ)*(q : ℝ)*s =
      ∑ i ∈ Finset.range q, ((windowSum s u N i : ℝ)-(N : ℝ)*s) := by
    rw [window_total_symmetry, Finset.sum_sub_distrib]
    simp only [Int.cast_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [heq]
  calc
    |∑ i ∈ Finset.range q, ((windowSum s u N i : ℝ)-(N : ℝ)*s)| ≤
        ∑ i ∈ Finset.range q, |(windowSum s u N i : ℝ)-(N : ℝ)*s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (window_rounding_error s u N i).le
    _ = (q : ℝ) := by simp

theorem total_discrepancy_error (s u : ℝ) (p : ℤ) (q N : ℕ) :
    |((∑ i ∈ Finset.range N, discrepancy s u p q i : ℤ) : ℝ)-
      (N : ℝ)*((q : ℝ)*s-(p : ℝ))| ≤ (q : ℝ) := by
  have heq : ((∑ i ∈ Finset.range N, discrepancy s u p q i : ℤ) : ℝ)-
      (N : ℝ)*((q : ℝ)*s-(p : ℝ)) =
      ((∑ i ∈ Finset.range N, windowSum s u q i : ℤ) : ℝ)-(N : ℝ)*(q : ℝ)*s := by
    simp only [discrepancy, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    ring
  rw [heq]
  exact total_window_error s u q N

end KroneckerWindowTotalError
end

/- Original module: KroneckerBadWindowBounds -/
section
/-! Finite bad-window estimates above and below an integral q-window slope. -/
set_option autoImplicit false
namespace KroneckerBadWindowBounds
open KroneckerWindowDiscrepancy KroneckerBadWindowCount KroneckerWindowTotalError

noncomputable def badWindows (s u : ℝ) (p : ℤ) (q N : ℕ) : ℕ :=
  nonzeroCount (discrepancy s u p q) N

theorem bad_windows_above (s u : ℝ) (p : ℤ) (q N : ℕ)
    (hlo : (p : ℝ) ≤ (q : ℝ)*s) (hhi : (q : ℝ)*s ≤ (p : ℝ)+1) :
    (badWindows s u p q N : ℝ) ≤ (N : ℝ)*((q : ℝ)*s-(p : ℝ))+(q : ℝ) := by
  have hc : (badWindows s u p q N : ℝ) =
      ((∑ i ∈ Finset.range N, discrepancy s u p q i : ℤ) : ℝ) := by
    exact_mod_cast count_eq_sum_nonnegative (discrepancy s u p q) N
      (fun i _ => discrepancy_above s u p q i hlo hhi)
  have he := (abs_le.mp (total_discrepancy_error s u p q N)).2
  rw [← hc] at he
  linarith

theorem bad_windows_below (s u : ℝ) (p : ℤ) (q N : ℕ)
    (hlo : (p : ℝ)-1 ≤ (q : ℝ)*s) (hhi : (q : ℝ)*s ≤ (p : ℝ)) :
    (badWindows s u p q N : ℝ) ≤ (N : ℝ)*((p : ℝ)-(q : ℝ)*s)+(q : ℝ) := by
  have hc : (badWindows s u p q N : ℝ) =
      -((∑ i ∈ Finset.range N, discrepancy s u p q i : ℤ) : ℝ) := by
    exact_mod_cast count_eq_neg_sum_nonpositive (discrepancy s u p q) N
      (fun i _ => discrepancy_below s u p q i hlo hhi)
  have he := (abs_le.mp (total_discrepancy_error s u p q N)).1
  linarith

end KroneckerBadWindowBounds
end
