import KroneckerGoodPartitionUpper
import KroneckerBadWindowBounds

/- Original module: KroneckerSeparatedStarts -/
section
/-! Starts chosen in different regularly spaced holes cannot coincide. -/
set_option autoImplicit false
namespace KroneckerSeparatedStarts

def holeStart (L j : ℕ) : ℕ := 3+j*(L+3)

theorem separated_start_injective (L j k i t : ℕ) (hi : i < L) (ht : t < L)
    (heq : holeStart L j+i = holeStart L k+t) : j = k := by
  unfold holeStart at heq
  by_contra h
  rcases lt_or_gt_of_ne h with hjk | hkj
  · have hm : (j+1)*(L+3) ≤ k*(L+3) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · have hm : (k+1)*(L+3) ≤ j*(L+3) := Nat.mul_le_mul_right _ (by omega)
    nlinarith


end KroneckerSeparatedStarts
end

/- Original module: KroneckerBadHoleWitness -/
section
/-! A hole failing the good-window condition contains an indexed bad full window. -/
set_option autoImplicit false
namespace KroneckerBadHoleWitness
open KroneckerMechanicalWindows KroneckerGoodIntervals KroneckerSeparatedStarts

noncomputable def badHoleCount (s u : ℝ) (p : ℤ) (q L H : ℕ) : ℕ := by
  classical
  exact ((Finset.range H).filter (fun j => ¬GoodWindows s u p q (holeStart L j) L)).card

theorem bad_interval_witness (s u : ℝ) (p : ℤ) (q start L : ℕ) (hq : 0 < q)
    (hbad : ¬GoodWindows s u p q start L) :
    ∃ i, i < L ∧ i+q ≤ L ∧ windowSum s u q (start+i) ≠ p := by
  classical
  unfold GoodWindows at hbad
  push Not at hbad
  obtain ⟨i,hi,hbad⟩ := hbad
  exact ⟨i,by omega,hi,hbad⟩


end KroneckerBadHoleWitness
end

/- Original module: KroneckerBadHoleCount -/
section
/-! Disjoint holes with a bad internal window inject into the bad-window starts. -/
set_option autoImplicit false
namespace KroneckerBadHoleCount
open KroneckerMechanicalWindows KroneckerWindowDiscrepancy KroneckerBadWindowCount KroneckerBadWindowBounds
open KroneckerGoodIntervals KroneckerSeparatedStarts KroneckerBadHoleWitness

theorem bad_holes_le_bad_windows (s u : ℝ) (p : ℤ) (q L H a : ℕ) (hq : 0 < q)
    (hfit : ∀ j < H, holeStart L j+L ≤ a) :
    badHoleCount s u p q L H ≤ badWindows s u p q (a+1-q) := by
  classical
  let S := (Finset.range H).filter (fun j => ¬GoodWindows s u p q (holeStart L j) L)
  let T := (Finset.range (a+1-q)).filter (fun i => discrepancy s u p q i ≠ 0)
  have hwit (j : S) : ∃ i, i < L ∧ i+q ≤ L ∧ windowSum s u q (holeStart L j.val+i) ≠ p :=
    bad_interval_witness s u p q (holeStart L j.val) L hq (Finset.mem_filter.mp j.property).2
  let w : S → ℕ := fun j => Classical.choose (hwit j)
  have hw (j : S) : w j < L ∧ w j+q ≤ L ∧ windowSum s u q (holeStart L j.val+w j) ≠ p :=
    Classical.choose_spec (hwit j)
  let f : S → T := fun j => ⟨holeStart L j.val+w j, by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hj : j.val < H := Finset.mem_range.mp (Finset.mem_filter.mp j.property).1
      have hfitj := hfit j.val hj
      have hwi := (hw j).2.1
      omega
    · exact sub_ne_zero.mpr (hw j).2.2⟩
  change S.card ≤ T.card
  apply Finset.card_le_card_of_injective (f := f)
  intro j k hjk
  apply Subtype.ext
  have heq : holeStart L j.val+w j = holeStart L k.val+w k := congrArg Subtype.val hjk
  exact separated_start_injective L j.val k.val (w j) (w k) (hw j).1 (hw k).1 heq

end KroneckerBadHoleCount
end

/- Original module: KroneckerRegularHoleBudget -/
section
/-! The floor-selected scaffold holes fit inside the mechanical frame part. -/
set_option autoImplicit false
namespace KroneckerRegularHoleBudget
open KroneckerSeparatedStarts KroneckerBadHoleWitness KroneckerBadHoleCount KroneckerBadWindowBounds

theorem regular_hole_fits (a L j : ℕ) (hj : j < (a-2)/(L+3)) : holeStart L j+L ≤ a := by
  have hdiv := Nat.div_mul_le_self (a-2) (L+3)
  have hmul : (j+1)*(L+3) ≤ ((a-2)/(L+3))*(L+3) := Nat.mul_le_mul_right _ (by omega)
  have hsub : a-2 ≤ a := Nat.sub_le _ _
  unfold holeStart
  nlinarith


end KroneckerRegularHoleBudget
end
