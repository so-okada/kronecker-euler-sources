import KroneckerPeriodicLimit

/-! The concrete periodic-growth proposition, including its supremum and finite bound. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPeriodicGrowth
open KroneckerPeriodicWords KroneckerPeriodicBounds KroneckerPeriodicLog
open KroneckerPeriodicTail KroneckerPeriodicLimit

theorem growthSet_eq_periodicRatios (m : ℕ) (W : List ℕ) :
    growthSet m W =
      (fun j : ℕ => periodicLog m W j / ((j : ℝ)+2)) '' Set.Ici 1 := by
  unfold growthSet
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hn' : 3 ≤ n := hn
    refine ⟨n-2, by change 1 ≤ n-2; omega, ?_⟩
    have he : n-2+2 = n := by omega
    have he' : ((n-2 : ℕ) : ℝ)+2 = (n : ℝ) := by exact_mod_cast he
    simp only [shiftedLog, he']
  · rintro ⟨j, hj, rfl⟩
    have hj' : 1 ≤ j := hj
    refine ⟨j+2, by change 3 ≤ j+2; omega, ?_⟩
    simp [shiftedLog, Nat.cast_add]

theorem periodicGrowth_sup (m : ℕ) (W : List ℕ) :
    periodicGrowth m W =
      sSup ((fun j : ℕ => periodicLog m W j / ((j : ℝ)+2)) '' Set.Ici 1) := by
  rw [periodicGrowth, growthSet_eq_periodicRatios]

theorem periodicRatio_le_growth (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (j : ℕ) (hj : 1 ≤ j) :
    periodicLog m W j / ((j : ℝ)+2) ≤ periodicGrowth m W := by
  apply le_csSup (growthSet_bddAbove m hm W hne hr)
  rw [growthSet_eq_periodicRatios]
  exact ⟨j, hj, rfl⟩

theorem periodicGrowth_upper (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) :
    periodicGrowth m W ≤ logUpperConstant m W := by
  apply csSup_le (growthSet_nonempty m W)
  rintro x ⟨n, hn, rfl⟩
  have hn' : 3 ≤ n := hn
  exact (div_le_iff₀ (by exact_mod_cast (show 0 < n from by omega))).mpr
    (shiftedLog_upper m hm W hne hr n hn')

theorem periodicGrowth_pos (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) : 0 < periodicGrowth m W := by
  have hp := periodicLog_pos m hm W hne hr 1 (by decide)
  have hratio := periodicRatio_le_growth m hm W hne hr 1 (by decide)
  have hpos : 0 < periodicLog m W 1 / (((1 : ℕ) : ℝ)+2) := div_pos hp (by norm_num)
  exact hpos.trans_le hratio



end KroneckerPeriodicGrowth
