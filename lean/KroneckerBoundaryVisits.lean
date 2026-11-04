import KroneckerAlignedOrbitError

/-! Prefix discrepancy is supported on actual visits near an integer boundary. -/
set_option autoImplicit false
namespace KroneckerBoundaryVisits
open KroneckerPrefixDiscrepancy KroneckerMechanicalRuns KroneckerFloorStability
open KroneckerFloorUnitDifference

def NearBoundary (x ε : ℝ) : Prop := Int.fract x < ε ∨ 1-ε < Int.fract x

noncomputable def visits (s u ε : ℝ) (n : ℕ) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range n, if NearBoundary (u+((i+1 : ℕ) : ℝ)*s) ε then 1 else 0

theorem discrepancy_mass_le_visits (s u t v ε : ℝ) (n : ℕ) (hε : ε ≤ 1)
    (hclose : ∀ i < n, |(u+((i+1 : ℕ) : ℝ)*s)-(v+((i+1 : ℕ) : ℝ)*t)| < ε) :
    (∑ i ∈ Finset.range n, |discrepancy s u t v (i+1)|) ≤ (visits s u ε n : ℝ) := by
  classical
  unfold visits
  push_cast
  apply Finset.sum_le_sum
  intro i hi
  have hc := hclose i (Finset.mem_range.mp hi)
  simp only [discrepancy,mechanicalPrefix]
  split_ifs with hn
  · exact floor_unit_difference _ _ (hc.trans_le hε)
  · have he : ⌊u+((i+1 : ℕ) : ℝ)*s⌋=⌊v+((i+1 : ℕ) : ℝ)*t⌋ := by
      by_contra he
      apply hn
      simpa only [NearBoundary, Nat.cast_add, Nat.cast_one] using
        floor_change_near_boundary (u+((i+1 : ℕ) : ℝ)*s) (v+((i+1 : ℕ) : ℝ)*t) ε hc he
    rw [he,sub_self,abs_zero]

end KroneckerBoundaryVisits
