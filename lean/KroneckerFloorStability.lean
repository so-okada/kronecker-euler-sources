import KroneckerMechanicalWords

/- Original module: KroneckerPrefixDiscrepancy -/
section
/-! Run discrepancies are the discrete derivative of floor-prefix discrepancies. -/
set_option autoImplicit false
namespace KroneckerPrefixDiscrepancy
open KroneckerMechanicalRuns

noncomputable def discrepancy (s u t v : ℝ) (i : ℕ) : ℝ :=
  (mechanicalPrefix s u i : ℝ) - (mechanicalPrefix t v i : ℝ)

theorem run_discrepancy (s u t v : ℝ) (i : ℕ) :
    (mechanicalRun s u i : ℝ) - (mechanicalRun t v i : ℝ) =
      discrepancy s u t v (i+1)-discrepancy s u t v i := by
  simp only [mechanicalRun,discrepancy,Int.cast_sub]
  ring

theorem discrepancy_zero (s u t v : ℝ) (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) :
    discrepancy s u t v 0=0 := by
  simp [discrepancy,mechanicalPrefix,Int.floor_eq_zero_iff.mpr hu,Int.floor_eq_zero_iff.mpr hv]

end KroneckerPrefixDiscrepancy
end

/- Original module: KroneckerDiscreteVariation -/
section
/-! Finite total variation is bounded by twice the absolute prefix discrepancy mass. -/
set_option autoImplicit false
namespace KroneckerDiscreteVariation

theorem variation_with_endpoints (d : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, |d (i+1)-d i|) + |d n| ≤
      |d 0| + 2*(∑ i ∈ Finset.range n, |d (i+1)|) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have h := abs_sub (d (n+1)) (d n)
    linarith

theorem variation_zero_start (d : ℕ → ℝ) (n : ℕ) (h0 : d 0=0) :
    (∑ i ∈ Finset.range n, |d (i+1)-d i|) ≤
      2*(∑ i ∈ Finset.range n, |d (i+1)|) := by
  have h := variation_with_endpoints d n
  rw [h0,abs_zero,zero_add] at h
  linarith [abs_nonneg (d n)]

end KroneckerDiscreteVariation
end

/- Original module: KroneckerMechanicalVariation -/
section
/-! A quantitative edit-cost bound for any two aligned mechanical blocks. -/
set_option autoImplicit false
namespace KroneckerMechanicalVariation
open KroneckerMechanicalRuns KroneckerPrefixDiscrepancy KroneckerDiscreteVariation

theorem mechanical_variation (s u t v : ℝ) (n : ℕ)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) :
    (∑ i ∈ Finset.range n, |(mechanicalRun s u i : ℝ)-(mechanicalRun t v i : ℝ)|) ≤
      2*(∑ i ∈ Finset.range n, |discrepancy s u t v (i+1)|) := by
  simp_rw [run_discrepancy]
  exact variation_zero_start _ n (discrepancy_zero s u t v hu hv)

end KroneckerMechanicalVariation
end

/- Original module: KroneckerFloorStability -/
section
/-! Explicit floor stability away from the two ends of the fractional interval. -/
set_option autoImplicit false
namespace KroneckerFloorStability

theorem floor_stable (x y ε : ℝ) (hxy : |x-y| < ε)
    (hlo : ε ≤ Int.fract x) (hhi : Int.fract x+ε ≤ 1) : ⌊x⌋=⌊y⌋ := by
  have h := abs_lt.mp hxy
  have hf : Int.fract x=x-(⌊x⌋ : ℝ) := rfl
  symm
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

theorem floor_change_near_boundary (x y ε : ℝ) (hxy : |x-y| < ε)
    (hne : ⌊x⌋ ≠ ⌊y⌋) : Int.fract x < ε ∨ 1-ε < Int.fract x := by
  by_contra h
  push Not at h
  exact hne (floor_stable x y ε hxy h.1 (by linarith [h.2]))

end KroneckerFloorStability
end
