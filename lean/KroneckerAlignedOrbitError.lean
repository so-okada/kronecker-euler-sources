import KroneckerFloorStability

/- Original module: KroneckerFloorUnitDifference -/
section
/-! Floors of points less than one apart differ by at most one integer. -/
set_option autoImplicit false
namespace KroneckerFloorUnitDifference

theorem floor_unit_difference (x y : ℝ) (hxy : |x-y| < 1) :
    |(⌊x⌋ : ℝ)-(⌊y⌋ : ℝ)| ≤ 1 := by
  have h := abs_lt.mp hxy
  have hx := Int.floor_le x
  have hy := Int.floor_le y
  have hx' := Int.lt_floor_add_one x
  have hy' := Int.lt_floor_add_one y
  have h₁ : (⌊x⌋ : ℝ)-(⌊y⌋ : ℝ) < 2 := by linarith
  have h₂ : (⌊y⌋ : ℝ)-(⌊x⌋ : ℝ) < 2 := by linarith
  have h₁' : ⌊x⌋-⌊y⌋ < 2 := by exact_mod_cast h₁
  have h₂' : ⌊y⌋-⌊x⌋ < 2 := by exact_mod_cast h₂
  rw [abs_le]
  constructor
  · exact_mod_cast (show (-1 : ℤ) ≤ ⌊x⌋-⌊y⌋ by omega)
  · exact_mod_cast (show ⌊x⌋-⌊y⌋ ≤ (1 : ℤ) by omega)

end KroneckerFloorUnitDifference
end

/- Original module: KroneckerAlignedOrbitError -/
section
/-! One finite alignment controls every point of the following mechanical block. -/
set_option autoImplicit false
namespace KroneckerAlignedOrbitError

theorem orbit_error (s u t v : ℝ) (i : ℕ) :
    |(u+(i : ℝ)*s)-(v+(i : ℝ)*t)| ≤ |u-v|+(i : ℝ)*|s-t| := by
  have he : (u+(i : ℝ)*s)-(v+(i : ℝ)*t)=(u-v)+(i : ℝ)*(s-t) := by ring
  rw [he]
  simpa only [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ i by positivity)] using abs_add_le (u-v) ((i : ℝ)*(s-t))

theorem block_orbit_error (s u t v ε : ℝ) (n i : ℕ) (hi : i ≤ n)
    (h : |u-v|+(n : ℝ)*|s-t| < ε) :
    |(u+(i : ℝ)*s)-(v+(i : ℝ)*t)| < ε := by
  have hc : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hm := mul_le_mul_of_nonneg_right hc (abs_nonneg (s-t))
  exact (orbit_error s u t v i).trans_lt (by linarith)

end KroneckerAlignedOrbitError
end
