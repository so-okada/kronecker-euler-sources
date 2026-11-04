import KroneckerExteriorEntropyZero
import KroneckerSlopeSymmetry

/-! An endpoint envelope proved on the closed root interval extends to every
actual admissible dimension, because exterior entropy vanishes exactly. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalInteriorBoundExtension
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))

theorem extend_bound (m : ℕ) (hm : 3≤m) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (h : ∀ p : Dimension (family H) m,slope p ∈ interval m →
      0≤value p ∧ value p≤C*Real.sqrt ((upperRoot m-slope p)*(slope p-lowerRoot m))+D/height p) :
    ∀ p : Dimension (family H) m,0≤value p ∧
      value p≤C*Real.sqrt (max ((m : ℝ)*slope p-1-(slope p)^2) 0)+D/height p := by
  intro p
  by_cases hi : slope p ∈ interval m
  · have hq : 0≤(upperRoot m-slope p)*(slope p-lowerRoot m) :=
      mul_nonneg (sub_nonneg.mpr hi.2) (sub_nonneg.mpr hi.1)
    have hf := quadratic_factorization (m:=(m : ℝ)) (r:=slope p)
      (by exact_mod_cast (show 2≤m by omega))
    rw [hf,max_eq_left hq]
    exact h p hi
  · rw [KroneckerExteriorEntropyZero.value_zero H m hm p hi]
    exact ⟨le_refl _,add_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
      (div_nonneg hD (Nat.cast_nonneg _))⟩
end KroneckerCanonicalInteriorBoundExtension
