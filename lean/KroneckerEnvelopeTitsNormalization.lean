import KroneckerNegativeTitsSymmetry
import KroneckerSlopeSymmetry

/- Original module: KroneckerTitsSlopeIdentity -/
section
/-! The exact integral Tits form equals minus the slope quadratic times
the source square, with all natural-to-real coercions made explicit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTitsSlopeIdentity
open KroneckerNegativeTitsSymmetry KroneckerSlopeSymmetry
theorem identity (m a b : ℕ) (ha : 0<a) :
    slopeQuadratic (m : ℝ) ((b : ℝ)/a) = -(tits m a b : ℝ)/(a : ℝ)^2 := by
  have ha' : (a : ℝ)≠0 := by exact_mod_cast (ne_of_gt ha)
  unfold slopeQuadratic tits
  push_cast
  field_simp <;> ring
theorem gap (m a b : ℕ) (hm : 3≤m) (ha : 0<a) :
    (KroneckerEndpointRoots.upperRoot m-(b : ℝ)/a)*((b : ℝ)/a-KroneckerEndpointRoots.lowerRoot m)=
      -(tits m a b : ℝ)/(a : ℝ)^2 := by
  rw [root_gap_product (by exact_mod_cast (show 2≤m by omega))]
  exact identity m a b ha
end KroneckerTitsSlopeIdentity
end
end

/- Original module: KroneckerTitsSquareRootNormalization -/
section
/-! The square root of the integral negative Tits magnitude, divided by
source height, is exactly the root-gap factor in the manuscript envelope. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTitsSquareRootNormalization
open KroneckerNegativeTitsSymmetry KroneckerEndpointRoots
theorem identity (m a b : ℕ) (hm : 3≤m) (ha : 0<a) :
    Real.sqrt ((upperRoot m-(b : ℝ)/a)*((b : ℝ)/a-lowerRoot m)) =
      Real.sqrt (-(tits m a b : ℝ))/(a : ℝ) := by
  rw [KroneckerTitsSlopeIdentity.gap m a b hm ha,Real.sqrt_div' _ (sq_nonneg _),
    Real.sqrt_sq_eq_abs,abs_of_pos (Nat.cast_pos.mpr ha)]
end KroneckerTitsSquareRootNormalization
end
end

/- Original module: KroneckerEnvelopeTitsNormalization -/
section
/-! The manuscript envelope is exactly C_m*sqrt(-Tits)/a on integral
dimensions, isolating the finite geometric inequality that would prove it. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEnvelopeTitsNormalization
open KroneckerNegativeTitsSymmetry KroneckerManuscriptTarget
def coefficient (m : ℕ) : ℝ := (m : ℝ)*Real.log 2*Real.sqrt (((m : ℝ)+2)/((m : ℝ)-2))
theorem identity (m a b : ℕ) (hm : 3≤m) (ha : 0<a) :
    bound m ((b : ℝ)/a)=coefficient m * Real.sqrt (-(tits m a b : ℝ))/(a : ℝ) := by
  unfold bound coefficient
  rw [KroneckerTitsSquareRootNormalization.identity m a b hm ha]
  ring
theorem positive (m : ℕ) (hm : 3≤m) : 0<coefficient m := by
  have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
  unfold coefficient
  apply mul_pos (mul_pos (by linarith) (Real.log_pos (by norm_num)))
  exact Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
end KroneckerEnvelopeTitsNormalization
end
end
