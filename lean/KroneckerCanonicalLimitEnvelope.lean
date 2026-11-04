import Mathlib.Analysis.SpecialFunctions.Log.Basic
import KroneckerCanonicalKroneckerModuli
import KroneckerApproximableSequenceCriterion

section

/- Original module: KroneckerIntegerEulerLogNonnegative -/
section
/-! The total real logarithm of an integer is nonnegative, including zero
and negative integers. This does not prove the separate positive-Euler gate. -/
set_option autoImplicit false
namespace KroneckerIntegerEulerLogNonnegative
theorem nonnegative (z : ℤ) : 0≤Real.log (z : ℝ) := by
  rcases lt_trichotomy z 0 with hn | hz | hp
  · have he : (z : ℝ)= -(-(z : ℝ)) := by ring
    rw [he,Real.log_neg_eq_log]
    apply Real.log_nonneg
    exact_mod_cast (show (1 : ℤ)≤ -z by omega)
  · subst z;simp
  · apply Real.log_nonneg
    exact_mod_cast (show (1 : ℤ)≤z by omega)
end KroneckerIntegerEulerLogNonnegative
end

/- Original module: KroneckerCanonicalEntropyNonnegative -/
section
/-! The actual normalized total-log Euler observable is nonnegative at every
allowed dimension. This formal property is weaker than positive Euler itself. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalEntropyNonnegative
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
theorem nonnegative (m : ℕ) (p : Dimension (family H) m) : 0≤value p :=
  div_nonneg (KroneckerIntegerEulerLogNonnegative.nonnegative _) (Nat.cast_nonneg _)
end KroneckerCanonicalEntropyNonnegative
end
end
end

section

/-! Finite actual entropy bounds pass to any nonvacuous joint limit, with
continuity of the exact manuscript square-root envelope proved explicitly. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalLimitEnvelope
open Filter KroneckerLogic
open scoped Topology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
theorem continuous_bound (m : ℕ) : Continuous (bound m) := by unfold bound;fun_prop
theorem limit_bounds (m : ℕ)
    (hb : ∀ p : Dimension (family H) m,0≤value p ∧ value p≤bound m (slope p))
    (r L : ℝ) (hn : Approximable (height (M:=family H) (m:=m)) slope r)
    (hl : JointLimit (height (M:=family H) (m:=m)) slope value r L) : 0≤L ∧ L≤bound m r := by
  obtain ⟨p⟩ := approaching_nonempty _ _ hn
  have hv := jointLimit_sequence _ _ _ hl p.val p.property.1 p.property.2
  have he := ((continuous_bound m).tendsto r).comp p.property.2
  exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hv (fun n => (hb (p.val n)).1),
    le_of_tendsto_of_tendsto' hv he (fun n => (hb (p.val n)).2)⟩
end KroneckerCanonicalLimitEnvelope
end
end

