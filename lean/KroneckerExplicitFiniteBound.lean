import KroneckerGeneralFrame
import KroneckerReadableMain

set_option autoImplicit false

namespace KroneckerExplicitFiniteBound
noncomputable section
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFiniteCoefficientIntegration
open KroneckerPublishedPositionApplication KroneckerScopedActualFrameApplication
open KroneckerNegativeTitsSymmetry KroneckerEnvelopeTitsNormalization

def error (m : ℕ) : ℝ := Real.log ((2 : ℝ) ^ m / (m : ℝ))

theorem error_nonnegative (m : ℕ) (hm : 3 ≤ m) : 0 ≤ error m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply Real.log_nonneg
  apply (le_div_iff₀ hm').mpr
  simpa only [one_mul] using
    (show (m : ℝ) ≤ (2 : ℝ) ^ m by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le)

theorem fundamental_multiplied_bound (G : Geometry) (A : Application G)
    (S : FiniteEnumeration G)
    (m a b : ℕ) (hm : 3 ≤ m) (ha : 0 < a) (hab : a ≤ b) (hc : a.Coprime b) :
    (m : ℤ) * euler (family G) m a b ≤ (2 : ℤ) ^ (m * (a + b + 1)) := by
  by_cases h1 : a = 1
  · subst a
    exact KroneckerGeneralFrame.unit_euler_upper G S m b hm (by omega)
  · have hab' : a < b := by
      by_contra hn
      have he : a = b := by omega
      subst b
      exact h1 (by simpa using hc)
    obtain ⟨p, hpm, hpa, hpb, _⟩ :=
      KroneckerFrameIdentity.parameters_exist m a b hm (by omega) hab' hc
    have h : (p.m : ℤ) * euler (family G) p.m p.a p.b ≤
        (2 : ℤ) ^ (p.m * (p.a + p.b + 1)) := by
      rw [← finite_coloring_identity G A p]
      exact_mod_cast KroneckerScopedActualFrameUpper.connected_card_upper p
    simpa only [hpm, hpa, hpb] using h

theorem fundamental_log_bound (G : Geometry) (A : Application G)
    (S : FiniteEnumeration G)
    (m a b : ℕ) (hm : 3 ≤ m) (ha : 0 < a) (hab : a ≤ b) (hb : 2 * b ≤ m * a)
    (hc : a.Coprime b) (ht : tits m a b < 0) (hE : 0 < euler (family G) m a b) :
    Real.log (euler (family G) m a b : ℝ) ≤
      coefficient m * Real.sqrt (-(tits m a b : ℝ)) + error m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hE' : (0 : ℝ) < euler (family G) m a b := by exact_mod_cast hE
  have hmul : (m : ℝ) * (euler (family G) m a b : ℝ) ≤
      (2 : ℝ) ^ (m * (a + b + 1)) := by
    exact_mod_cast fundamental_multiplied_bound G A S m a b hm ha hab hc
  have hl := Real.log_le_log (mul_pos hm' hE') hmul
  rw [Real.log_mul (ne_of_gt hm') (ne_of_gt hE'), Real.log_pow] at hl
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hl
  have hred : Real.log (euler (family G) m a b : ℝ) ≤
      (m : ℝ) * ((a : ℝ) + b) * Real.log 2 + error m := by
    unfold error
    rw [Real.log_div (by positivity) (ne_of_gt hm'), Real.log_pow]
    nlinarith
  exact hred.trans (add_le_add
    (KroneckerFundamentalSqrtBound.linear_log_bound m a b hm hab hb ht) le_rfl)

theorem global_log_bound (G : Geometry) (A : Application G)
    (S : FiniteEnumeration G)
    (m a b : ℕ) (hm : 3 ≤ m) (hc : a.Coprime b) (ht : tits m a b < 0)
    (hE : 0 < euler (family G) m a b) :
    Real.log (euler (family G) m a b : ℝ) ≤
      coefficient m * Real.sqrt (-(tits m a b : ℝ)) + error m := by
  obtain ⟨c, d, hcpos, hcd, hd, hq, hg, he⟩ :=
    KroneckerFundamentalEulerReduction.reduction (finiteHomology G) m a b ht
  change Real.log (KroneckerOrdinarySingularEuler.ordinaryEuler
    (KroneckerCanonicalKroneckerModuli.space m a b) (finiteHomology G m a b) : ℝ) ≤ _
  rw [he, ← hq]
  apply fundamental_log_bound G A S m c d hm hcpos hcd hd
  · change Nat.gcd c d = 1
    rw [hg]
    exact hc
  · rw [hq]
    exact ht
  · change 0 < KroneckerOrdinarySingularEuler.ordinaryEuler
      (KroneckerCanonicalKroneckerModuli.space m a b) (finiteHomology G m a b) at hE
    rw [he] at hE
    exact hE

theorem finite_envelope (m : ℕ) (hm : 3 ≤ m)
    (p : Dimension (family KroneckerReadableMain.geometry) m) :
    0 ≤ value p ∧ value p ≤ bound m (slope p) + error m / (height p : ℝ) := by
  let G := KroneckerReadableMain.geometry
  let A := KroneckerReadableMain.counting
  let S := Classical.choice (finite_enumeration G)
  refine ⟨value_nonnegative G KroneckerReadableMain.localization m p, ?_⟩
  by_cases hp : slope p ∈ interior m
  · have hneg := (KroneckerIntegralInteriorCriterion.criterion m hm
      p.val.1 p.val.2 p.property.1).mp hp
    have hE := positiveEuler G KroneckerReadableMain.localization m hm
      p.val.1 p.val.2 p.property
    have h := global_log_bound G A S m p.val.1 p.val.2 hm p.property.2.2.1 hneg hE
    have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg p.val.1)
    rw [add_div] at hd
    dsimp only [KroneckerManuscriptTarget.value, KroneckerManuscriptTarget.slope,
      KroneckerManuscriptTarget.height]
    rw [KroneckerEnvelopeTitsNormalization.identity m p.val.1 p.val.2 hm p.property.1]
    exact hd
  · rw [KroneckerScopedActualFiniteEnvelope.outside_zero G m hm p hp]
    exact add_nonneg (KroneckerScopedActualFiniteEnvelope.bound_nonnegative m hm _)
      (div_nonneg (error_nonnegative m hm) (Nat.cast_nonneg _))

theorem finite_endpoint (m : ℕ) (hm : 3 ≤ m)
    (p : Dimension (family KroneckerReadableMain.geometry) m) :
    0 ≤ value p ∧ value p ≤
      (m : ℝ) * Real.log 2 * Real.sqrt (((m : ℝ) + 2) / ((m : ℝ) - 2)) *
        Real.sqrt (max ((m : ℝ) * slope p - 1 - slope p ^ 2) 0) +
      Real.log ((2 : ℝ) ^ m / (m : ℝ)) / (height p : ℝ) := by
  have h := finite_envelope m hm p
  have hs : ∀ x : ℝ, Real.sqrt (max x 0) = Real.sqrt x := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx]
    · rw [max_eq_right (le_of_not_ge hx), Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hx)]
  rw [hs]
  simpa only [bound, error, KroneckerSlopeSymmetry.root_gap_product
    (show (2 : ℝ) ≤ m by exact_mod_cast (show 2 ≤ m by omega)),
    KroneckerSlopeSymmetry.slopeQuadratic] using h

end
end KroneckerExplicitFiniteBound
