import KroneckerCanonicalClosedApproximableFromFundamental

/-!
Schofield's established nonemptiness result, followed by short Lean deductions.

Sources: Schofield, Birational classification of moduli spaces of
representations of quivers, Indag. Math. 12 (2001), Theorem 4.1, p. 417;
Schofield, General representations of quivers, Proc. London Math. Soc. 65
(1992), Theorem 6.1 and the following discussion, p. 62 (directly checked
in the uploaded original). The exact Kronecker consequence is also proved in Reineke, Wild
quantum dilogarithm identities, Ann. Repr. Th. 1 (2024), Theorems 2.7(1)
and 4.1(1), with the Schofield application on p. 390.

The only new external assertion is existence for positive imaginary-root
dimensions, without a coprimality hypothesis. Necessity and the real-root
case reuse internal proofs. No Euler characteristic or entropy is imported.
-/
noncomputable section
set_option autoImplicit false
namespace KroneckerSchofieldNonemptiness
open KroneckerCanonicalKroneckerModuli KroneckerFiniteQuiverHom
open KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerNegativeTitsSymmetry

/-- External Schofield--Reineke Kronecker corollary, translated to the actual
matrix representation and weight used in this project. -/
axiom schofield_imaginary_stable (m a b : ℕ) :
    3 ≤ m → 0 < a → 0 < b →
    (a : ℤ)^2 + (b : ℤ)^2 - (m : ℤ)*a*b ≤ 0 →
    ∃ R : Representation (source m) (target m) (dimension a b),
      Stable (character a b) R

/-- For arrows from the a-dimensional source to the b-dimensional target,
Schofield's antisymmetric Euler form is the negative of m times our weight. -/
theorem schofield_euler_difference (m a b u v : ℤ) :
    (u*a+v*b-m*u*b) - (a*u+b*v-m*a*v) = m*(a*v-b*u) := by ring

/-- The positive inequality in Schofield 1992, Theorem 6.1, is precisely
the negative-weight stability convention of this project. -/
theorem schofield_stability_sign (m a b u v : ℤ) (hm : 0 < m) :
    0 < (u*a+v*b-m*u*b) - (a*u+b*v-m*a*v) ↔ b*u-a*v < 0 := by
  rw [schofield_euler_difference, mul_pos_iff_of_pos_left hm, sub_pos, sub_neg]

/-- Reineke uses dimensions (b,a) for arrows 2 -> 1. Cross-multiplying
his slope inequality gives exactly the sign of our weight b*u-a*v. -/
theorem stability_cross_product (m a b u v : ℤ) :
    m*(u-v)*(a+b) - m*(a-b)*(u+v) = 2*m*(b*u-a*v) := by ring

theorem stability_sign (m a b u v : ℤ) (hm : 0 < m) :
    m*(u-v)*(a+b) - m*(a-b)*(u+v) < 0 ↔ b*u-a*v < 0 := by
  rw [stability_cross_product]
  simpa only [mul_zero] using
    (mul_lt_mul_iff_right₀ (b := b*u-a*v) (c := 0) (by positivity : 0 < 2*m))

theorem imaginary_nonempty (m a b : ℕ) (hm : 3 ≤ m)
    (ha : 0 < a) (hb : 0 < b)
    (hq : (a : ℤ)^2 + (b : ℤ)^2 - (m : ℤ)*a*b ≤ 0) :
    Nonempty (space m a b) :=
  (space_nonempty_iff m a b).mpr (schofield_imaginary_stable m a b hm ha hb hq)

/-- Full positive-dimension criterion; coprimality is unnecessary here. -/
theorem nonempty_iff (m a b : ℕ) (hm : 3 ≤ m) (ha : 0 < a) (hb : 0 < b) :
    Nonempty (space m a b) ↔ (a : ℤ)^2 + (b : ℤ)^2 - (m : ℤ)*a*b ≤ 1 := by
  constructor
  · exact KroneckerCanonicalTitsNecessary.tits_le_one m a b ha
  · intro hq
    by_cases hi : (a : ℤ)^2 + (b : ℤ)^2 - (m : ℤ)*a*b ≤ 0
    · exact imaginary_nonempty m a b hm ha hb hi
    · exact KroneckerRealRootRealization.nonempty m hm a b (by omega)

variable (H : ∀ m a b, Admissible (space m a b))

theorem nonempty_domain : NonemptyDomain (KroneckerCanonicalKroneckerModuli.family H) := by
  intro m hm a b ha hb _
  exact nonempty_iff m a b hm ha hb

/-- The existing arithmetic slope sequences now use Schofield's existence
input instead of the central-strip constructive nonemptiness induction. -/
theorem slope_approximable : SlopeApproximable (KroneckerCanonicalKroneckerModuli.family H) := by
  intro m hm r hr
  apply KroneckerCanonicalClosedApproximableFromFundamental.approximable H m hm
    (fun c d hc hcd _ _ hq => ?_) r hr
  exact imaginary_nonempty m c d hm hc (lt_of_lt_of_le hc hcd) (le_of_lt hq)

end KroneckerSchofieldNonemptiness
#print axioms KroneckerSchofieldNonemptiness.schofield_stability_sign
#print axioms KroneckerSchofieldNonemptiness.nonempty_iff
#print axioms KroneckerSchofieldNonemptiness.slope_approximable
