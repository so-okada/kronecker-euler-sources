import KroneckerScopedDeleteActualCentral
import KroneckerExchangeEuler
import KroneckerCanonicalReflectionEuler
import KroneckerReflectionPrimitive

set_option autoImplicit false
noncomputable section
namespace KroneckerManuscriptFiniteStatements
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler KroneckerManuscriptTarget
open KroneckerScopedActualFrameApplication KroneckerScopedPublishedAdjacent
open KroneckerScopedWeistCentralLowerLimit

theorem euler_symmetries (G : Geometry) (m a b : ℕ) (ha : 0 < a) (hb : b < m * a) :
    euler (family G) m a b = euler (family G) m b a ∧
      euler (family G) m b a = euler (family G) m a (m * a - b) := by
  have he (x y : ℕ) : euler (family G) m x y = euler (family G) m y x :=
    KroneckerExchangeEuler.euler_eq m x y (finiteHomology G m x y) (finiteHomology G m y x)
  have hr : euler (family G) m a b = euler (family G) m (m * a - b) a :=
    KroneckerCanonicalReflectionEuler.euler_eq m a b ha hb.le
      (finiteHomology G m a b) (finiteHomology G m (m * a - b) a)
  exact ⟨he a b, (he a b).symm.trans (hr.trans (he (m * a - b) a))⟩

theorem coprime_symmetries (m a b : ℕ) (hb : b ≤ m * a) :
    (a.Coprime b ↔ b.Coprime a) ∧ (a.Coprime b ↔ a.Coprime (m * a - b)) := by
  exact ⟨Nat.coprime_comm, (KroneckerReflectionPrimitive.coprime_iff m a b hb).symm.trans
    Nat.coprime_comm⟩

theorem quadratic_symmetries (m a b : ℕ) (hb : b ≤ m * a) :
    (m : ℤ) * b * a - (b : ℤ)^2 - (a : ℤ)^2 =
      (m : ℤ) * a * b - (a : ℤ)^2 - (b : ℤ)^2 ∧
    (m : ℤ) * a * (m * a - b : ℕ) - (a : ℤ)^2 - ((m * a - b : ℕ) : ℤ)^2 =
      (m : ℤ) * a * b - (a : ℤ)^2 - (b : ℤ)^2 := by
  rw [Nat.cast_sub hb]
  push_cast
  constructor <;> ring

theorem central_finite_comparison (G : Geometry) (A : Application G) (F : Formula G)
    (a r : ℕ) (hr : 2 ≤ r) (hra : 2 * r ≤ a) (hc : a.Coprime r) :
    E G a r ≤ ((a+r).choose (r-1) : ℝ) * 64^(r-1) * E G (a+8*r-6) 1 ∧
    ((a+r).choose (r-1) : ℝ) * 64^(r-1) * E G (a+8*r-6) 1 ≤
      (4096/729 : ℝ) * ((a+r).choose (r-1) : ℝ) * 64^(r-1) *
        (256/27 : ℝ)^(a+8*r-6) := by
  refine ⟨KroneckerScopedDeleteActualFinite.finite_comparison G A a r
    (by omega) (by omega) (by omega) hc, ?_⟩
  have h := mul_le_mul_of_nonneg_left
    (KroneckerScopedDeleteActualUpper.actual_adjacent_upper G F (a+8*r-6) (by omega))
    (by positivity : (0 : ℝ) ≤ ((a+r).choose (r-1) : ℝ) * 64^(r-1))
  convert h using 1
  ring

end KroneckerManuscriptFiniteStatements
