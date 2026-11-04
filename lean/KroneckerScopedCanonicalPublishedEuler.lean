import KroneckerScopedModuli

/-! Actual ordinary-Euler positivity for the canonical all-m family, relative
only to the explicit general Geometry input and Weist's positivity theorem.
This removes an independent numerical positivity premise. Geometry itself
is still unconstructed, and no entropy-limit existence is asserted. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedCanonicalPublishedEuler
open KroneckerScopedModuli KroneckerOrdinarySingularEuler
open KroneckerAllMPublishedDatum KroneckerCanonicalKroneckerModuli
open KroneckerManuscriptTarget

def finiteHomology (G : Geometry) (m a b : ℕ) : Admissible (space m a b) :=
  G.canonicalAdmissible (datum m a b)

def family (G : Geometry) : ModuliFamily :=
  KroneckerCanonicalKroneckerModuli.family (finiteHomology G)

theorem published_nonempty (G : Geometry) (m a b : ℕ)
    (h : Nonempty (space m a b)) : Nonempty (G.space (datum m a b)) :=
  h.map (G.comparison (datum m a b))

theorem euler_comparison (G : Geometry) (m a b : ℕ) :
    euler (family G) m a b = G.euler (datum m a b) :=
  G.euler_comparison (datum m a b)

theorem euler_ge_one (G : Geometry) (W : Weist G) (m a b : ℕ)
    (ha : 0 < a) (hc : a.Coprime b) (h : Nonempty (space m a b)) :
    1 ≤ euler (family G) m a b := by
  rw [euler_comparison]
  exact W.positive _ (acyclic m a b) (nonzero_of_source m a b ha)
    (balanced m a b) (indivisible m a b hc) (published_nonempty G m a b h)

theorem positiveEuler (G : Geometry) (W : Weist G) : PositiveEuler (family G) := by
  intro m _ a b h
  exact lt_of_lt_of_le (by norm_num : (0 : ℤ) < 1)
    (euler_ge_one G W m a b h.1 h.2.2.1 h.2.2.2)

theorem log_nonnegative (G : Geometry) (W : Weist G) (m : ℕ)
    (p : Dimension (family G) m) :
    0 ≤ Real.log (euler (family G) m p.val.1 p.val.2 : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast euler_ge_one G W m p.val.1 p.val.2
    p.property.1 p.property.2.2.1 p.property.2.2.2

theorem value_nonnegative (G : Geometry) (W : Weist G) (m : ℕ)
    (p : Dimension (family G) m) : 0 ≤ value p :=
  div_nonneg (log_nonnegative G W m p) (Nat.cast_nonneg _)

end KroneckerScopedCanonicalPublishedEuler
