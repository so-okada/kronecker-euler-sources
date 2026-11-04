import KroneckerPublishedPositionApplication
import KroneckerScopedPublishedAdjacent

/-! Explicit accepted literature boundary. These axioms are translated published
finite results, including the canonical analytic-moduli interpretation. They do
not assert a frame identity, deletion estimate, entropy limit, or main theorem.
See SOURCES.txt for the precise sources and translation obligations accepted here.
-/
noncomputable section
set_option autoImplicit false
namespace KroneckerPublishedInputBoundary
open KroneckerScopedModuli KroneckerApplicationScope
open KroneckerPublishedPositionApplication
open KroneckerScopedPublishedAdjacent
open scoped BigOperators

/-- The m = 3 instance of Weist, published Corollary 3.16 (arXiv v2 Corollary 3.14),
transported to finite-support word-cover data and translation classes. -/
axiom weist_localization (G : Geometry) :
  ∀ a b : ℕ, Acyclic (KroneckerWeistApplicationGates.base a b) →
    Connected (KroneckerWeistApplicationGates.base a b) →
    Nonzero (KroneckerWeistApplicationGates.base a b) →
    Balanced (KroneckerWeistApplicationGates.base a b) →
    ∀ (rep : Class (KroneckerWeistApplicationGates.base a b) →
      (wordCover (KroneckerWeistApplicationGates.base a b)).V →₀ ℕ),
      (∀ q, Quotient.mk (translationSetoid (KroneckerWeistApplicationGates.base a b))
        (rep q) = q) →
      G.euler (KroneckerWeistApplicationGates.base a b) =
        ∑ᶠ q, localizationTerm G a b (rep q)

/-- King-Walter Theorem 3(c), with King's smooth projective fine moduli
construction, specialized to the nonempty Euler consequence. Alternatively
Weist Corollary 3.11 implies this statement directly. Indivisible means
coprime FOR THE WEIGHT, as defined in KroneckerPublishedModuli. -/
axiom king_walter_positive (G : Geometry) :
  ∀ (D : Datum) [Covered D], Acyclic D → Nonzero D → Balanced D →
    Indivisible D → Nonempty (G.space D) → 1 ≤ G.euler D

/-- Weist Theorem 6.6: the exact finite adjacent formula, with no asymptotic
assertion. -/
axiom weist_adjacent (G : Geometry) (m a : ℕ) :
  3 ≤ m → 0 < a →
    (G.euler (KroneckerAllMPublishedDatum.datum m a (a+1)) : ℝ) =
      (m : ℝ) / (((a : ℝ)+1)*(((m-1 : ℕ) : ℝ)*a+m)) *
        ((((m-1)^2*a+(m-1)*m).choose a : ℕ) : ℝ)

def localizationAndPositivity (G : Geometry) : Weist G where
  localization := weist_localization G
  positive := king_walter_positive G

def adjacent (G : Geometry) : Formula G where
  finite := weist_adjacent G

end KroneckerPublishedInputBoundary
