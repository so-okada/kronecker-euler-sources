import KroneckerLogic
import KroneckerEndpointRoots
import KroneckerOrdinarySingularEuler

/-!
Target contract for manuscript Theorem 1.1 (`thm:main`).
This file DEFINES the goal; it does not prove it. In particular no arbitrary
family below is asserted to be the actual Kronecker stable-moduli family.
The construction/identification of that family is obligation G01.
All published and manuscript-specific proof inputs are tracked separately.
The quantitative upper bound is a separate corollary.
-/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptTarget
open KroneckerOrdinarySingularEuler KroneckerEndpointRoots KroneckerLogic

/-- Candidate topological moduli family. Completion requires its identification
with the analytic spaces of stable complex m-Kronecker moduli, with weight
`a*v-b*u > 0` on every proper nonzero subrepresentation. Merely constructing
an inhabitant of this structure does NOT discharge that identification. -/
structure ModuliFamily where
  space : ℕ → ℕ → ℕ → TopCat.{0}
  finiteHomology : ∀ m a b, Admissible (space m a b)

def euler (M : ModuliFamily) (m a b : ℕ) : ℤ :=
  ordinaryEuler (M.space m a b) (M.finiteHomology m a b)

/-- This uses actual nonemptiness of the supplied space, not the arithmetic
nonempty-domain theorem, whose proof is a separate obligation. -/
def Allowed (M : ModuliFamily) (m a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ Nonempty (M.space m a b)

abbrev Dimension (M : ModuliFamily) (m : ℕ) :=
  {p : ℕ × ℕ // Allowed M m p.1 p.2}

def height {M : ModuliFamily} {m : ℕ} (p : Dimension M m) : ℕ := p.val.1
def slope {M : ModuliFamily} {m : ℕ} (p : Dimension M m) : ℝ :=
  (p.val.2 : ℝ) / p.val.1
def value {M : ModuliFamily} {m : ℕ} (p : Dimension M m) : ℝ :=
  Real.log (euler M m p.val.1 p.val.2 : ℝ) / p.val.1

def interval (m : ℕ) : Set ℝ := Set.Icc (lowerRoot m) (upperRoot m)
def interior (m : ℕ) : Set ℝ := Set.Ioo (lowerRoot m) (upperRoot m)
def bound (m : ℕ) (r : ℝ) : ℝ :=
  (m : ℝ) * Real.log 2 * Real.sqrt (((m : ℝ) + 2) / ((m : ℝ) - 2)) *
    Real.sqrt ((upperRoot m - r) * (r - lowerRoot m))

/-- A real-valued extension off I_m is harmless: only its restriction to I_m
is constrained. Nonnegativity encodes the manuscript's codomain R_{>=0};
finiteness follows because F is real-valued. JointLimit covers every admissible
sequence, including exterior real-root dimensions approaching the endpoints. -/
def MainConclusion (M : ModuliFamily) (m : ℕ) : Prop :=
  ∃ F : ℝ → ℝ,
    ContinuousOn F (interval m) ∧
    F (lowerRoot m) = 0 ∧ F (upperRoot m) = 0 ∧
    (∀ r ∈ interior m, 0 < F r) ∧
    (∀ r ∈ interval m,
      0 ≤ F r ∧
      JointLimit (height (M := M) (m := m)) slope value r (F r))

def AllMConclusion (M : ModuliFamily) : Prop :=
  ∀ m : ℕ, 3 ≤ m → MainConclusion M m

/-- Separate semantic gate: real logarithms in the intended theorem are of
strictly positive Euler characteristics. Lean's total Real.log does not supply
this condition automatically. -/
def PositiveEuler (M : ModuliFamily) : Prop :=
  ∀ m, 3 ≤ m → ∀ a b, Allowed M m a b → 0 < euler M m a b

/-- Nonvacuity is checked independently of the joint-limit implication. -/
def SlopeApproximable (M : ModuliFamily) : Prop :=
  ∀ m, 3 ≤ m → ∀ r ∈ interval m,
    Approximable (height (M := M) (m := m)) slope r

/-- Companion claim eq:nonempty-domain, not silently used in Allowed. -/
def NonemptyDomain (M : ModuliFamily) : Prop :=
  ∀ m, 3 ≤ m → ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    (Nonempty (M.space m a b) ↔
      (a : ℤ)^2 + (b : ℤ)^2 - (m : ℤ) * a * b ≤ 1)

end KroneckerManuscriptTarget
