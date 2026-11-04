import KroneckerExchangeOrbitHomeomorphism

/-! Source/sink exchange preserves actual nonemptiness, finite singular homology
and Euler; these are now proved symmetries of the canonical moduli family. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeEuler
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler

theorem nonempty_iff (m a b : ℕ) : Nonempty (space m a b) ↔ Nonempty (space m b a) :=
  (KroneckerExchangeOrbitHomeomorphism.homeomorph m a b).toEquiv.nonempty_congr

theorem admissible_iff (m a b : ℕ) : Admissible (space m a b) ↔ Admissible (space m b a) :=
  KroneckerHomologyHomeomorphism.admissible_iff (KroneckerExchangeOrbitHomeomorphism.homeomorph m a b)

theorem euler_eq (m a b : ℕ) (h : Admissible (space m a b)) (h' : Admissible (space m b a)) :
    ordinaryEuler (space m a b) h=ordinaryEuler (space m b a) h' :=
  KroneckerHomologyHomeomorphism.euler_eq (KroneckerExchangeOrbitHomeomorphism.homeomorph m a b) h h'
end KroneckerExchangeEuler
