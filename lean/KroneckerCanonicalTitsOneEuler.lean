import KroneckerCanonicalTitsNecessary

/-! At Tits value one a nonempty actual stable orbit space is a singleton.
Its finite singular homology and Euler one are internal, for every m. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalTitsOneEuler
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
open scoped BigOperators

theorem singleton (m a b : ℕ) (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1) :
    Subsingleton (space m a b) := by
  apply KroneckerStableOrbitEuler.stableOrbit_subsingleton
  have H : m*(a*b)<a*a+b*b := by nlinarith
  simpa [Fin.sum_univ_two,dimension,source,target] using H

theorem admissible (m a b : ℕ) (hn : Nonempty (space m a b))
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1) : Admissible (space m a b) := by
  let := hn
  let := singleton m a b ht
  exact singleton_admissible _

theorem euler_one (m a b : ℕ) (hn : Nonempty (space m a b))
    (ht : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=1) (h : Admissible (space m a b)) :
    ordinaryEuler (space m a b) h=1 := by
  let := hn
  let := singleton m a b ht
  exact ordinaryEuler_singleton _
end KroneckerCanonicalTitsOneEuler
