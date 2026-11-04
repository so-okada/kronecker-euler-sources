import KroneckerCanonicalReflectionHomeomorphism
import KroneckerHomologyHomeomorphism

/- Original module: KroneckerCanonicalReflectionHomology -/
section
/-! Reflection induces isomorphisms of ordinary rational singular homology
in every degree, and hence preserves the actual Betti numbers. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionHomology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
def homology (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) (n : ℕ) :=
  homologyIso (TopCat.isoOfHomeo (KroneckerCanonicalReflectionHomeomorphism.homeomorph m a b ha hb)) n
theorem betti (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) (n : ℕ) :
    KroneckerOrdinarySingularEuler.betti (space m a b) n =
      KroneckerOrdinarySingularEuler.betti (space m (m*a-b) a) n :=
  betti_iso (TopCat.isoOfHomeo (KroneckerCanonicalReflectionHomeomorphism.homeomorph m a b ha hb)) n
end KroneckerCanonicalReflectionHomology
end
end

/- Original module: KroneckerCanonicalReflectionEuler -/
section
/-! Actual homological finiteness and ordinary singular Euler are invariant
under reflection, now justified by the proved canonical homeomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionEuler
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
theorem admissible_iff (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) :
    Admissible (space m a b) ↔ Admissible (space m (m*a-b) a) :=
  KroneckerHomologyHomeomorphism.admissible_iff
    (KroneckerCanonicalReflectionHomeomorphism.homeomorph m a b ha hb)
theorem euler_eq (m a b : ℕ) (ha : 0<a) (hb : b≤m*a)
    (h : Admissible (space m a b)) (h' : Admissible (space m (m*a-b) a)) :
    ordinaryEuler (space m a b) h = ordinaryEuler (space m (m*a-b) a) h' :=
  KroneckerHomologyHomeomorphism.euler_eq
    (KroneckerCanonicalReflectionHomeomorphism.homeomorph m a b ha hb) h h'
end KroneckerCanonicalReflectionEuler
end
end
