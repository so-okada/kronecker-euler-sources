import KroneckerScopedCanonicalGeometry

/-!
Readable geometric input for the canonical stable-moduli spaces.

External sources: King, Q. J. Math. 45 (1994), Theorem 4.1 and Proposition
4.3; the analytic principal-fibration interpretation in Reineke's quiver
moduli survey, Proposition 3.5 and section 3.5; and Dimca, Singularities and
Topology of Hypersurfaces (1992), Chapter 1, Corollary (6.10), p. 27.

Dimca supplies finite CW homotopy type, hence finite-dimensional rational
homology with finite support. The quotient presentation is the separate
King/Reineke component. This named external COROLLARY includes the checked
translation to the definitions below; it is not an internal proof of GIT or
of Dimca's theorem. See SOURCES.txt for the exact hypotheses and translation.
-/
noncomputable section
set_option autoImplicit false
namespace KroneckerCitedGeometry
open KroneckerPublishedModuli KroneckerApplicationScope
open KroneckerScopedRealization KroneckerScopedCanonicalGeometry

/-- Accepted quotient and finiteness corollary from King (4.1 and 4.3),
Reineke 2008 (3.5 and Sec 3.5), and Dimca (6.10).
There is no coprimality or projectivity assumption on the stable locus.
There is no `Covered D` hypothesis: the broad acyclic, balanced form is also
used by `KroneckerFiniteEnumerationSourceSplit.bipartiteEuler` for the complete
bipartite K(m,m) data. -/
axiom king_dimca_realization (D : Datum) :
    Acyclic D → Balanced D → Nonempty (Realization D)

theorem covered_balanced (D : Datum) [Covered D] : Balanced D := by
  rcases covered_cases D with ⟨m,a,b,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,d,hc,rfl⟩
  · exact KroneckerAllMPublishedDatum.balanced m a b
  · exact KroneckerWeistApplicationGates.base_balanced a b
  · exact KroneckerWeistApplicationGates.cover_balanced a b d
      ((KroneckerWeistApplicationGates.compatible_dictionary a b d).mp hc)

/-- Transport the cited finite homology directly to the canonical quotient. -/
theorem canonicalFinite : CanonicalFinite := by
  intro D hD
  obtain ⟨R⟩ := king_dimca_realization D (covered_acyclic D) (covered_balanced D)
  exact R.canonicalAdmissible

/-- Direct construction; no projective-space or residual-case detour. -/
def geometry : KroneckerScopedModuli.Geometry := canonicalGeometry canonicalFinite

theorem actual_space (D : Datum) : geometry.space D = canonical D := rfl

end KroneckerCitedGeometry
#print axioms KroneckerCitedGeometry.canonicalFinite
#print axioms KroneckerCitedGeometry.actual_space
