import KroneckerCitedGeometry
import KroneckerSchofieldNonemptiness
import KroneckerFiniteCoefficientIntegration
import KroneckerScopedDeleteMainAssembly

/-!
Readable main proof using the established Dimca and Schofield inputs.

For dimension `(a,b)`, `a` is the dimension at the source and `b` at the target.
The canonical model has `m` arrows from vertex `0` to vertex `1`.

1. King/Reineke + Dimca give the actual geometry directly.
2. Schofield gives nonemptiness and slope approximability.
3. Three source inputs derive finite enumeration. Three localization,
   positivity and adjacent-dimension inputs complete the growth estimates.
4. Joint limits and slope approximability give continuity and nonnegativity.

The combined declaration `theorem_1_1` includes the limit conclusion, Euler
positivity, and the nonemptiness criterion. The quantitative upper bound is
a separate corollary. There are eight external mathematical inputs. The
formal solution is constructed by coefficient recursion; BLMMR Theorem 3.2
and uniqueness give the common-series equality.
-/
noncomputable section
set_option autoImplicit false
namespace KroneckerReadableMain
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerLogic
open KroneckerScopedActualFrameApplication KroneckerScopedPublishedAdjacent

abbrev geometry := KroneckerCitedGeometry.geometry

/-- The canonical family, including its Euler invariant, is independent
of the proof used to supply finite homology. Thus the old and new geometry
constructions give definitionally identical manuscript statements. -/
theorem canonical_family_eq (G G' : Geometry) : family G = family G' := rfl

theorem localization : Weist geometry :=
  KroneckerPublishedInputBoundary.localizationAndPositivity geometry

theorem adjacent : Formula geometry := KroneckerPublishedInputBoundary.adjacent geometry

def counting : Application geometry :=
  KroneckerFiniteCoefficientIntegration.application geometry
    (Classical.choice (KroneckerFiniteCoefficientIntegration.finite_enumeration geometry))

theorem nonempty_domain : NonemptyDomain (family geometry) :=
  KroneckerSchofieldNonemptiness.nonempty_domain (finiteHomology geometry)

theorem slope_approximable : SlopeApproximable (family geometry) :=
  KroneckerSchofieldNonemptiness.slope_approximable (finiteHomology geometry)

/-- The same joint limits and finite estimates, with Schofield supplying
the nonvacuity needed for continuity and for passing bounds to the limit. -/
theorem main (m : ℕ) (hm : 3 ≤ m) : MainConclusion (family geometry) m := by
  let F := KroneckerScopedDeleteMainAssembly.profile geometry localization adjacent counting m hm
  have hj := KroneckerScopedDeleteMainAssembly.joint geometry localization adjacent counting m hm
  have hd := slope_approximable m hm
  refine ⟨F, continuousOn_of_jointLimits _ _ _ hj hd,
    KroneckerScopedDeleteMainAssembly.lower geometry localization adjacent counting m hm,
    KroneckerScopedDeleteMainAssembly.upper geometry localization adjacent counting m hm,
    KroneckerScopedDeleteMainAssembly.positive geometry localization adjacent counting m hm, ?_⟩
  intro r hr
  have hb := KroneckerLimitEnvelopeWithError.limit_bounds (family geometry) m
    (KroneckerScopedActualUniformError.error geometry m)
    (KroneckerScopedActualFiniteEnvelope.finite_envelope geometry counting m hm)
    r (F r) (hd r hr) (hj r hr)
  exact ⟨hb.1, hj r hr⟩

/-- The limit and continuity conclusion of Theorem 1.1. The combined
statement is `theorem_1_1`; the quantitative upper bound is
`KroneckerManuscriptEnvelope.profile_envelope`. -/
theorem semantic_main : AllMConclusion (family geometry) := main

theorem semantic_properties :
    NonemptyDomain (family geometry) ∧ SlopeApproximable (family geometry) ∧
      PositiveEuler (family geometry) :=
  ⟨nonempty_domain, slope_approximable, positiveEuler geometry localization⟩

/-- Theorem 1.1, including positivity of the Euler characteristics and the
nonemptiness criterion. The quantitative upper bound remains separate. -/
theorem theorem_1_1 :
    AllMConclusion (family geometry) ∧
      PositiveEuler (family geometry) ∧ NonemptyDomain (family geometry) :=
  ⟨semantic_main, semantic_properties.2.2, semantic_properties.1⟩

theorem actual_space (m a b : ℕ) :
    (family geometry).space m a b = KroneckerCanonicalKroneckerModuli.space m a b := rfl

end KroneckerReadableMain
#print axioms KroneckerReadableMain.canonical_family_eq
#print axioms KroneckerReadableMain.main
#print axioms KroneckerReadableMain.semantic_main
#print axioms KroneckerReadableMain.semantic_properties
#print axioms KroneckerReadableMain.theorem_1_1
#print axioms KroneckerReadableMain.actual_space
