import KroneckerBoundaryListComparison
import KroneckerExchangeIntermediateLemma
import KroneckerBinaryFactorLemmas
import KroneckerApproachingDimensionReduction
import KroneckerFractionalPartEstimates
import KroneckerCurrentMechanicalNotation
import KroneckerBoundedMechanicalEdits
import KroneckerMechanicalEditsStatement
import KroneckerRestrictedIntegerLimits
import KroneckerCompositionMap
import KroneckerRecolCollars
import KroneckerWitnessPreparedComparison
import KroneckerManuscriptGradeRecovery
import KroneckerManuscriptExplicitNotation
import KroneckerExample25Classification
import KroneckerExample25Count
import KroneckerManuscriptBadFactors
import KroneckerManuscriptCentralNotation
import KroneckerManuscriptGradingSets
import KroneckerExplicitShellGrading
import KroneckerRecolorConstructions
import KroneckerManuscriptRunEditList
import KroneckerExchangeRecolor
import KroneckerManuscriptOuterExtension
import KroneckerManuscriptPeriodic
import KroneckerManuscriptShell
import KroneckerAmbientShadows
import KroneckerManuscriptShadowNodes
import KroneckerNaturalTightness
import KroneckerNaturalShadowNodes
import KroneckerCurrentDyckDefinitions
import KroneckerCurrentShadowDefinitions
import KroneckerEndpointDifferences
import KroneckerManuscriptRun
import KroneckerCurrentLimitStatements
import InsertionConventionCheck

/-! Entry point for the current manuscript (24 October 2026).
Ordinary subpaths use geometric positions; cyclic subpaths use ordered ambient
edge names; NEReal keeps their directions, grades, colors, and correspondence.
Unrestricted gradings and both signed tightness clauses are exposed in
KroneckerNaturalPathGradings. Colors recover the finite counting core by a
proved equivalence.
The current interface includes pi, TCG, Start_pt, End_pt, Start_NE, End_NE, NGrDiff, EGrDiff,
the concrete zero extension in Lemma 2.24, calU and its run-count identity,
G, G_h, Diff, recoveryGrading, Col, CtdG, CtdG_h, Recol,
the shell path and its pointwise grading, explicit recolored constructions,
the four run-edit primitives and their ordered lists, the outer-extension recovery map,
the three periodic-growth claims followed by ell, the bad-factor estimate,
the (2,5) example, the central Euler notation and limits, run-factors, run phases,
the named map i_d with grade and color recovery, and the marked-slot counts.
The 24 October adapters expose one-based RunFactor, Dbad(W,p,q), the
restricted integer-limit set and one-sided domains, the composition map with
its fibre bound, and Definition 6.2, the fractional-part estimates in Lemma 6.3, and
Lemma 6.5 with admissible lengths and bounded run-edits.
The extraction in Sections 9 and 10 exposes boundary-list comparison (9.2),
the connected-grading exchange and its recoverable index (9.3), mechanical
factor comparison (9.10), final-factor completion (9.11), and sequence-level
dimension reduction (10.1). The dependent results are 9.4, 9.12, and 10.2.
The seven external interfaces and the Theorem 1.1 target are not modified. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerPaperPathGradings
open KroneckerPaperPaths KroneckerPredecessor KroneckerPaperTraceBridge

/-- Lemma 2.24(1): every positive horizontal occurrence in NEReal has its first
closing node, and the initial node fills the realization. -/
theorem NEReal_shadow_nodes {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (hs : AmbientFirstShadow g u v) :
    let U := sample (geometricTrace (NERealGrading g u v)) (cyclicLength u v)
    ∃ p : Fin (cyclicLength u v) → Fin (cyclicLength u v),
      ValidThrough U p (cyclicLength u v) ∧ KroneckerPaperConnected.FullRoot U p ∧
      ∀ x, KroneckerPredecessor.IsHorizontal U x → 0 < (U x).grade →
        ∃ z, KroneckerPredecessor.IsNode U p x z ∧
          intervalVerticalCount U x.val (z.val+1) = intervalHorizontalGrade U x.val (z.val+1) ∧
          ∀ k, x.val < k → k ≤ z.val →
            intervalVerticalCount U x.val k < intervalHorizontalGrade U x.val k :=
  firstShadow_all_nodes g u v ((ambientFirstShadow_iff g u v).mp hs)

end KroneckerPaperPathGradings
