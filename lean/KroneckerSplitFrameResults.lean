import KroneckerManuscriptRun

/-! The run length lemma precedes the Euler identity. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerSplitFrameResults
open KroneckerPaperPaths KroneckerNaturalPathGradings
open KroneckerFrameIdentity KroneckerFrameBadDensity KroneckerFrameWord
open KroneckerFramePrefix KroneckerMechanicalWords

open KroneckerManuscriptRun

theorem first_runs_vertical_count (a b d₁ : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hd : 0 < d₁) :
    ((runLengths a b d₁).take a).sum = b-1 :=
  KroneckerManuscriptRun.first_runs_vertical_count a b d₁ ha hb hd

theorem counting_colored_gradings (p : Parameters) :
    (connectedCount p.m (calU p.a p.b p.d₁) 0 : ℤ) =
      (p.m : ℤ) * KroneckerManuscriptTarget.euler
        (KroneckerScopedCanonicalPublishedEuler.family KroneckerReadableMain.geometry)
        p.m p.a p.b :=
  KroneckerManuscriptRun.counting_colored_gradings p

end KroneckerSplitFrameResults
#print axioms KroneckerSplitFrameResults.first_runs_vertical_count
#print axioms KroneckerSplitFrameResults.counting_colored_gradings
