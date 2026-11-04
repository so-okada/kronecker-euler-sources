import KroneckerNaturalTightness
import KroneckerReadableMain

/-! Definition 2.25 and Proposition 2.26: the run U(a,b), its natural-valued
colored grading count, and the Euler-characteristic identity. The declarations
retain the explicit parameter d1. For the manuscript, specialize d1 to a+t,
where t is the unique integer with 0<t<a and b*t mod a=1. Then
KroneckerFrameSlope.frameSlope a b d1 is Gamma(a,b). -/
set_option autoImplicit false
noncomputable section
namespace KroneckerManuscriptRun
open KroneckerPaperPaths KroneckerNaturalPathGradings
open KroneckerFrameIdentity KroneckerFrameBadDensity KroneckerFrameWord
open KroneckerFramePrefix KroneckerMechanicalWords

/-- Vertical lengths of the simple runs of calU(a,b). -/
abbrev runLengths (a b d₁ : ℕ) : List ℕ := frameWord a b d₁

/-- The run U(a,b) of Definition 2.25, specialized at its d1=a+t. -/
def calU (a b d₁ : ℕ) : TNEPath := runPath (runLengths a b d₁) 0

theorem runLengths_length (a b d₁ : ℕ) : (runLengths a b d₁).length = a+1 :=
  frameWord_length a b d₁

theorem runLengths_sum (a b d₁ : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d₁) :
    (runLengths a b d₁).sum = b := frameWord_sum a b d₁ ha hb hd

theorem first_runs_vertical_count (a b d₁ : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hd : 0 < d₁) :
    ((runLengths a b d₁).take a).sum = b-1 := by
  simpa [runLengths, frameWord, List.take_append, mechanicalWord_length] using
    frame_mechanical_sum a b d₁ ha hb hd

theorem connectedCount_calU (m a b d₁ d : ℕ) :
    connectedCount m (calU a b d₁) d =
      KroneckerWordCounts.runCount m (runLengths a b d₁) d := by
  rw [connectedCount_eq_pathCount]
  rfl

/-- Claim 2 of Proposition 2.26, for the actual Euler invariant. -/
theorem counting_colored_gradings (p : Parameters) :
    (connectedCount p.m (calU p.a p.b p.d₁) 0 : ℤ) =
      (p.m : ℤ) * KroneckerManuscriptTarget.euler
        (KroneckerScopedCanonicalPublishedEuler.family KroneckerReadableMain.geometry)
        p.m p.a p.b := by
  rw [connectedCount_calU]
  exact KroneckerScopedActualFrameApplication.literal_identity
    KroneckerReadableMain.geometry KroneckerReadableMain.counting p

end KroneckerManuscriptRun
