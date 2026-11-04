import KroneckerRecolDeleteComposition
import KroneckerRecolConcatenation

set_option autoImplicit false
noncomputable section
namespace KroneckerRecolCollars
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerColoring KroneckerWordCounts KroneckerColoredShell KroneckerCollarColoring
open KroneckerRecolShell

def automatic {m : ℕ} (X : TNEPath) (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (b : ColoredGrading m X) : ColoredGrading m (KroneckerManuscriptShell.path X u v) :=
  KroneckerManuscriptShell.coloring X b.1 b.2 u v 1 (if c=0 then 0 else 1)
    (by omega) (by omega) (by split_ifs <;> omega)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem automatic_eq {m : ℕ} (X : TNEPath) (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (g : Coloring m X.steps.length) :
    automatic X u v c hm hu hv (fromPalette X g) =
      fromPalette _ (KroneckerAutomaticShell.autoColoring u v c hm hu hv X.steps g) := by
  by_cases hc : c=0
  · simp only [automatic, KroneckerAutomaticShell.autoColoring, hc, ite_true]
    exact explicit_shell_eq X u v 1 0 (by omega) (by omega) (by omega) hv.1 g
  · simp only [automatic, KroneckerAutomaticShell.autoColoring, hc, ite_false]
    exact explicit_shell_eq X u v 1 1 (by omega) (by omega) (by omega) hv.1 g

/-- Each outer layer is the explicit preserving or draining shell from Definition 3.1. -/
inductive Execution {m : ℕ} (hm : 3 ≤ m) (U : List Bool) (source : ColoredGrading m (ofSteps U 0))
    (c : ℕ) : (pairs : List (ℕ×ℕ)) → ColoredGrading m (ofSteps (collarPath pairs U) 0) → Prop
  | nil : Execution hm U source c [] source
  | cons (p : ℕ×ℕ) (pairs : List (ℕ×ℕ))
      (hu : 1 ≤ p.1 ∧ p.1 ≤ m-1) (hv : 1 ≤ p.2 ∧ p.2 ≤ m-1)
      (b : ColoredGrading m (ofSteps (collarPath pairs U) 0))
      (h : Execution hm U source c pairs b) :
      Execution hm U source c (p::pairs)
        (automatic _ p.1 p.2 (c-pairs.length) hm hu hv b)

theorem collar_execution {m : ℕ} (hm : 3 ≤ m) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs)
    (c : ℕ) (U : List Bool) (g : Coloring m U.length) :
    Execution hm U (fromPalette (ofSteps U 0) g) c pairs
      (fromPalette (ofSteps (collarPath pairs U) 0) (collarColoring hm pairs hp c U g)) := by
  induction pairs with
  | nil => exact Execution.nil
  | cons p pairs ih =>
    have h := Execution.cons p pairs (hp p (by simp)).1 (hp p (by simp)).2 _
      (ih (fun q hq => hp q (by simp [hq])))
    have he := automatic_eq (ofSteps (collarPath pairs U) 0) p.1 p.2 (c-pairs.length) hm
      (hp p (by simp)).1 (hp p (by simp)).2
      (collarColoring hm pairs (fun q hq => hp q (by simp [hq])) c U g)
    exact (congrArg (Execution hm U (fromPalette (ofSteps U 0) g) c (p::pairs)) he).mp h

/-- Both the edit program and its surplus-removing collars are literal Recol executions. -/
theorem zero_mixed_execution {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m)
    {U V : List Bool} {K A D : ℕ} (p : KroneckerMixedPrograms.MixedProgram m U V K A D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    let out := KroneckerWitnessMixedExecution.runMixed rule hm p 0 g
    KroneckerRecolComposition.Execution hm U (fromPalette (ofSteps U 0) g.val) p
      (fromPalette (ofSteps V 0) out.2.val) ∧
    Execution (by omega) V (fromPalette (ofSteps V 0) out.2.val) out.1 pairs
      (fromPalette (ofSteps (collarPath pairs V) 0)
        (KroneckerWitnessZeroMixed.zeroMixed rule hm p pairs hp hs g).val) := by
  exact ⟨KroneckerRecolComposition.run_execution rule hm p 0 g,
    collar_execution (by omega) pairs hp _ V _⟩

theorem zero_delete_execution {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m)
    {U V : List Bool} {D : ℕ} (p : KroneckerDeleteVerticalPrograms.Program m U V D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    let out := KroneckerWitnessDeleteProgramExecution.runProgram rule hm p 0 g
    KroneckerRecolDeleteComposition.Execution hm U (fromPalette (ofSteps U 0) g.val) p
      (fromPalette (ofSteps V 0) out.2.val) ∧
    Execution hm V (fromPalette (ofSteps V 0) out.2.val) out.1 pairs
      (fromPalette (ofSteps (collarPath pairs V) 0)
        (KroneckerWitnessDeleteZeroProgram.zeroProgram rule hm p pairs hp hs g).val) := by
  exact ⟨KroneckerRecolDeleteComposition.run_execution rule hm p 0 g,
    collar_execution hm pairs hp _ V _⟩

end KroneckerRecolCollars
