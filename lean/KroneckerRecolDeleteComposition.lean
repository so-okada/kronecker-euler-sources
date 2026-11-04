import KroneckerRecolComposition

set_option autoImplicit false
noncomputable section
namespace KroneckerRecolDeleteComposition
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerColoring KroneckerWordCounts KroneckerDeleteVerticalPrograms
open KroneckerDeletionColoring KroneckerRecolDeletion

inductive Execution {m : ℕ} (hm : 3 ≤ m) (U : List Bool)
    (source : ColoredGrading m (ofSteps U 0)) :
    {V : List Bool} → {D : ℕ} → Program m U V D → ColoredGrading m (ofSteps V 0) → Prop
  | nil : Execution hm U source .nil source
  | delete {V D} (p : Program m U V D) (u v i : ℕ)
      (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (hi : i < V.length)
      (hvrt : V[i] = false) (c : Coloring m V.length) (j : Fin i)
      (hj : V[j.val] = true) (hp : 0 < grade (c ⟨j.val, lt_trans j.isLt hi⟩))
      (h : Execution hm U source p (fromPalette (ofSteps V 0) c)) :
      Execution hm U source (.delete p u v i hu hv hi hvrt)
        (KroneckerRecolorConstructions.deletion (ofSteps V 0) u v
          (by omega) (by omega) (by omega) hv.1 ⟨i,hi⟩ j c)

theorem run_execution {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m)
    {U V : List Bool} {D : ℕ} (p : Program m U V D)
    (c : ℕ) (g : ConnectedColorings m U c) :
    Execution hm U (fromPalette (ofSteps U 0) g.val) p
      (fromPalette (ofSteps V 0) (KroneckerWitnessDeleteProgramExecution.runProgram rule hm p c g).2.val) := by
  induction p with
  | nil => exact Execution.nil
  | @delete V D p u v i hu hv hi hvrt ih =>
    let old := KroneckerWitnessDeleteProgramExecution.runProgram rule hm p c g
    let j := KroneckerDeletionWitness.index (rule (steps p)) u v old.1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvrt old.2
    have hj := KroneckerDeletionWitness.index_spec (rule (steps p)) u v old.1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvrt old.2
    have h := Execution.delete p u v i hu hv hi hvrt old.2.val j hj.1 hj.2.1 ih
    rw [deletion_eq (ofSteps V 0) u v _ _ _ _ ⟨i,hi⟩ j old.2.val hj.2.1] at h
    exact h

theorem run_standard {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (c : ℕ) (g : ConnectedColorings m U c) :
    KroneckerWitnessDeleteProgramExecution.runProgram (fun _ => KroneckerDeletionWitness.standard m) hm p c g =
      KroneckerDeleteProgramExecution.runProgram hm p c g := by
  induction p with
  | nil => rfl
  | @delete V D p u v i hu hv hi hvrt ih =>
    exact congrArg (fun old : KroneckerProgramExecution.SurplusColorings m V =>
      let d := KroneckerVerticalDeletionMap.verticalDeletion u v old.1 (by omega) (by omega)
        (by omega) hv.1 V i hi hvrt old.2
      (⟨old.1+d.1.val,d.2⟩ : KroneckerProgramExecution.SurplusColorings m (deletionPath u v V i))) ih

theorem actual_execution {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (c : ℕ) (g : ConnectedColorings m U c) :
    Execution hm U (fromPalette (ofSteps U 0) g.val) p
      (fromPalette (ofSteps V 0) (KroneckerDeleteProgramExecution.runProgram hm p c g).2.val) := by
  exact (congrArg (fun out : KroneckerProgramExecution.SurplusColorings m V =>
    Execution hm U (fromPalette (ofSteps U 0) g.val) p
      (fromPalette (ofSteps V 0) out.2.val)) (run_standard hm p c g)).mp
        (run_execution (fun _ => KroneckerDeletionWitness.standard m) hm p c g)

end KroneckerRecolDeleteComposition
