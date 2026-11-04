import KroneckerRecolDeletion
import KroneckerRecolShell
import KroneckerWitnessDeletePrograms

/-! Exact colored correspondence for each step of an ordered program.
All paths here have origin zero; geometric translation is handled by the
existing word-reindexing equivalence. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerRecolComposition
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerColoring KroneckerWordCounts KroneckerMixedPrograms
open KroneckerCompleteRunPalette KroneckerInsertionPalette KroneckerDeletionColoring
open KroneckerRecolPaletteBridge KroneckerRecolOperations KroneckerRecolDeletion

/-- Complete-run recoloring on the normalized target path. -/
def completeZero {m : ℕ} (V : List Bool) (r i : ℕ) (hi : i ≤ V.length)
    (hr : 0 < r) (hm : r ≤ m) (c : Coloring m V.length) :
    ColoredGrading m (ofSteps (completePath r i V) 0) :=
  let d := fromPalette (ofSteps (completePath r i V) 0) (completeColoring r i hm V c)
  let b := fromPalette (ofSteps V 0) c
  let f : Edge (ofSteps V 0) ↪ Edge (ofSteps (completePath r i V) 0) :=
    completeIndices (ofSteps V 0) i r hi hr
  ⟨d.1, Recol _ _ (edgeCopy f) d.1 (color_grade_le d.2) b.1 b.2⟩

theorem completeZero_eq {m : ℕ} (V : List Bool) (r i : ℕ) (hi : i ≤ V.length)
    (hr : 0 < r) (hm : r ≤ m) (c : Coloring m V.length) :
    completeZero V r i hi hr hm c =
      fromPalette (ofSteps (completePath r i V) 0) (completeColoring r i hm V c) := by
  apply fromPalette_recol_total
  · intro k
    have h := complete_copy (ofSteps V 0) i r hi hr hm c k
    exact (congrArg (RespectsRecol (c k)) h).mpr (respects_self _)
  · exact complete_new (ofSteps V 0) i r hi hr hm c

/-- A derivation records literal Recol operations, in the program's order. -/
inductive Execution {m : ℕ} (hm : 4 ≤ m) (U : List Bool)
    (source : ColoredGrading m (ofSteps U 0)) :
    {V : List Bool} → {K A D : ℕ} → MixedProgram m U V K A D →
      ColoredGrading m (ofSteps V 0) → Prop
  | nil : Execution hm U source .nil source
  | complete {V K A D} (p : MixedProgram m U V K A D) (r i : ℕ)
      (hr : 1 ≤ r ∧ r ≤ m-2) (hi : 1 ≤ i ∧ i < V.length)
      (c : Coloring m V.length) (h : Execution hm U source p (fromPalette (ofSteps V 0) c)) :
      Execution hm U source (.complete p r i hr hi)
        (completeZero V r i (by omega) (by omega) (by omega) c)
  | insert {V K A D} (p : MixedProgram m U V K A D) (u v i : ℕ)
      (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) (hi : 1 ≤ i ∧ i ≤ V.length)
      (c : Coloring m V.length) (h : Execution hm U source p (fromPalette (ofSteps V 0) c)) :
      Execution hm U source (.insert p u v i hu hv hi)
        (KroneckerRecolorConstructions.insertion (ofSteps V 0) u v i
          (by omega) (by omega) (by omega) hv.1 c)
  | delete {V K A D} (p : MixedProgram m U V K A D) (u v i : ℕ)
      (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) (hi : i < V.length)
      (hvrt : V[i] = false) (c : Coloring m V.length) (j : Fin i)
      (hj : V[j.val] = true) (hp : 0 < grade (c ⟨j.val, lt_trans j.isLt hi⟩))
      (h : Execution hm U source p (fromPalette (ofSteps V 0) c)) :
      Execution hm U source (.delete p u v i hu hv hi hvrt)
        (KroneckerRecolorConstructions.deletion (ofSteps V 0) u v
          (by omega) (by omega) (by omega) hv.1 ⟨i,hi⟩ j c)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem run_execution {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m)
    {U V : List Bool} {K A D : ℕ} (p : MixedProgram m U V K A D)
    (c : ℕ) (g : ConnectedColorings m U c) :
    Execution hm U (fromPalette (ofSteps U 0) g.val) p
      (fromPalette (ofSteps V 0) (KroneckerWitnessMixedExecution.runMixed rule hm p c g).2.val) := by
  induction p with
  | nil => exact Execution.nil
  | @complete V K A D p r i hr hi ih =>
    have h := Execution.complete p r i hr hi _ ih
    rw [completeZero_eq] at h
    exact h
  | @insert V K A D p u v i hu hv hi ih =>
    have h := Execution.insert p u v i hu hv hi _ ih
    rw [insertion_eq (ofSteps V 0) u v i _ _ _ _ hi.2] at h
    exact h
  | @delete V K A D p u v i hu hv hi hvrt ih =>
    let old := KroneckerWitnessMixedExecution.runMixed rule hm p c g
    let j := KroneckerDeletionWitness.index (rule (KroneckerMixedPrograms.steps p)) u v old.1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvrt old.2
    have hj := KroneckerDeletionWitness.index_spec (rule (KroneckerMixedPrograms.steps p)) u v old.1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvrt old.2
    have h := Execution.delete p u v i hu hv hi hvrt old.2.val j hj.1 hj.2.1 ih
    rw [deletion_eq (ofSteps V 0) u v _ _ _ _ ⟨i,hi⟩ j old.2.val hj.2.1] at h
    exact h

/-- The standard selector specializes to the counted implementation. -/
theorem run_standard {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) :
    KroneckerWitnessMixedExecution.runMixed (fun _ => KroneckerDeletionWitness.standard m) hm p c g =
      KroneckerMixedExecution.runMixed hm p c g := by
  induction p with
  | nil => rfl
  | @complete V K A D p r i hr hi ih =>
    exact congrArg (fun old : KroneckerProgramExecution.SurplusColorings m V =>
      (⟨old.1+1, KroneckerCompleteRunMap.completeRun r i old.1 (by omega) V hi old.2⟩ :
        KroneckerProgramExecution.SurplusColorings m (completePath r i V))) ih
  | @insert V K A D p u v i hu hv hi ih =>
    exact congrArg (fun old : KroneckerProgramExecution.SurplusColorings m V =>
      (⟨old.1, KroneckerVerticalInsertionMap.verticalInsertion u v i old.1 hm hu hv V hi old.2⟩ :
        KroneckerProgramExecution.SurplusColorings m (insertedPath u v i V))) ih
  | @delete V K A D p u v i hu hv hi hvrt ih =>
    exact congrArg (fun old : KroneckerProgramExecution.SurplusColorings m V =>
      let d := KroneckerVerticalDeletionMap.verticalDeletion u v old.1 (by omega) (by omega)
        (by omega) hv.1 V i hi hvrt old.2
      (⟨old.1+d.1.val,d.2⟩ : KroneckerProgramExecution.SurplusColorings m (deletionPath u v V i))) ih

theorem actual_execution {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) :
    Execution hm U (fromPalette (ofSteps U 0) g.val) p
      (fromPalette (ofSteps V 0) (KroneckerMixedExecution.runMixed hm p c g).2.val) := by
  exact (congrArg (fun out : KroneckerProgramExecution.SurplusColorings m V =>
    Execution hm U (fromPalette (ofSteps U 0) g.val) p
      (fromPalette (ofSteps V 0) out.2.val)) (run_standard hm p c g)).mp
        (run_execution (fun _ => KroneckerDeletionWitness.standard m) hm p c g)

end KroneckerRecolComposition
