import KroneckerWitnessPrograms
import KroneckerDeletePrescribedCount

set_option autoImplicit false
noncomputable section
namespace KroneckerWitnessDeleteProgramExecution
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap

abbrev SurplusColorings (m : ℕ) (U : List Bool) := (c : ℕ) × ConnectedColorings m U c

noncomputable def runProgram {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (c : ℕ) (g : ConnectedColorings m U c) : SurplusColorings m V :=
  match p with
  | .nil => ⟨c,g⟩
  | .delete p u v i hu hv hi hvert =>
    let old := runProgram rule hm p c g
    let d := KroneckerDeletionWitness.deleteBy (rule (KroneckerDeleteVerticalPrograms.steps p)) u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvert old.2
    ⟨old.1+d.1.val,d.2⟩

theorem runProgram_nil {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) (U : List Bool) (c : ℕ) (g : ConnectedColorings m U c) :
    runProgram rule hm (.nil : Program m U U 0) c g=⟨c,g⟩ := rfl


end KroneckerWitnessDeleteProgramExecution


namespace KroneckerWitnessDeleteProgramSurplus
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerWitnessDeleteProgramExecution KroneckerVerticalDeletionMap

theorem runProgram_surplus {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (c : ℕ) (g : ConnectedColorings m U c) :
    c ≤ (runProgram rule hm p c g).1 ∧ (runProgram rule hm p c g).1 ≤ c+m*D := by
  induction p with
  | nil => simp [runProgram]
  | @delete V D p u v i hu hv hi hvert ih =>
    have hh := (KroneckerDeletionWitness.deleteBy (rule (KroneckerDeleteVerticalPrograms.steps p)) u v (runProgram rule hm p c g).1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvert (runProgram rule hm p c g).2).1.isLt
    change c ≤ (runProgram rule hm p c g).1+_ ∧ (runProgram rule hm p c g).1+_ ≤ c+m*(D+1)
    simp only [Nat.mul_add,Nat.mul_one]
    omega

end KroneckerWitnessDeleteProgramSurplus


namespace KroneckerWitnessDeleteProgramChangeLog
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerWitnessDeleteProgramExecution KroneckerDeleteProgramLayouts
open KroneckerTaggedLayout KroneckerTaggedDeletion KroneckerDeletionChoice

noncomputable def programLog {m n q : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) : List (Fin n) :=
  match p with
  | .nil => []
  | .delete p u v i hu hv hi hvert =>
    let old := runProgram rule hm p c g
    let j := KroneckerDeletionWitness.index (rule (KroneckerDeleteVerticalPrograms.steps p)) u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvert old.2
    changedAt (programLayout p L) ⟨j.val,lt_trans j.isLt hi⟩ (programLog rule hm p L c g)

theorem programLog_bound {m n q : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) :
    (programLog rule hm p L c g).length ≤ D := by
  induction p with
  | nil => simp [programLog]
  | delete p u v i hu hv hi hvert ih =>
    apply (changedAt_bound _ _ _).trans
    exact Nat.add_le_add_right ih 1

end KroneckerWitnessDeleteProgramChangeLog


namespace KroneckerWitnessDeleteProgramRetention
open KroneckerColoring KroneckerInputRecovery KroneckerWordCounts KroneckerDeleteVerticalPrograms
open KroneckerWitnessDeleteProgramExecution KroneckerDeleteProgramLayouts KroneckerWitnessDeleteProgramChangeLog
open KroneckerTaggedLayout KroneckerTaggedInsertion KroneckerTaggedDeletion
open KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap KroneckerDeletionChoice

set_option backward.isDefEq.respectTransparency false in
theorem program_retains {m n q : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (source : Input m n q) (L : Layout n q U) (c : ℕ)
    (g : ConnectedColorings m U c) (hinit : Retains source [] L g.val) :
    Retains source (programLog rule hm p L c g) (programLayout p L) (runProgram rule hm p c g).2.val := by
  induction p with
  | nil => exact hinit
  | @delete V D p u v i hu hv hi hvert ih =>
    let old := runProgram rule hm p c g
    let j := KroneckerDeletionWitness.index (rule (KroneckerDeleteVerticalPrograms.steps p)) u v old.1 (by omega) (by omega) (by omega) hv.1 V i hi hvert old.2
    have hj : V[j.val]=true := (KroneckerDeletionWitness.index_spec (rule (KroneckerDeleteVerticalPrograms.steps p)) u v old.1 (by omega) (by omega) (by omega)
      hv.1 V i hi hvert old.2).1
    simpa only [programLog,programLayout,runProgram,KroneckerDeletionWitness.deleteBy] using
      deletion_retains source (programLog rule hm p L c g) (programLayout p L) old.2.val ih
        u v i (by omega) (by omega) (by omega) hv.1 hi hvert j hj

end KroneckerWitnessDeleteProgramRetention


namespace KroneckerWitnessDeleteOriginalProgramRetention
open KroneckerWordCounts KroneckerWordPaletteSplit KroneckerDeleteVerticalPrograms KroneckerTaggedLayout
open KroneckerWitnessDeleteProgramExecution KroneckerDeleteProgramLayouts KroneckerWitnessDeleteProgramChangeLog KroneckerWitnessDeleteProgramRetention

theorem original_program_retains {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (c : ℕ) (g : ConnectedColorings m U c) :
    Retains (splitColoring U g.val) (programLog rule hm p (initialLayout U) c g)
      (programLayout p (initialLayout U)) (runProgram rule hm p c g).2.val :=
  program_retains rule hm p (splitColoring U g.val) (initialLayout U) c g (initialLayout_retains U g.val)

theorem original_program_deleted_bound {m : ℕ} {U V : List Bool} {D : ℕ}
    (p : Program m U V D) : (programLayout p (initialLayout U)).deleted.length ≤ D := by
  simpa only [initialLayout,List.length_nil,Nat.zero_add] using programLayout_deleted_bound p (initialLayout U)

end KroneckerWitnessDeleteOriginalProgramRetention


namespace KroneckerWitnessDeleteZeroProgram
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerWitnessDeleteProgramExecution KroneckerWitnessDeleteProgramSurplus
open KroneckerCollarColoring KroneckerCollarConnected KroneckerCollarRecovery

noncomputable def zeroProgram {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) : ConnectedColorings m (collarPath pairs V) 0 := by
  let r := runProgram rule hm p 0 g
  have hr := (runProgram_surplus rule hm p 0 g).2
  have hz : r.1-pairs.length=0 := by dsimp [r]; omega
  refine ⟨collarColoring (by omega) pairs hp r.1 V r.2.val,?_⟩
  simpa only [hz] using collarColoring_connected (by omega) pairs hp r.1 V r.2.val r.2.property

theorem zeroProgram_recover {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    recoverCollar pairs V (zeroProgram rule hm p pairs hp hsize g).val=(runProgram rule hm p 0 g).2.val :=
  recover_collarColoring (by omega) pairs hp _ V _

end KroneckerWitnessDeleteZeroProgram


namespace KroneckerWitnessDeleteZeroProgramRecovery
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerInputRecovery
open KroneckerDeleteVerticalPrograms KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerRecoverySpecification
open KroneckerWitnessDeleteProgramExecution KroneckerDeleteProgramLayouts KroneckerWitnessDeleteProgramChangeLog KroneckerWitnessDeleteOriginalProgramRetention
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerWitnessDeleteZeroProgram

noncomputable def zeroProgramSpec {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (zeroProgram rule hm p pairs hp hsize) :=
  taggedSpec (connectedSource m U 0) (zeroProgram rule hm p pairs hp hsize) Subtype.val
    (collarLayout pairs (programLayout p (initialLayout U)))
    (programLog rule hm p (initialLayout U) 0) (programLog_bound rule hm p (initialLayout U) 0)
    (by rw [collarLayout_deleted]; exact original_program_deleted_bound p)
    (fun g => collar_retains (by omega) (connectedSource m U 0 g) _ _ _
      (original_program_retains rule hm p 0 g) pairs hp (runProgram rule hm p 0 g).1)

theorem zeroProgram_decode {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (zeroProgramSpec rule hm p pairs hp hsize).deleted (zeroProgramSpec rule hm p pairs hp hsize).deleted_card
      ((zeroProgramSpec rule hm p pairs hp hsize).retained (zeroProgram rule hm p pairs hp hsize g))
      (code (zeroProgramSpec rule hm p pairs hp hsize) g)=connectedSource m U 0 g :=
  recover_source (zeroProgramSpec rule hm p pairs hp hsize) g

end KroneckerWitnessDeleteZeroProgramRecovery


namespace KroneckerWitnessDeleteZeroProgramCount
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerCollarColoring KroneckerWitnessDeleteZeroProgram
open KroneckerWitnessDeleteZeroProgramRecovery KroneckerWordRecoveryCount KroneckerWordRecoveryFiber KroneckerFiberBudget

theorem zero_program_count {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 :=
  word_recovery_count_bound (zeroProgramSpec rule hm p pairs hp hsize)

theorem zero_program_real {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤ (pathCount m (collarPath pairs V) 0 : ℝ) :=
  word_recovery_real_bound (zeroProgramSpec rule hm p pairs hp hsize)

theorem zero_program_fiber {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (b : ConnectedColorings m (collarPath pairs V) 0) :
    Nat.card {g // zeroProgram rule hm p pairs hp hsize g=b} ≤ fiberBudget m (U.count true) D :=
  word_recovery_fiber_bound (zeroProgramSpec rule hm p pairs hp hsize) b

end KroneckerWitnessDeleteZeroProgramCount

