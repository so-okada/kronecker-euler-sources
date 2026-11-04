import KroneckerRawMixedPrograms

/-! The recovery and comparison bounds hold for every certified deletion selector. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerDeletionWitness
open KroneckerColoring KroneckerWordCounts KroneckerDeletionColoring

abbrev Witness {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (g : ConnectedColorings m U c) :=
  {j : Fin i // U[j.val] = true ∧ 0 < grade (g.val ⟨j.val, lt_trans j.isLt hi⟩) ∧
    KroneckerStack.Connected m
      (pathWord (deletionPath u v U i) (deletionColoring u v hu hv hm hpos U i hi j g.val))
      (c + grade (g.val ⟨i,hi⟩))}

abbrev Rule (m : ℕ) :=
  ∀ (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (U : List Bool) (i : ℕ) (hi : i < U.length) (_ : U[i] = false)
    (g : ConnectedColorings m U c), Witness u v c hu hv hm hpos U i hi g

def standard (m : ℕ) : Rule m := fun u v c hu hv hm hpos U i hi hvrt g =>
  ⟨KroneckerDeletionChoice.chosenIndex u v c hu hv hm hpos U i hi hvrt g,
    KroneckerDeletionChoice.chosenIndex_spec u v c hu hv hm hpos U i hi hvrt g⟩

def index {m : ℕ} (rule : Rule m) (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvrt : U[i] = false) (g : ConnectedColorings m U c) : Fin i :=
  (rule u v c hu hv hm hpos U i hi hvrt g).val

theorem index_spec {m : ℕ} (rule : Rule m) (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvrt : U[i] = false) (g : ConnectedColorings m U c) :
    let j := index rule u v c hu hv hm hpos U i hi hvrt g
    U[j.val] = true ∧ 0 < grade (g.val ⟨j.val, lt_trans j.isLt hi⟩) ∧
    KroneckerStack.Connected m
      (pathWord (deletionPath u v U i) (deletionColoring u v hu hv hm hpos U i hi j g.val))
      (c + grade (g.val ⟨i,hi⟩)) :=
  (rule u v c hu hv hm hpos U i hi hvrt g).property

def deleteBy {m : ℕ} (rule : Rule m) (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvrt : U[i] = false) (g : ConnectedColorings m U c) :
    KroneckerVerticalDeletionMap.DeletionTarget m (deletionPath u v U i) c :=
  ⟨⟨grade (g.val ⟨i,hi⟩), by have := grade_le (g.val ⟨i,hi⟩); omega⟩,
    ⟨deletionColoring u v hu hv hm hpos U i hi
      (index rule u v c hu hv hm hpos U i hi hvrt g) g.val,
      (index_spec rule u v c hu hv hm hpos U i hi hvrt g).2.2⟩⟩

@[simp] theorem deleteBy_standard {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvrt : U[i] = false) (g : ConnectedColorings m U c) :
    deleteBy (standard m) u v c hu hv hm hpos U i hi hvrt g =
      KroneckerVerticalDeletionMap.verticalDeletion u v c hu hv hm hpos U i hi hvrt g := rfl

end KroneckerDeletionWitness

namespace KroneckerWitnessMixedExecution
open KroneckerWordCounts KroneckerProgramExecution KroneckerMixedPrograms
open KroneckerCompleteRunMap KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap

noncomputable def runMixed {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) : SurplusColorings m V :=
  match p with
  | .nil => ⟨c,g⟩
  | .complete p r i hr hi =>
    let old := runMixed rule hm p c g
    ⟨old.1+1,completeRun r i old.1 (by omega) _ hi old.2⟩
  | .insert p u v i hu hv hi =>
    let old := runMixed rule hm p c g
    ⟨old.1,verticalInsertion u v i old.1 hm hu hv _ hi old.2⟩
  | .delete p u v i hu hv hi hvrt =>
    let old := runMixed rule hm p c g
    let d := KroneckerDeletionWitness.deleteBy (rule (KroneckerMixedPrograms.steps p)) u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvrt old.2
    ⟨old.1+d.1.val,d.2⟩

theorem runMixed_complete_surplus {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (r i : ℕ) (hr : 1 ≤ r ∧ r ≤ m-2)
    (hi : 1 ≤ i ∧ i < V.length) (c : ℕ) (g : ConnectedColorings m U c) :
    (runMixed rule hm (.complete p r i hr hi) c g).1=(runMixed rule hm p c g).1+1 := rfl

end KroneckerWitnessMixedExecution


namespace KroneckerWitnessMixedSurplus
open KroneckerWordCounts KroneckerMixedPrograms KroneckerWitnessMixedExecution KroneckerVerticalDeletionMap

theorem runMixed_surplus {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) :
    c+K ≤ (runMixed rule hm p c g).1 ∧ (runMixed rule hm p c g).1 ≤ c+K+m*D := by
  induction p with
  | nil => simp [runMixed]
  | complete p r i hr hi ih =>
    change c+(_+1) ≤ (runMixed rule hm p c g).1+1 ∧ (runMixed rule hm p c g).1+1 ≤ c+(_+1)+_
    omega
  | insert p u v i hu hv hi ih => exact ih
  | @delete V K A D p u v i hu hv hi hvrt ih =>
    have hh := (KroneckerDeletionWitness.deleteBy (rule (KroneckerMixedPrograms.steps p)) u v (runMixed rule hm p c g).1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvrt (runMixed rule hm p c g).2).1.isLt
    change c+K ≤ (runMixed rule hm p c g).1+_ ∧ (runMixed rule hm p c g).1+_ ≤ c+K+m*(D+1)
    simp only [Nat.mul_add,Nat.mul_one]
    omega

end KroneckerWitnessMixedSurplus


namespace KroneckerWitnessMixedChangeLog
open KroneckerWordCounts KroneckerMixedPrograms KroneckerWitnessMixedExecution KroneckerMixedLayouts
open KroneckerTaggedLayout KroneckerTaggedDeletion KroneckerDeletionChoice

noncomputable def mixedLog {m n q : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) : List (Fin n) :=
  match p with
  | .nil => []
  | .complete p _ _ _ _ => mixedLog rule hm p L c g
  | .insert p _ _ _ _ _ _ => mixedLog rule hm p L c g
  | .delete p u v i hu hv hi hvrt =>
    let old := runMixed rule hm p c g
    let j := KroneckerDeletionWitness.index (rule (KroneckerMixedPrograms.steps p)) u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvrt old.2
    changedAt (mixedLayout p L) ⟨j.val,lt_trans j.isLt hi⟩ (mixedLog rule hm p L c g)

theorem mixedLog_bound {m n q : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) :
    (mixedLog rule hm p L c g).length ≤ D := by
  induction p with
  | nil => simp [mixedLog]
  | complete p r i hr hi ih => exact ih
  | insert p u v i hu hv hi ih => exact ih
  | delete p u v i hu hv hi hvrt ih =>
    exact (changedAt_bound _ _ _).trans (Nat.add_le_add_right ih 1)

end KroneckerWitnessMixedChangeLog


namespace KroneckerWitnessMixedRetention
open KroneckerColoring KroneckerInputRecovery KroneckerWordCounts KroneckerWordRecoveryFiber
open KroneckerMixedPrograms KroneckerWitnessMixedExecution KroneckerMixedLayouts KroneckerWitnessMixedChangeLog
open KroneckerTaggedLayout KroneckerTaggedInsertion KroneckerTaggedDeletion KroneckerCompleteRunRetention
open KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap KroneckerDeletionChoice KroneckerCompleteRunMap

set_option backward.isDefEq.respectTransparency false in
theorem mixed_retains {m n q : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (source : Input m n q) (L : Layout n q U) (c : ℕ)
    (g : ConnectedColorings m U c) (hinit : Retains source [] L g.val) :
    Retains source (mixedLog rule hm p L c g) (mixedLayout p L) (runMixed rule hm p c g).2.val := by
  induction p with
  | nil => exact hinit
  | complete p r i hr hi ih =>
    simpa only [mixedLog,mixedLayout,runMixed,completeRun] using
      completeColoring_retains source (mixedLog rule hm p L c g) (mixedLayout p L)
        (runMixed rule hm p c g).2.val ih r i (by omega)
  | insert p u v i hu hv hi ih =>
    simpa only [mixedLog,mixedLayout,runMixed,verticalInsertion] using
      insertion_retains source (mixedLog rule hm p L c g) (mixedLayout p L)
        (runMixed rule hm p c g).2.val ih u v i (by omega) (by omega) (by omega) hv.1
  | @delete V K A D p u v i hu hv hi hvrt ih =>
    let old := runMixed rule hm p c g
    let j := KroneckerDeletionWitness.index (rule (KroneckerMixedPrograms.steps p)) u v old.1 (by omega) (by omega) (by omega) hv.1 V i hi hvrt old.2
    have hj : V[j.val]=true := (KroneckerDeletionWitness.index_spec (rule (KroneckerMixedPrograms.steps p)) u v old.1 (by omega) (by omega) (by omega)
      hv.1 V i hi hvrt old.2).1
    simpa only [mixedLog,mixedLayout,runMixed,KroneckerDeletionWitness.deleteBy] using
      deletion_retains source (mixedLog rule hm p L c g) (mixedLayout p L) old.2.val ih
        u v i (by omega) (by omega) (by omega) hv.1 hi hvrt j hj

theorem original_mixed_retains {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) :
    Retains (connectedSource m U c g) (mixedLog rule hm p (initialLayout U) c g)
      (mixedLayout p (initialLayout U)) (runMixed rule hm p c g).2.val :=
  mixed_retains rule hm p _ (initialLayout U) c g (initialLayout_retains U g.val)

theorem original_mixed_deleted_bound {m : ℕ} {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) : (mixedLayout p (initialLayout U)).deleted.length ≤ D := by
  have h := mixedLayout_deleted_bound p (initialLayout U)
  simpa only [initialLayout,List.length_nil,Nat.zero_add] using h

end KroneckerWitnessMixedRetention


namespace KroneckerWitnessMixedRecovery
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerInputRecovery
open KroneckerMixedPrograms KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerRecoverySpecification
open KroneckerWitnessMixedExecution KroneckerMixedLayouts KroneckerWitnessMixedChangeLog KroneckerWitnessMixedRetention

noncomputable def mixedSpec {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) :
    RecoverySpec m (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) D
      (connectedSource m U c) (runMixed rule hm p c) :=
  taggedSpec (connectedSource m U c) (runMixed rule hm p c)
    (fun b : SurplusColorings m V => b.2.val) (mixedLayout p (initialLayout U))
    (mixedLog rule hm p (initialLayout U) c) (mixedLog_bound rule hm p (initialLayout U) c)
    (original_mixed_deleted_bound p) (original_mixed_retains rule hm p c)

theorem mixed_recover {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) :
    decodeInput (mixedSpec rule hm p c).deleted (mixedSpec rule hm p c).deleted_card
      ((mixedSpec rule hm p c).retained (runMixed rule hm p c g))
      (code (mixedSpec rule hm p c) g)=connectedSource m U c g :=
  recover_source (mixedSpec rule hm p c) g

end KroneckerWitnessMixedRecovery


namespace KroneckerWitnessMixedFiber
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerFiberBudget
open KroneckerMixedPrograms KroneckerWitnessMixedExecution KroneckerWitnessMixedRecovery
open KroneckerRecoverySpecification KroneckerReconstructionFiber

theorem mixed_code_injective {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) :
    Function.Injective (fun g : ConnectedColorings m U c =>
      (runMixed rule hm p c g,code (mixedSpec rule hm p c) g)) :=
  target_code_injective (mixedSpec rule hm p c) (connectedSource_injective m U c)

theorem mixed_fiber_bound {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (b : SurplusColorings m V) :
    Nat.card {g // runMixed rule hm p c g=b} ≤ fiberBudget m (U.count true) D := by
  classical
  simpa only [positions_card] using
    reconstruction_fiber_bound (mixedSpec rule hm p c) (connectedSource_injective m U c) b

end KroneckerWitnessMixedFiber


namespace KroneckerWitnessZeroMixed
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerMixedPrograms KroneckerWitnessMixedExecution KroneckerWitnessMixedSurplus
open KroneckerCollarColoring KroneckerCollarConnected KroneckerCollarRecovery

noncomputable def zeroMixed {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) : ConnectedColorings m (collarPath pairs V) 0 := by
  let r := runMixed rule hm p 0 g
  have hr := (runMixed_surplus rule hm p 0 g).2
  have hz : r.1-pairs.length=0 := by dsimp [r]; omega
  refine ⟨collarColoring (by omega) pairs hp r.1 V r.2.val,?_⟩
  simpa only [hz] using collarColoring_connected (by omega) pairs hp r.1 V r.2.val r.2.property

theorem zeroMixed_recover {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    recoverCollar pairs V (zeroMixed rule hm p pairs hp hsize g).val=(runMixed rule hm p 0 g).2.val :=
  recover_collarColoring (by omega) pairs hp _ V _

end KroneckerWitnessZeroMixed


namespace KroneckerWitnessZeroMixedRecovery
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerInputRecovery
open KroneckerMixedPrograms KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerRecoverySpecification
open KroneckerWitnessMixedExecution KroneckerMixedLayouts KroneckerWitnessMixedChangeLog KroneckerWitnessMixedRetention
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerWitnessZeroMixed

noncomputable def zeroMixedSpec {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (zeroMixed rule hm p pairs hp hsize) :=
  taggedSpec (connectedSource m U 0) (zeroMixed rule hm p pairs hp hsize) Subtype.val
    (collarLayout pairs (mixedLayout p (initialLayout U)))
    (mixedLog rule hm p (initialLayout U) 0) (mixedLog_bound rule hm p (initialLayout U) 0)
    (by rw [collarLayout_deleted]; exact original_mixed_deleted_bound p)
    (fun g => collar_retains (by omega) (connectedSource m U 0 g) _ _ _
      (original_mixed_retains rule hm p 0 g) pairs hp (runMixed rule hm p 0 g).1)

theorem zeroMixed_decode {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (zeroMixedSpec rule hm p pairs hp hsize).deleted (zeroMixedSpec rule hm p pairs hp hsize).deleted_card
      ((zeroMixedSpec rule hm p pairs hp hsize).retained (zeroMixed rule hm p pairs hp hsize g))
      (code (zeroMixedSpec rule hm p pairs hp hsize) g)=connectedSource m U 0 g :=
  recover_source (zeroMixedSpec rule hm p pairs hp hsize) g

end KroneckerWitnessZeroMixedRecovery


namespace KroneckerWitnessZeroMixedCount
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerMixedPrograms KroneckerCollarColoring KroneckerWitnessZeroMixed
open KroneckerWitnessZeroMixedRecovery KroneckerWordRecoveryCount KroneckerWordRecoveryFiber KroneckerFiberBudget

theorem zero_mixed_count {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 :=
  word_recovery_count_bound (zeroMixedSpec rule hm p pairs hp hsize)

theorem zero_mixed_real {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤ (pathCount m (collarPath pairs V) 0 : ℝ) :=
  word_recovery_real_bound (zeroMixedSpec rule hm p pairs hp hsize)

theorem zero_mixed_fiber {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length)
    (b : ConnectedColorings m (collarPath pairs V) 0) :
    Nat.card {g // zeroMixed rule hm p pairs hp hsize g=b} ≤ fiberBudget m (U.count true) D :=
  word_recovery_fiber_bound (zeroMixedSpec rule hm p pairs hp hsize) b

end KroneckerWitnessZeroMixedCount

