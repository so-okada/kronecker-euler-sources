import KroneckerMixedLayerBudget

/- Original module: KroneckerDeleteVerticalPrograms -/
section
/-! Deletion-only programs work for three arrows; no insertion gate is present. -/
set_option autoImplicit false
namespace KroneckerDeleteVerticalPrograms
open KroneckerDeletionColoring

inductive Program (m : ℕ) (U : List Bool) : List Bool → ℕ → Type
  | nil : Program m U U 0
  | delete {V : List Bool} {D : ℕ} (p : Program m U V D) (u v i : ℕ)
      (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
      (hi : i < V.length) (hvertical : V[i]=false) :
      Program m U (deletionPath u v V i) (D+1)

def steps {m : ℕ} {U V : List Bool} {D : ℕ} : Program m U V D → ℕ
  | .nil => 0
  | .delete p _ _ _ _ _ _ _ => steps p+1

theorem steps_eq {m : ℕ} {U V : List Bool} {D : ℕ} (p : Program m U V D) : steps p=D := by
  induction p with
  | nil => rfl
  | delete p u v i hu hv hi hvert ih => simp only [steps,ih]

end KroneckerDeleteVerticalPrograms
end

/- Original module: KroneckerDeleteProgramLayouts -/
section
/-! The layout and deleted-original record of a deletion-only program are independent of colors. -/
set_option autoImplicit false
namespace KroneckerDeleteProgramLayouts
open KroneckerTaggedLayout KroneckerWrappedTags KroneckerEditedLayouts KroneckerDeleteVerticalPrograms

def programLayout {m n q : ℕ} {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (L : Layout n q U) : Layout n q V :=
  match p with
  | .nil => L
  | .delete p u v i _ _ hi hvert => wrapLayout u v (removeLayout i hi hvert (programLayout p L))

theorem programLayout_deleted_bound {m n q : ℕ} {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (L : Layout n q U) :
    (programLayout p L).deleted.length ≤ L.deleted.length+D := by
  induction p with
  | nil => simp [programLayout]
  | delete p u v i hu hv hi hvert ih =>
    have h := removeLayout_deleted_bound i hi hvert (programLayout p L)
    change (removeLayout i hi hvert (programLayout p L)).deleted.length ≤ _
    omega

end KroneckerDeleteProgramLayouts
end

/- Original module: KroneckerDeleteProgramExecution -/
section
/-! Execute the prescribed edits on actual connected colorings. -/
set_option autoImplicit false
namespace KroneckerDeleteProgramExecution
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap

abbrev SurplusColorings (m : ℕ) (U : List Bool) := (c : ℕ) × ConnectedColorings m U c

noncomputable def runProgram {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (c : ℕ) (g : ConnectedColorings m U c) : SurplusColorings m V :=
  match p with
  | .nil => ⟨c,g⟩
  | .delete p u v i hu hv hi hvert =>
    let old := runProgram hm p c g
    let d := verticalDeletion u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvert old.2
    ⟨old.1+d.1.val,d.2⟩

theorem runProgram_nil {m : ℕ} (hm : 3 ≤ m) (U : List Bool) (c : ℕ) (g : ConnectedColorings m U c) :
    runProgram hm (.nil : Program m U U 0) c g=⟨c,g⟩ := rfl


end KroneckerDeleteProgramExecution
end

/- Original module: KroneckerDeleteProgramSurplus -/
section
/-! A deletion-only program preserves the lower surplus bound and adds at most m per deletion. -/
set_option autoImplicit false
namespace KroneckerDeleteProgramSurplus
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerDeleteProgramExecution KroneckerVerticalDeletionMap

theorem runProgram_surplus {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (c : ℕ) (g : ConnectedColorings m U c) :
    c ≤ (runProgram hm p c g).1 ∧ (runProgram hm p c g).1 ≤ c+m*D := by
  induction p with
  | nil => simp [runProgram]
  | @delete V D p u v i hu hv hi hvert ih =>
    have hh := (verticalDeletion u v (runProgram hm p c g).1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvert (runProgram hm p c g).2).1.isLt
    change c ≤ (runProgram hm p c g).1+_ ∧ (runProgram hm p c g).1+_ ≤ c+m*(D+1)
    simp only [Nat.mul_add,Nat.mul_one]
    omega

end KroneckerDeleteProgramSurplus
end

/- Original module: KroneckerDeleteProgramChangeLog -/
section
/-! Log only original horizontal labels changed by actual deletions in the program. -/
set_option autoImplicit false
namespace KroneckerDeleteProgramChangeLog
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerDeleteProgramExecution KroneckerDeleteProgramLayouts
open KroneckerTaggedLayout KroneckerTaggedDeletion KroneckerDeletionChoice

noncomputable def programLog {m n q : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) : List (Fin n) :=
  match p with
  | .nil => []
  | .delete p u v i hu hv hi hvert =>
    let old := runProgram hm p c g
    let j := chosenIndex u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvert old.2
    changedAt (programLayout p L) ⟨j.val,lt_trans j.isLt hi⟩ (programLog hm p L c g)

theorem programLog_bound {m n q : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) :
    (programLog hm p L c g).length ≤ D := by
  induction p with
  | nil => simp [programLog]
  | delete p u v i hu hv hi hvert ih =>
    apply (changedAt_bound _ _ _).trans
    exact Nat.add_le_add_right ih 1

end KroneckerDeleteProgramChangeLog
end

/- Original module: KroneckerDeleteProgramRetention -/
section
/-! Compose the proved local palette-retention invariants along the actual program. -/
set_option autoImplicit false
namespace KroneckerDeleteProgramRetention
open KroneckerColoring KroneckerInputRecovery KroneckerWordCounts KroneckerDeleteVerticalPrograms
open KroneckerDeleteProgramExecution KroneckerDeleteProgramLayouts KroneckerDeleteProgramChangeLog
open KroneckerTaggedLayout KroneckerTaggedInsertion KroneckerTaggedDeletion
open KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap KroneckerDeletionChoice

set_option backward.isDefEq.respectTransparency false in
theorem program_retains {m n q : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (source : Input m n q) (L : Layout n q U) (c : ℕ)
    (g : ConnectedColorings m U c) (hinit : Retains source [] L g.val) :
    Retains source (programLog hm p L c g) (programLayout p L) (runProgram hm p c g).2.val := by
  induction p with
  | nil => exact hinit
  | @delete V D p u v i hu hv hi hvert ih =>
    let old := runProgram hm p c g
    let j := chosenIndex u v old.1 (by omega) (by omega) (by omega) hv.1 V i hi hvert old.2
    have hj : V[j.val]=true := (chosenIndex_spec u v old.1 (by omega) (by omega) (by omega)
      hv.1 V i hi hvert old.2).1
    simpa only [programLog,programLayout,runProgram,verticalDeletion] using
      deletion_retains source (programLog hm p L c g) (programLayout p L) old.2.val ih
        u v i (by omega) (by omega) (by omega) hv.1 hi hvert j hj

end KroneckerDeleteProgramRetention
end

/- Original module: KroneckerDeleteOriginalProgramRetention -/
section
/-! Initialize the actual composed program on the original horizontal and vertical color arrays. -/
set_option autoImplicit false
namespace KroneckerDeleteOriginalProgramRetention
open KroneckerWordCounts KroneckerWordPaletteSplit KroneckerDeleteVerticalPrograms KroneckerTaggedLayout
open KroneckerDeleteProgramExecution KroneckerDeleteProgramLayouts KroneckerDeleteProgramChangeLog KroneckerDeleteProgramRetention

theorem original_program_retains {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (c : ℕ) (g : ConnectedColorings m U c) :
    Retains (splitColoring U g.val) (programLog hm p (initialLayout U) c g)
      (programLayout p (initialLayout U)) (runProgram hm p c g).2.val :=
  program_retains hm p (splitColoring U g.val) (initialLayout U) c g (initialLayout_retains U g.val)

theorem original_program_deleted_bound {m : ℕ} {U V : List Bool} {D : ℕ}
    (p : Program m U V D) : (programLayout p (initialLayout U)).deleted.length ≤ D := by
  simpa only [initialLayout,List.length_nil,Nat.zero_add] using programLayout_deleted_bound p (initialLayout U)

end KroneckerDeleteOriginalProgramRetention
end

/- Original module: KroneckerDeleteZeroProgram -/
section
/-! Drain the surplus of an actual deletion-only program on a fixed prescribed target path. -/
set_option autoImplicit false
namespace KroneckerDeleteZeroProgram
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerDeleteProgramExecution KroneckerDeleteProgramSurplus
open KroneckerCollarColoring KroneckerCollarConnected KroneckerCollarRecovery

noncomputable def zeroProgram {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) : ConnectedColorings m (collarPath pairs V) 0 := by
  let r := runProgram hm p 0 g
  have hr := (runProgram_surplus hm p 0 g).2
  have hz : r.1-pairs.length=0 := by dsimp [r]; omega
  refine ⟨collarColoring (by omega) pairs hp r.1 V r.2.val,?_⟩
  simpa only [hz] using collarColoring_connected (by omega) pairs hp r.1 V r.2.val r.2.property

theorem zeroProgram_recover {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    recoverCollar pairs V (zeroProgram hm p pairs hp hsize g).val=(runProgram hm p 0 g).2.val :=
  recover_collarColoring (by omega) pairs hp _ V _

end KroneckerDeleteZeroProgram
end

/- Original module: KroneckerDeleteZeroProgramRecovery -/
section
/-! A proved compressed decoder for the actual zero-surplus program map. -/
set_option autoImplicit false
namespace KroneckerDeleteZeroProgramRecovery
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerInputRecovery
open KroneckerDeleteVerticalPrograms KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerRecoverySpecification
open KroneckerDeleteProgramExecution KroneckerDeleteProgramLayouts KroneckerDeleteProgramChangeLog KroneckerDeleteOriginalProgramRetention
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerDeleteZeroProgram

noncomputable def zeroProgramSpec {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (zeroProgram hm p pairs hp hsize) :=
  taggedSpec (connectedSource m U 0) (zeroProgram hm p pairs hp hsize) Subtype.val
    (collarLayout pairs (programLayout p (initialLayout U)))
    (programLog hm p (initialLayout U) 0) (programLog_bound hm p (initialLayout U) 0)
    (by rw [collarLayout_deleted]; exact original_program_deleted_bound p)
    (fun g => collar_retains (by omega) (connectedSource m U 0 g) _ _ _
      (original_program_retains hm p 0 g) pairs hp (runProgram hm p 0 g).1)

theorem zeroProgram_decode {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (zeroProgramSpec hm p pairs hp hsize).deleted (zeroProgramSpec hm p pairs hp hsize).deleted_card
      ((zeroProgramSpec hm p pairs hp hsize).retained (zeroProgram hm p pairs hp hsize g))
      (code (zeroProgramSpec hm p pairs hp hsize) g)=connectedSource m U 0 g :=
  recover_source (zeroProgramSpec hm p pairs hp hsize) g

end KroneckerDeleteZeroProgramRecovery
end

/- Original module: KroneckerDeleteZeroProgramCount -/
section
/-! The actual multi-vertical-edit comparison with one B_m(n,D) factor and a single surplus-zero target. -/
set_option autoImplicit false
namespace KroneckerDeleteZeroProgramCount
open KroneckerWordCounts KroneckerDeleteVerticalPrograms KroneckerCollarColoring KroneckerDeleteZeroProgram
open KroneckerDeleteZeroProgramRecovery KroneckerWordRecoveryCount KroneckerWordRecoveryFiber KroneckerFiberBudget

theorem zero_program_count {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 :=
  word_recovery_count_bound (zeroProgramSpec hm p pairs hp hsize)

theorem zero_program_real {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤ (pathCount m (collarPath pairs V) 0 : ℝ) :=
  word_recovery_real_bound (zeroProgramSpec hm p pairs hp hsize)

theorem zero_program_fiber {m : ℕ} (hm : 3 ≤ m) {U V : List Bool} {D : ℕ}
    (p : Program m U V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (b : ConnectedColorings m (collarPath pairs V) 0) :
    Nat.card {g // zeroProgram hm p pairs hp hsize g=b} ≤ fiberBudget m (U.count true) D :=
  word_recovery_fiber_bound (zeroProgramSpec hm p pairs hp hsize) b

end KroneckerDeleteZeroProgramCount
end

/- Original module: KroneckerDeletePreparedProgramRecovery -/
section
/-! Preparation may add unlabelled edges without enlarging the original recovery alphabet. -/
set_option autoImplicit false
namespace KroneckerDeletePreparedProgramRecovery
open KroneckerWordCounts KroneckerWordRecoveryFiber KroneckerOrientationPositions
open KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerDeleteVerticalPrograms
open KroneckerDeleteProgramLayouts KroneckerDeleteProgramChangeLog KroneckerDeleteProgramRetention KroneckerDeleteProgramExecution
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerDeleteZeroProgram
open KroneckerInputRecovery KroneckerRecoverySpecification

noncomputable def preparedSpec {m : ℕ} (hm : 3 ≤ m) {U W V : List Bool} {D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : Program m W V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (fun g => zeroProgram hm p pairs hp hs (prep g)) :=
  taggedSpec (connectedSource m U 0) (fun g => zeroProgram hm p pairs hp hs (prep g)) Subtype.val
    (collarLayout pairs (programLayout p L)) (fun g => programLog hm p L 0 (prep g))
    (fun g => programLog_bound hm p L 0 (prep g))
    (by rw [collarLayout_deleted]; have h := programLayout_deleted_bound p L; omega)
    (fun g => collar_retains (by omega) _ _ _ _ (program_retains hm p _ L 0 (prep g) (hk g))
      pairs hp (runProgram hm p 0 (prep g)).1)

theorem prepared_decode {m : ℕ} (hm : 3 ≤ m) {U W V : List Bool} {D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : Program m W V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (preparedSpec hm prep L hd hk p pairs hp hs).deleted
      (preparedSpec hm prep L hd hk p pairs hp hs).deleted_card
      ((preparedSpec hm prep L hd hk p pairs hp hs).retained (zeroProgram hm p pairs hp hs (prep g)))
      (code (preparedSpec hm prep L hd hk p pairs hp hs) g)=connectedSource m U 0 g :=
  recover_source (preparedSpec hm prep L hd hk p pairs hp hs) g

end KroneckerDeletePreparedProgramRecovery
end

/- Original module: KroneckerDeleteBufferedCount -/
section
/-! Two initial buffers cost no additional original horizontal positions in B_m(n,D). -/
set_option autoImplicit false
namespace KroneckerDeleteBufferedCount
open KroneckerDeleteProgramExecution
open KroneckerWordCounts KroneckerColoredShell KroneckerWrappedTags KroneckerTaggedLayout
open KroneckerDeleteVerticalPrograms KroneckerCollarColoring KroneckerDeletePreparedProgramRecovery
open KroneckerWordRecoveryCount KroneckerFiberBudget

theorem buffered_delete_count {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) {U V : List Bool} {D : ℕ}
    (p : Program m (shellPath u v U) V D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_count_bound (preparedSpec hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)

theorem buffered_delete_real {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) {U V : List Bool} {D : ℕ}
    (p : Program m (shellPath u v U) V D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤
      (pathCount m (collarPath pairs V) 0 : ℝ) := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_real_bound (preparedSpec hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)

end KroneckerDeleteBufferedCount
end

/- Original module: KroneckerDeleteMiddleLift -/
section
/-! Lift one raw middle deletion to the actual prescribed-shell deletion map. -/
set_option autoImplicit false
namespace KroneckerDeleteMiddleLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerDeleteVerticalPrograms KroneckerDeletionColoring
open KroneckerMiddleContext KroneckerMiddlePositions KroneckerContextDeletion KroneckerListDeletion

open KroneckerMiddleDeleteLift

def deleteLift {m u v : ℕ} {U V : List Bool} {D : ℕ} (pairs : List (ℕ×ℕ))
    (p : Program m (shellPath u v U) (collarPath pairs (shellPath u v V)) D)
    (x y i : ℕ) (hx : 1 ≤ x ∧ x ≤ m-1) (hy : 1 ≤ y ∧ y ≤ m-1)
    (hi : i < V.length) (hvertical : V[i]=false) :
    Program m (shellPath u v U) (collarPath ((x,y)::pairs) (shellPath u v (removeAt i V))) (D+1) := by
  simpa only [deleted_middle_path pairs u v x y i V hi] using
    Program.delete p x y ((leftContext pairs u).length+i) hx hy
      (middle_delete_bound pairs u v V i hi) (middle_vertical pairs u v V i hi hvertical)

end KroneckerDeleteMiddleLift
end

/- Original module: KroneckerDeleteRawLift -/
section
/-! Lift a raw program with zero insertions and zero complete-run additions.
The impossible constructors are eliminated from their exact cost indices. -/
set_option autoImplicit false
namespace KroneckerDeleteRawLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerDeleteVerticalPrograms
open KroneckerRawMixedPrograms KroneckerMiddleContext KroneckerDeleteMiddleLift

noncomputable def liftRaw {m u v : ℕ} {U V : List Bool} {K A D : ℕ}
    (p : RawProgram m U V K A D) (hK : K=0) (hA : A=0)
    (pairs : List (ℕ×ℕ)) (hlen : pairs.length=D) (hp : LegalPairs m pairs) :
    Program m (shellPath u v U) (collarPath pairs (shellPath u v V)) D := by
  induction p generalizing pairs with
  | nil =>
    have h : pairs=[] := List.length_eq_zero_iff.mp hlen
    subst pairs
    exact .nil
  | complete p r i hr hi ih => omega
  | insert p i hi ih => omega
  | @delete V K A D p i hi hv ih =>
    cases pairs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons pair pairs =>
      have htail : pairs.length=D := by simpa using hlen
      exact deleteLift pairs (ih hK hA pairs htail (fun q hq => hp q (by simp [hq])))
        pair.1 pair.2 i (hp pair (by simp)).1 (hp pair (by simp)).2 hi hv

end KroneckerDeleteRawLift
end

/- Original module: KroneckerDeleteRawCount -/
section
/-! One shared recovery budget for all prescribed deletions, including m=3. -/
set_option autoImplicit false
namespace KroneckerDeleteRawCount
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerCollarColoring
open KroneckerRawMixedPrograms KroneckerMiddleContext KroneckerDeleteRawLift KroneckerDeleteBufferedCount

theorem raw_delete_count {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) {U V : List Bool} {D : ℕ}
    (p : RawProgram m U V 0 0 D) (edit drain : List (ℕ×ℕ))
    (he : edit.length=D) (hle : LegalPairs m edit) (hld : LegalPairs m drain)
    (hd : m*D ≤ drain.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D *
      pathCount m (collarPath drain (collarPath edit (shellPath u v V))) 0 :=
  buffered_delete_count hm hu hv (liftRaw p rfl rfl edit he hle) drain hld hd

theorem raw_delete_real {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) {U V : List Bool} {D : ℕ}
    (p : RawProgram m U V 0 0 D) (edit drain : List (ℕ×ℕ))
    (he : edit.length=D) (hle : LegalPairs m edit) (hld : LegalPairs m drain)
    (hd : m*D ≤ drain.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤
      (pathCount m (collarPath drain (collarPath edit (shellPath u v V))) 0 : ℝ) :=
  buffered_delete_real hm hu hv (liftRaw p rfl rfl edit he hle) drain hld hd

end KroneckerDeleteRawCount
end

/- Original module: KroneckerDeletePrescribedCount -/
section
/-! Split fixed collar layers into D deletion shells and m*D draining shells. -/
set_option autoImplicit false
namespace KroneckerDeletePrescribedCount
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerCollarColoring
open KroneckerRawMixedPrograms KroneckerMiddleContext KroneckerDeleteRawCount
open KroneckerPrescribedLayerSplit KroneckerMixedLayerBudget

theorem prescribed_delete_count {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) {U V : List Bool} {D : ℕ}
    (p : RawProgram m U V 0 0 D) (pairs : List (ℕ×ℕ))
    (hp : LegalPairs m pairs) (hs : (m+1)*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D *
      pathCount m (collarPath pairs (shellPath u v V)) 0 := by
  let k := pairs.length-D
  have h : (pairs.drop k).length=D ∧ m*D ≤ (pairs.take k).length := by
    simp only [List.length_drop,List.length_take]
    dsimp [k]
    have : m*D+D ≤ pairs.length := by nlinarith [hs]
    omega
  have hc := raw_delete_count hm hu hv p (pairs.drop k) (pairs.take k) h.1
    (fun q hq => hp q ((List.drop_sublist k pairs).subset hq))
    (fun q hq => hp q ((List.take_sublist k pairs).subset hq)) h.2
  simpa only [← collarPath_append,List.take_append_drop] using hc

theorem prescribed_delete_real {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) {U V : List Bool} {D : ℕ}
    (p : RawProgram m U V 0 0 D) (pairs : List (ℕ×ℕ))
    (hp : LegalPairs m pairs) (hs : (m+1)*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤
      (pathCount m (collarPath pairs (shellPath u v V)) 0 : ℝ) := by
  have h := prescribed_delete_count hm hu hv p pairs hp hs
  have hb : (0 : ℝ) < fiberBudget m (U.count true) D := by
    exact_mod_cast KroneckerFiberBudget.fiberBudget_positive m (U.count true) D
  apply (div_le_iff₀ hb).mpr
  rw [mul_comm]
  exact_mod_cast h

end KroneckerDeletePrescribedCount
end
