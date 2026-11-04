import KroneckerCollarPaletteRetention

/- Original module: KroneckerZeroProgram -/
section
/-! Drain the surplus of an actual mixed vertical-edit program on a fixed prescribed target path. -/
set_option autoImplicit false
namespace KroneckerZeroProgram
open KroneckerWordCounts KroneckerVerticalPrograms KroneckerProgramExecution KroneckerProgramSurplus
open KroneckerCollarColoring KroneckerCollarConnected KroneckerCollarRecovery

noncomputable def zeroProgram {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) : ConnectedColorings m (collarPath pairs V) 0 := by
  let r := runProgram hm p 0 g
  have hr := (runProgram_surplus hm p 0 g).2
  have hz : r.1-pairs.length=0 := by dsimp [r]; omega
  refine ⟨collarColoring (by omega) pairs hp r.1 V r.2.val,?_⟩
  simpa only [hz] using collarColoring_connected (by omega) pairs hp r.1 V r.2.val r.2.property

theorem zeroProgram_recover {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    recoverCollar pairs V (zeroProgram hm p pairs hp hsize g).val=(runProgram hm p 0 g).2.val :=
  recover_collarColoring (by omega) pairs hp _ V _

end KroneckerZeroProgram
end

/- Original module: KroneckerZeroProgramRecovery -/
section
/-! A proved compressed decoder for the actual zero-surplus program map. -/
set_option autoImplicit false
namespace KroneckerZeroProgramRecovery
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerInputRecovery
open KroneckerVerticalPrograms KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerRecoverySpecification
open KroneckerProgramExecution KroneckerProgramLayouts KroneckerProgramChangeLog KroneckerOriginalProgramRetention
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerZeroProgram

noncomputable def zeroProgramSpec {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (zeroProgram hm p pairs hp hsize) :=
  taggedSpec (connectedSource m U 0) (zeroProgram hm p pairs hp hsize) Subtype.val
    (collarLayout pairs (programLayout p (initialLayout U)))
    (programLog hm p (initialLayout U) 0) (programLog_bound hm p (initialLayout U) 0)
    (by rw [collarLayout_deleted]; exact original_program_deleted_bound p)
    (fun g => collar_retains (by omega) (connectedSource m U 0 g) _ _ _
      (original_program_retains hm p 0 g) pairs hp (runProgram hm p 0 g).1)

theorem zeroProgram_decode {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (zeroProgramSpec hm p pairs hp hsize).deleted (zeroProgramSpec hm p pairs hp hsize).deleted_card
      ((zeroProgramSpec hm p pairs hp hsize).retained (zeroProgram hm p pairs hp hsize g))
      (code (zeroProgramSpec hm p pairs hp hsize) g)=connectedSource m U 0 g :=
  recover_source (zeroProgramSpec hm p pairs hp hsize) g

end KroneckerZeroProgramRecovery
end

/- Original module: KroneckerZeroProgramCount -/
section
/-! The actual multi-vertical-edit comparison with one B_m(n,D) factor and a single surplus-zero target. -/
set_option autoImplicit false
namespace KroneckerZeroProgramCount
open KroneckerWordCounts KroneckerVerticalPrograms KroneckerCollarColoring KroneckerZeroProgram
open KroneckerZeroProgramRecovery KroneckerWordRecoveryCount KroneckerWordRecoveryFiber KroneckerFiberBudget

theorem zero_program_count {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 :=
  word_recovery_count_bound (zeroProgramSpec hm p pairs hp hsize)

theorem zero_program_real {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤ (pathCount m (collarPath pairs V) 0 : ℝ) :=
  word_recovery_real_bound (zeroProgramSpec hm p pairs hp hsize)

theorem zero_program_fiber {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : m*D ≤ pairs.length)
    (b : ConnectedColorings m (collarPath pairs V) 0) :
    Nat.card {g // zeroProgram hm p pairs hp hsize g=b} ≤ fiberBudget m (U.count true) D :=
  word_recovery_fiber_bound (zeroProgramSpec hm p pairs hp hsize) b

end KroneckerZeroProgramCount
end

/- Original module: KroneckerPreparedProgramRecovery -/
section
/-! Preparation may add unlabelled edges without enlarging the original recovery alphabet. -/
set_option autoImplicit false
namespace KroneckerPreparedProgramRecovery
open KroneckerWordCounts KroneckerWordRecoveryFiber KroneckerOrientationPositions
open KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerVerticalPrograms
open KroneckerProgramLayouts KroneckerProgramChangeLog KroneckerProgramRetention KroneckerProgramExecution
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerZeroProgram
open KroneckerInputRecovery KroneckerRecoverySpecification

noncomputable def preparedSpec {m : ℕ} (hm : 4 ≤ m) {U W V : List Bool} {A D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : Program m W V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (fun g => zeroProgram hm p pairs hp hs (prep g)) :=
  taggedSpec (connectedSource m U 0) (fun g => zeroProgram hm p pairs hp hs (prep g)) Subtype.val
    (collarLayout pairs (programLayout p L)) (fun g => programLog hm p L 0 (prep g))
    (fun g => programLog_bound hm p L 0 (prep g))
    (by rw [collarLayout_deleted]; have h := programLayout_deleted_bound p L; omega)
    (fun g => collar_retains (by omega) _ _ _ _ (program_retains hm p _ L 0 (prep g) (hk g))
      pairs hp (runProgram hm p 0 (prep g)).1)

theorem prepared_decode {m : ℕ} (hm : 4 ≤ m) {U W V : List Bool} {A D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : Program m W V A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (preparedSpec hm prep L hd hk p pairs hp hs).deleted
      (preparedSpec hm prep L hd hk p pairs hp hs).deleted_card
      ((preparedSpec hm prep L hd hk p pairs hp hs).retained (zeroProgram hm p pairs hp hs (prep g)))
      (code (preparedSpec hm prep L hd hk p pairs hp hs) g)=connectedSource m U 0 g :=
  recover_source (preparedSpec hm prep L hd hk p pairs hp hs) g

end KroneckerPreparedProgramRecovery
end

/- Original module: KroneckerBufferedProgramCount -/
section
/-! Two initial buffers cost no additional original horizontal positions in B_m(n,D). -/
set_option autoImplicit false
namespace KroneckerBufferedProgramCount
open KroneckerWordCounts KroneckerColoredShell KroneckerWrappedTags KroneckerTaggedLayout
open KroneckerVerticalPrograms KroneckerCollarColoring KroneckerPreparedProgramRecovery
open KroneckerWordRecoveryCount KroneckerFiberBudget

theorem buffered_program_count {m u v : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {A D : ℕ}
    (p : Program m (shellPath u v U) V A D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_count_bound (preparedSpec hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)


end KroneckerBufferedProgramCount
end

/- Original module: KroneckerContextInsertion -/
section
/-! A fixed middle insertion commutes with the surrounding fixed path context. -/
set_option autoImplicit false
namespace KroneckerContextInsertion
open KroneckerListInsertion

theorem insertAt_context {α : Type*} (pre xs post : List α) (i : ℕ) (a : α) (hi : i ≤ xs.length) :
    insertAt (pre.length+i) a (pre++xs++post)=pre++insertAt i a xs++post := by
  induction pre with
  | nil =>
    simp only [List.length_nil,Nat.zero_add,List.nil_append,insertAt]
    rw [List.take_append_of_le_length hi,List.drop_append_of_le_length hi]
    simp only [List.append_assoc,List.cons_append]
  | cons b pre ih =>
    simpa only [List.length_cons,Nat.add_right_comm, List.cons_append,insertAt,
      List.take_succ_cons,List.drop_succ_cons] using congrArg (List.cons b) ih

end KroneckerContextInsertion
end

/- Original module: KroneckerContextDeletion -/
section
/-! A fixed middle deletion and its orientation lookup commute with the fixed path context. -/
set_option autoImplicit false
namespace KroneckerContextDeletion
open KroneckerListDeletion

theorem removeAt_context {α : Type*} (pre xs post : List α) (i : ℕ) (hi : i < xs.length) :
    removeAt (pre.length+i) (pre++xs++post)=pre++removeAt i xs++post := by
  induction pre with
  | nil =>
    simp only [List.length_nil,Nat.zero_add,List.nil_append,removeAt]
    rw [List.take_append_of_le_length (by omega),List.drop_append_of_le_length (by omega)]
    simp only [List.append_assoc]
  | cons b pre ih =>
    simpa only [List.length_cons,Nat.add_right_comm,List.cons_append,removeAt,
      List.take_succ_cons,List.drop_succ_cons] using congrArg (List.cons b) ih

theorem getElem_context {α : Type*} (pre xs post : List α) (i : ℕ) (hi : i < xs.length) :
    (pre++xs++post)[pre.length+i]'(by simp; omega)=xs[i] := by
  rw [List.getElem_append_left (by simp; omega),List.getElem_append_right (by omega)]
  simp

end KroneckerContextDeletion
end
