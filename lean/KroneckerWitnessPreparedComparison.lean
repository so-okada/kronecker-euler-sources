import KroneckerWitnessDeletePrograms

set_option autoImplicit false
noncomputable section
namespace KroneckerWitnessPreparedMixedRecovery
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerWordRecoveryFiber KroneckerOrientationPositions
open KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerMixedPrograms
open KroneckerMixedLayouts KroneckerWitnessMixedChangeLog KroneckerWitnessMixedRetention KroneckerWitnessMixedExecution
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerWitnessZeroMixed
open KroneckerInputRecovery KroneckerRecoverySpecification

noncomputable def preparedMixedSpec {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U W V : List Bool} {K A D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : MixedProgram m W V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (fun g => zeroMixed rule hm p pairs hp hs (prep g)) :=
  taggedSpec (connectedSource m U 0) (fun g => zeroMixed rule hm p pairs hp hs (prep g)) Subtype.val
    (collarLayout pairs (mixedLayout p L)) (fun g => mixedLog rule hm p L 0 (prep g))
    (fun g => mixedLog_bound rule hm p L 0 (prep g))
    (by rw [collarLayout_deleted]; have h := mixedLayout_deleted_bound p L; omega)
    (fun g => collar_retains (by omega) _ _ _ _ (mixed_retains rule hm p _ L 0 (prep g) (hk g))
      pairs hp (runMixed rule hm p 0 (prep g)).1)

theorem preparedMixed_decode {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m) {U W V : List Bool} {K A D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : MixedProgram m W V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (preparedMixedSpec rule hm prep L hd hk p pairs hp hs).deleted
      (preparedMixedSpec rule hm prep L hd hk p pairs hp hs).deleted_card
      ((preparedMixedSpec rule hm prep L hd hk p pairs hp hs).retained (zeroMixed rule hm p pairs hp hs (prep g)))
      (code (preparedMixedSpec rule hm prep L hd hk p pairs hp hs) g)=connectedSource m U 0 g :=
  recover_source (preparedMixedSpec rule hm prep L hd hk p pairs hp hs) g

end KroneckerWitnessPreparedMixedRecovery


namespace KroneckerWitnessBufferedMixedCount
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerColoredShell KroneckerWrappedTags KroneckerTaggedLayout
open KroneckerMixedPrograms KroneckerCollarColoring KroneckerWitnessPreparedMixedRecovery
open KroneckerWordRecoveryCount KroneckerFiberBudget

theorem buffered_mixed_count {m u v : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m (shellPath u v U) V K A D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_count_bound (preparedMixedSpec rule hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)

theorem buffered_mixed_real {m u v : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m (shellPath u v U) V K A D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤
      (pathCount m (collarPath pairs V) 0 : ℝ) := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_real_bound (preparedMixedSpec rule hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)

end KroneckerWitnessBufferedMixedCount


namespace KroneckerWitnessDeletePreparedProgramRecovery
open KroneckerWordCounts KroneckerWordRecoveryFiber KroneckerOrientationPositions
open KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerDeleteVerticalPrograms
open KroneckerDeleteProgramLayouts KroneckerWitnessDeleteProgramChangeLog KroneckerWitnessDeleteProgramRetention KroneckerWitnessDeleteProgramExecution
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerWitnessDeleteZeroProgram
open KroneckerInputRecovery KroneckerRecoverySpecification

noncomputable def preparedSpec {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U W V : List Bool} {D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : Program m W V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (fun g => zeroProgram rule hm p pairs hp hs (prep g)) :=
  taggedSpec (connectedSource m U 0) (fun g => zeroProgram rule hm p pairs hp hs (prep g)) Subtype.val
    (collarLayout pairs (programLayout p L)) (fun g => programLog rule hm p L 0 (prep g))
    (fun g => programLog_bound rule hm p L 0 (prep g))
    (by rw [collarLayout_deleted]; have h := programLayout_deleted_bound p L; omega)
    (fun g => collar_retains (by omega) _ _ _ _ (program_retains rule hm p _ L 0 (prep g) (hk g))
      pairs hp (runProgram rule hm p 0 (prep g)).1)

theorem prepared_decode {m : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m) {U W V : List Bool} {D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : Program m W V D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (preparedSpec rule hm prep L hd hk p pairs hp hs).deleted
      (preparedSpec rule hm prep L hd hk p pairs hp hs).deleted_card
      ((preparedSpec rule hm prep L hd hk p pairs hp hs).retained (zeroProgram rule hm p pairs hp hs (prep g)))
      (code (preparedSpec rule hm prep L hd hk p pairs hp hs) g)=connectedSource m U 0 g :=
  recover_source (preparedSpec rule hm prep L hd hk p pairs hp hs) g

end KroneckerWitnessDeletePreparedProgramRecovery


namespace KroneckerWitnessDeleteBufferedCount
open KroneckerWitnessDeleteProgramExecution
open KroneckerWordCounts KroneckerColoredShell KroneckerWrappedTags KroneckerTaggedLayout
open KroneckerDeleteVerticalPrograms KroneckerCollarColoring KroneckerWitnessDeletePreparedProgramRecovery
open KroneckerWordRecoveryCount KroneckerFiberBudget

theorem buffered_delete_count {m u v : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) {U V : List Bool} {D : ℕ}
    (p : Program m (shellPath u v U) V D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_count_bound (preparedSpec rule hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)

theorem buffered_delete_real {m u v : ℕ} (rule : ℕ → KroneckerDeletionWitness.Rule m) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) {U V : List Bool} {D : ℕ}
    (p : Program m (shellPath u v U) V D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤
      (pathCount m (collarPath pairs V) 0 : ℝ) := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_real_bound (preparedSpec rule hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)

end KroneckerWitnessDeleteBufferedCount

