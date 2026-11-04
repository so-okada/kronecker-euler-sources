import KroneckerProgramExecution

/- Original module: KroneckerProgramSurplus -/
section
/-! A mixed vertical-edit program preserves the lower surplus bound and adds at most m per deletion. -/
set_option autoImplicit false
namespace KroneckerProgramSurplus
open KroneckerWordCounts KroneckerVerticalPrograms KroneckerProgramExecution KroneckerVerticalDeletionMap

theorem runProgram_surplus {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) (g : ConnectedColorings m U c) :
    c ≤ (runProgram hm p c g).1 ∧ (runProgram hm p c g).1 ≤ c+m*D := by
  induction p with
  | nil => simp [runProgram]
  | insert p u v i hu hv hi ih => exact ih
  | @delete V A D p u v i hu hv hi hvert ih =>
    have hh := (verticalDeletion u v (runProgram hm p c g).1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvert (runProgram hm p c g).2).1.isLt
    change c ≤ (runProgram hm p c g).1+_ ∧ (runProgram hm p c g).1+_ ≤ c+m*(D+1)
    simp only [Nat.mul_add,Nat.mul_one]
    omega

end KroneckerProgramSurplus
end

/- Original module: KroneckerProgramChangeLog -/
section
/-! Log only original horizontal labels changed by actual deletions in the program. -/
set_option autoImplicit false
namespace KroneckerProgramChangeLog
open KroneckerWordCounts KroneckerVerticalPrograms KroneckerProgramExecution KroneckerProgramLayouts
open KroneckerTaggedLayout KroneckerTaggedDeletion KroneckerDeletionChoice

noncomputable def programLog {m n q : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) : List (Fin n) :=
  match p with
  | .nil => []
  | .insert p _ _ _ _ _ _ => programLog hm p L c g
  | .delete p u v i hu hv hi hvert =>
    let old := runProgram hm p c g
    let j := chosenIndex u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvert old.2
    changedAt (programLayout p L) ⟨j.val,lt_trans j.isLt hi⟩ (programLog hm p L c g)

theorem programLog_bound {m n q : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) :
    (programLog hm p L c g).length ≤ D := by
  induction p with
  | nil => simp [programLog]
  | insert p u v i hu hv hi ih => exact ih
  | delete p u v i hu hv hi hvert ih =>
    apply (changedAt_bound _ _ _).trans
    exact Nat.add_le_add_right ih 1

end KroneckerProgramChangeLog
end

/- Original module: KroneckerProgramRetention -/
section
/-! Compose the proved local palette-retention invariants along the actual program. -/
set_option autoImplicit false
namespace KroneckerProgramRetention
open KroneckerColoring KroneckerInputRecovery KroneckerWordCounts KroneckerVerticalPrograms
open KroneckerProgramExecution KroneckerProgramLayouts KroneckerProgramChangeLog
open KroneckerTaggedLayout KroneckerTaggedInsertion KroneckerTaggedDeletion
open KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap KroneckerDeletionChoice

set_option backward.isDefEq.respectTransparency false in
theorem program_retains {m n q : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (source : Input m n q) (L : Layout n q U) (c : ℕ)
    (g : ConnectedColorings m U c) (hinit : Retains source [] L g.val) :
    Retains source (programLog hm p L c g) (programLayout p L) (runProgram hm p c g).2.val := by
  induction p with
  | nil => exact hinit
  | insert p u v i hu hv hi ih =>
    simpa only [programLog,programLayout,runProgram,verticalInsertion] using
      insertion_retains source (programLog hm p L c g) (programLayout p L)
        (runProgram hm p c g).2.val ih u v i (by omega) (by omega) (by omega) hv.1
  | @delete V A D p u v i hu hv hi hvert ih =>
    let old := runProgram hm p c g
    let j := chosenIndex u v old.1 (by omega) (by omega) (by omega) hv.1 V i hi hvert old.2
    have hj : V[j.val]=true := (chosenIndex_spec u v old.1 (by omega) (by omega) (by omega)
      hv.1 V i hi hvert old.2).1
    simpa only [programLog,programLayout,runProgram,verticalDeletion] using
      deletion_retains source (programLog hm p L c g) (programLayout p L) old.2.val ih
        u v i (by omega) (by omega) (by omega) hv.1 hi hvert j hj

end KroneckerProgramRetention
end

/- Original module: KroneckerOriginalProgramRetention -/
section
/-! Initialize the actual composed program on the original horizontal and vertical color arrays. -/
set_option autoImplicit false
namespace KroneckerOriginalProgramRetention
open KroneckerWordCounts KroneckerWordPaletteSplit KroneckerVerticalPrograms KroneckerTaggedLayout
open KroneckerProgramExecution KroneckerProgramLayouts KroneckerProgramChangeLog KroneckerProgramRetention

theorem original_program_retains {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) (g : ConnectedColorings m U c) :
    Retains (splitColoring U g.val) (programLog hm p (initialLayout U) c g)
      (programLayout p (initialLayout U)) (runProgram hm p c g).2.val :=
  program_retains hm p (splitColoring U g.val) (initialLayout U) c g (initialLayout_retains U g.val)

theorem original_program_deleted_bound {m : ℕ} {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) : (programLayout p (initialLayout U)).deleted.length ≤ D := by
  simpa only [initialLayout,List.length_nil,Nat.zero_add] using programLayout_deleted_bound p (initialLayout U)

end KroneckerOriginalProgramRetention
end

/- Original module: KroneckerActualProgramRecovery -/
section
/-! A concrete compressed RecoverySpec for the constructed multi-edit map, with no structural premise. -/
set_option autoImplicit false
namespace KroneckerActualProgramRecovery
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerInputRecovery
open KroneckerVerticalPrograms KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerRecoverySpecification
open KroneckerProgramExecution KroneckerProgramLayouts KroneckerProgramChangeLog KroneckerOriginalProgramRetention

noncomputable def programSpec {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) :
    RecoverySpec m (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) D
      (connectedSource m U c) (runProgram hm p c) :=
  taggedSpec (connectedSource m U c) (runProgram hm p c)
    (fun b : SurplusColorings m V => b.2.val) (programLayout p (initialLayout U))
    (programLog hm p (initialLayout U) c) (programLog_bound hm p (initialLayout U) c)
    (original_program_deleted_bound p) (original_program_retains hm p c)

theorem program_recover {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) (g : ConnectedColorings m U c) :
    decodeInput (programSpec hm p c).deleted (programSpec hm p c).deleted_card
      ((programSpec hm p c).retained (runProgram hm p c g))
      (code (programSpec hm p c) g)=connectedSource m U c g :=
  recover_source (programSpec hm p c) g

end KroneckerActualProgramRecovery
end

/- Original module: KroneckerProgramFiber -/
section
/-! The full program uses one compressed code, including repeated changes and edits to inserted edges. -/
set_option autoImplicit false
namespace KroneckerProgramFiber
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerFiberBudget
open KroneckerVerticalPrograms KroneckerProgramExecution KroneckerActualProgramRecovery
open KroneckerRecoverySpecification KroneckerReconstructionFiber

theorem program_code_injective {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) :
    Function.Injective (fun g : ConnectedColorings m U c =>
      (runProgram hm p c g,code (programSpec hm p c) g)) :=
  target_code_injective (programSpec hm p c) (connectedSource_injective m U c)

theorem program_fiber_bound {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) (b : SurplusColorings m V) :
    Nat.card {g // runProgram hm p c g=b} ≤ fiberBudget m (U.count true) D := by
  classical
  simpa only [positions_card] using
    reconstruction_fiber_bound (programSpec hm p c) (connectedSource_injective m U c) b

end KroneckerProgramFiber
end

/- Original module: KroneckerProgramCount -/
section
/-! A finite surplus-indexed count bound for the actual complete vertical-edit program. -/
set_option autoImplicit false
namespace KroneckerProgramCount
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerFiberBudget
open KroneckerVerticalPrograms KroneckerProgramExecution KroneckerProgramSurplus KroneckerProgramLayouts
open KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerProgramChangeLog KroneckerOriginalProgramRetention
open KroneckerRecoverySpecification KroneckerRecoveryCode
open scoped BigOperators

abbrev BoundedOutput (m D c : ℕ) (V : List Bool) :=
  (h : Fin (m*D+1)) × ConnectedColorings m V (c+h.val)

noncomputable def boundedProgram {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) (g : ConnectedColorings m U c) : BoundedOutput m D c V := by
  let r := runProgram hm p c g
  have hr := runProgram_surplus hm p c g
  refine ⟨⟨r.1-c,by dsimp [r]; omega⟩,⟨r.2.val,?_⟩⟩
  have he : c+(r.1-c)=r.1 := by dsimp [r]; omega
  simpa only [he] using r.2.property

theorem boundedProgram_palette {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) (g : ConnectedColorings m U c) :
    (boundedProgram hm p c g).2.val=(runProgram hm p c g).2.val := rfl

theorem program_count_bound {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {A D : ℕ}
    (p : Program m U V A D) (c : ℕ) :
    pathCount m U c ≤ fiberBudget m (U.count true) D*
      ∑ h : Fin (m*D+1),pathCount m V (c+h.val) := by
  classical
  let s := taggedSpec (connectedSource m U c) (boundedProgram hm p c)
    (fun b : BoundedOutput m D c V => b.2.val) (programLayout p (initialLayout U))
    (programLog hm p (initialLayout U) c) (programLog_bound hm p (initialLayout U) c)
    (original_program_deleted_bound p) (original_program_retains hm p c)
  have h := Fintype.card_le_of_injective (fun g => (boundedProgram hm p c g,code s g))
    (target_code_injective s (connectedSource_injective m U c))
  rw [Fintype.card_prod,recoveryCode_card] at h
  simpa only [pathCount,Nat.card_eq_fintype_card,BoundedOutput,Fintype.card_sigma,positions_card,Nat.mul_comm] using h

end KroneckerProgramCount
end

/- Original module: KroneckerTaggedCollars -/
section
/-! Attach fixed prescribed collars without changing any original tag or deletion record. -/
set_option autoImplicit false
namespace KroneckerTaggedCollars
open KroneckerTaggedLayout KroneckerWrappedTags KroneckerCollarColoring

def collarLayout {n q : ℕ} {U : List Bool} (pairs : List (ℕ×ℕ)) (L : Layout n q U) :
    Layout n q (collarPath pairs U) :=
  match pairs with
  | [] => L
  | p::ps => wrapLayout p.1 p.2 (collarLayout ps L)

theorem collarLayout_deleted {n q : ℕ} {U : List Bool} (pairs : List (ℕ×ℕ)) (L : Layout n q U) :
    (collarLayout pairs L).deleted=L.deleted := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => exact ih

end KroneckerTaggedCollars
end

/- Original module: KroneckerCollarPaletteRetention -/
section
/-! All prescribed draining and preserving collar layers retain the original tagged palettes. -/
set_option autoImplicit false
namespace KroneckerCollarPaletteRetention
open KroneckerColoring KroneckerInputRecovery KroneckerTaggedLayout KroneckerTaggedCollars
open KroneckerTaggedAutomaticShell KroneckerCollarColoring

theorem collar_retains {m n q : ℕ} (hm : 3 ≤ m) {U : List Bool} (source : Input m n q)
    (changed : List (Fin n)) (L : Layout n q U) (g : Coloring m U.length) (hg : Retains source changed L g)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (c : ℕ) :
    Retains source changed (collarLayout pairs L) (collarColoring hm pairs hp c U g) := by
  induction pairs with
  | nil => exact hg
  | cons p ps ih =>
    have ht : LegalPairs m ps := fun a ha => hp a (by simp [ha])
    exact autoColoring_retains source changed (collarLayout ps L) (collarColoring hm ps ht c U g)
      (ih ht) p.1 p.2 (c-ps.length) hm (hp p (by simp)).1 (hp p (by simp)).2

end KroneckerCollarPaletteRetention
end
