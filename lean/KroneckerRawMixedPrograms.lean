import KroneckerCompleteRunInjection

/- Original module: KroneckerSpliceTagCoverage -/
section
/-! Block insertion retains every original tag and respects pointwise alignment. -/
set_option autoImplicit false
namespace KroneckerSpliceTagCoverage
open KroneckerListSplice KroneckerOriginalTags KroneckerTagCoverage

theorem mem_splice {α : Type*} (xs block : List α) (i : ℕ) (a : α) (ha : a ∈ xs) :
    a ∈ splice i block xs := by
  have h : a ∈ xs.take i++xs.drop i := by simpa using ha
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append_left _ (List.mem_append_left _ h)
  · exact List.mem_append_right _ h

theorem covers_splice {n q : ℕ} (tags block : List (Tag n q)) (deleted : List (Fin q))
    (h : Covers tags deleted) (i : ℕ) : Covers (splice i block tags) deleted :=
  ⟨fun j => mem_splice tags block i _ (h.horizontal j),
    fun j hj => mem_splice tags block i _ (h.vertical j hj)⟩

theorem rel_splice {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    {a : List α} {b : List β} (h : List.Forall₂ R xs ys) (hab : List.Forall₂ R a b) (i : ℕ) :
    List.Forall₂ R (splice i a xs) (splice i b ys) :=
  List.rel_append (List.rel_append (List.forall₂_take i h) hab) (List.forall₂_drop i h)

end KroneckerSpliceTagCoverage
end

/- Original module: KroneckerCompleteRunLayout -/
section
/-! Complete-run edges are unlabelled additions to the static original-edge layout. -/
set_option autoImplicit false
namespace KroneckerCompleteRunLayout
open KroneckerStack KroneckerListSplice KroneckerTaggedLayout KroneckerEmptyTags
open KroneckerSpliceTagCoverage KroneckerCompleteRunPalette

def completeLayout {n q : ℕ} {U : List Bool} (r i : ℕ) (L : Layout n q U) :
    Layout n q (completePath r i U) where
  tags := splice i (List.replicate (r+1) none) L.tags
  typed := by
    simpa only [completePath,runShape,List.length_cons,List.length_replicate] using
      rel_splice L.typed (compatible_none (runShape r)) i
  deleted := L.deleted
  covers := covers_splice L.tags _ L.deleted L.covers i

theorem completeLayout_deleted {n q : ℕ} {U : List Bool} (r i : ℕ) (L : Layout n q U) :
    (completeLayout r i L).deleted=L.deleted := rfl

end KroneckerCompleteRunLayout
end

/- Original module: KroneckerCompleteRunRetention -/
section
/-! Complete-run insertion preserves all original palette entries and requires no recovery log. -/
set_option autoImplicit false
namespace KroneckerCompleteRunRetention
open KroneckerColoring KroneckerInputRecovery KroneckerColoredShell KroneckerTaggedLayout
open KroneckerEmptyTags KroneckerSpliceTagCoverage KroneckerCompleteRunLayout KroneckerCompleteRunPalette

theorem completeColoring_retains {m n q : ℕ} {U : List Bool} (source : Input m n q)
    (changed : List (Fin n)) (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (r i : ℕ) (hr : r ≤ m) : Retains source changed (completeLayout r i L) (completeColoring r i hr U g) := by
  unfold Retains
  rw [completeColoring,fromList_colors]
  simpa only [completeLayout,completeColors,childColors,List.length_cons,List.length_replicate] using
    rel_splice h (keeps_none source changed (childColors m r hr)) i

end KroneckerCompleteRunRetention
end

/- Original module: KroneckerMixedPrograms -/
section
/-! Fixed actual programs with complete-run, vertical-insertion and vertical-deletion steps in any order. -/
set_option autoImplicit false
namespace KroneckerMixedPrograms
open KroneckerInsertionPalette KroneckerDeletionColoring KroneckerCompleteRunPalette

inductive MixedProgram (m : ℕ) (U : List Bool) : List Bool → ℕ → ℕ → ℕ → Type
  | nil : MixedProgram m U U 0 0 0
  | complete {V : List Bool} {K A D : ℕ} (p : MixedProgram m U V K A D) (r i : ℕ)
      (hr : 1 ≤ r ∧ r ≤ m-2) (hi : 1 ≤ i ∧ i < V.length) :
      MixedProgram m U (completePath r i V) (K+1) A D
  | insert {V : List Bool} {K A D : ℕ} (p : MixedProgram m U V K A D) (u v i : ℕ)
      (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) (hi : 1 ≤ i ∧ i ≤ V.length) :
      MixedProgram m U (insertedPath u v i V) K (A+1) D
  | delete {V : List Bool} {K A D : ℕ} (p : MixedProgram m U V K A D) (u v i : ℕ)
      (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2)
      (hi : i < V.length) (hvrt : V[i]=false) :
      MixedProgram m U (deletionPath u v V i) K A (D+1)

def steps {m : ℕ} {U V : List Bool} {K A D : ℕ} : MixedProgram m U V K A D → ℕ
  | .nil => 0
  | .complete p _ _ _ _ => steps p+1
  | .insert p _ _ _ _ _ _ => steps p+1
  | .delete p _ _ _ _ _ _ _ => steps p+1

theorem mixed_steps {m : ℕ} {U V : List Bool} {K A D : ℕ} (p : MixedProgram m U V K A D) :
    steps p=K+A+D := by
  induction p with
  | nil => rfl
  | complete p r i hr hi ih => simp only [steps,ih]; omega
  | insert p u v i hu hv hi ih => simp only [steps,ih]; omega
  | delete p u v i hu hv hi hvrt ih => simp only [steps,ih]; omega

end KroneckerMixedPrograms
end

/- Original module: KroneckerMixedLayouts -/
section
/-! The original-edge layout of a full mixed program is independent of the input colors. -/
set_option autoImplicit false
namespace KroneckerMixedLayouts
open KroneckerTaggedLayout KroneckerWrappedTags KroneckerEditedLayouts
open KroneckerCompleteRunLayout KroneckerMixedPrograms

def mixedLayout {m n q : ℕ} {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (L : Layout n q U) : Layout n q V :=
  match p with
  | .nil => L
  | .complete p r i _ _ => completeLayout r i (mixedLayout p L)
  | .insert p u v i _ _ _ => wrapLayout u v (insertLayout i (mixedLayout p L))
  | .delete p u v i _ _ hi hvrt => wrapLayout u v (removeLayout i hi hvrt (mixedLayout p L))

theorem mixedLayout_deleted_bound {m n q : ℕ} {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (L : Layout n q U) :
    (mixedLayout p L).deleted.length ≤ L.deleted.length+D := by
  induction p with
  | nil => simp [mixedLayout]
  | complete p r i hr hi ih => exact ih
  | insert p u v i hu hv hi ih => exact ih
  | delete p u v i hu hv hi hvrt ih =>
    have h := removeLayout_deleted_bound i hi hvrt (mixedLayout p L)
    change (removeLayout i hi hvrt (mixedLayout p L)).deleted.length ≤ _
    omega

end KroneckerMixedLayouts
end

/- Original module: KroneckerMixedExecution -/
section
/-! Execute the actual colored maps for arbitrary mixed edit order. -/
set_option autoImplicit false
namespace KroneckerMixedExecution
open KroneckerWordCounts KroneckerProgramExecution KroneckerMixedPrograms
open KroneckerCompleteRunMap KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap

noncomputable def runMixed {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) : SurplusColorings m V :=
  match p with
  | .nil => ⟨c,g⟩
  | .complete p r i hr hi =>
    let old := runMixed hm p c g
    ⟨old.1+1,completeRun r i old.1 (by omega) _ hi old.2⟩
  | .insert p u v i hu hv hi =>
    let old := runMixed hm p c g
    ⟨old.1,verticalInsertion u v i old.1 hm hu hv _ hi old.2⟩
  | .delete p u v i hu hv hi hvrt =>
    let old := runMixed hm p c g
    let d := verticalDeletion u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvrt old.2
    ⟨old.1+d.1.val,d.2⟩

theorem runMixed_complete_surplus {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (r i : ℕ) (hr : 1 ≤ r ∧ r ≤ m-2)
    (hi : 1 ≤ i ∧ i < V.length) (c : ℕ) (g : ConnectedColorings m U c) :
    (runMixed hm (.complete p r i hr hi) c g).1=(runMixed hm p c g).1+1 := rfl

end KroneckerMixedExecution
end

/- Original module: KroneckerMixedSurplus -/
section
/-! K complete runs contribute K surplus units; D deletions contribute at most mD. -/
set_option autoImplicit false
namespace KroneckerMixedSurplus
open KroneckerWordCounts KroneckerMixedPrograms KroneckerMixedExecution KroneckerVerticalDeletionMap

theorem runMixed_surplus {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) :
    c+K ≤ (runMixed hm p c g).1 ∧ (runMixed hm p c g).1 ≤ c+K+m*D := by
  induction p with
  | nil => simp [runMixed]
  | complete p r i hr hi ih =>
    change c+(_+1) ≤ (runMixed hm p c g).1+1 ∧ (runMixed hm p c g).1+1 ≤ c+(_+1)+_
    omega
  | insert p u v i hu hv hi ih => exact ih
  | @delete V K A D p u v i hu hv hi hvrt ih =>
    have hh := (verticalDeletion u v (runMixed hm p c g).1 (by omega) (by omega)
      (by omega) hv.1 V i hi hvrt (runMixed hm p c g).2).1.isLt
    change c+K ≤ (runMixed hm p c g).1+_ ∧ (runMixed hm p c g).1+_ ≤ c+K+m*(D+1)
    simp only [Nat.mul_add,Nat.mul_one]
    omega

end KroneckerMixedSurplus
end

/- Original module: KroneckerMixedChangeLog -/
section
/-! Complete-run insertion requires no original-horizontal change records. -/
set_option autoImplicit false
namespace KroneckerMixedChangeLog
open KroneckerWordCounts KroneckerMixedPrograms KroneckerMixedExecution KroneckerMixedLayouts
open KroneckerTaggedLayout KroneckerTaggedDeletion KroneckerDeletionChoice

noncomputable def mixedLog {m n q : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) : List (Fin n) :=
  match p with
  | .nil => []
  | .complete p _ _ _ _ => mixedLog hm p L c g
  | .insert p _ _ _ _ _ _ => mixedLog hm p L c g
  | .delete p u v i hu hv hi hvrt =>
    let old := runMixed hm p c g
    let j := chosenIndex u v old.1 (by omega) (by omega) (by omega) hv.1 _ i hi hvrt old.2
    changedAt (mixedLayout p L) ⟨j.val,lt_trans j.isLt hi⟩ (mixedLog hm p L c g)

theorem mixedLog_bound {m n q : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (L : Layout n q U) (c : ℕ) (g : ConnectedColorings m U c) :
    (mixedLog hm p L c g).length ≤ D := by
  induction p with
  | nil => simp [mixedLog]
  | complete p r i hr hi ih => exact ih
  | insert p u v i hu hv hi ih => exact ih
  | delete p u v i hu hv hi hvrt ih =>
    exact (changedAt_bound _ _ _).trans (Nat.add_le_add_right ih 1)

end KroneckerMixedChangeLog
end

/- Original module: KroneckerMixedRetention -/
section
/-! Compose complete-run and vertical palette invariants in arbitrary mixed order. -/
set_option autoImplicit false
namespace KroneckerMixedRetention
open KroneckerColoring KroneckerInputRecovery KroneckerWordCounts KroneckerWordRecoveryFiber
open KroneckerMixedPrograms KroneckerMixedExecution KroneckerMixedLayouts KroneckerMixedChangeLog
open KroneckerTaggedLayout KroneckerTaggedInsertion KroneckerTaggedDeletion KroneckerCompleteRunRetention
open KroneckerVerticalInsertionMap KroneckerVerticalDeletionMap KroneckerDeletionChoice KroneckerCompleteRunMap

set_option backward.isDefEq.respectTransparency false in
theorem mixed_retains {m n q : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (source : Input m n q) (L : Layout n q U) (c : ℕ)
    (g : ConnectedColorings m U c) (hinit : Retains source [] L g.val) :
    Retains source (mixedLog hm p L c g) (mixedLayout p L) (runMixed hm p c g).2.val := by
  induction p with
  | nil => exact hinit
  | complete p r i hr hi ih =>
    simpa only [mixedLog,mixedLayout,runMixed,completeRun] using
      completeColoring_retains source (mixedLog hm p L c g) (mixedLayout p L)
        (runMixed hm p c g).2.val ih r i (by omega)
  | insert p u v i hu hv hi ih =>
    simpa only [mixedLog,mixedLayout,runMixed,verticalInsertion] using
      insertion_retains source (mixedLog hm p L c g) (mixedLayout p L)
        (runMixed hm p c g).2.val ih u v i (by omega) (by omega) (by omega) hv.1
  | @delete V K A D p u v i hu hv hi hvrt ih =>
    let old := runMixed hm p c g
    let j := chosenIndex u v old.1 (by omega) (by omega) (by omega) hv.1 V i hi hvrt old.2
    have hj : V[j.val]=true := (chosenIndex_spec u v old.1 (by omega) (by omega) (by omega)
      hv.1 V i hi hvrt old.2).1
    simpa only [mixedLog,mixedLayout,runMixed,verticalDeletion] using
      deletion_retains source (mixedLog hm p L c g) (mixedLayout p L) old.2.val ih
        u v i (by omega) (by omega) (by omega) hv.1 hi hvrt j hj

theorem original_mixed_retains {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) :
    Retains (connectedSource m U c g) (mixedLog hm p (initialLayout U) c g)
      (mixedLayout p (initialLayout U)) (runMixed hm p c g).2.val :=
  mixed_retains hm p _ (initialLayout U) c g (initialLayout_retains U g.val)

theorem original_mixed_deleted_bound {m : ℕ} {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) : (mixedLayout p (initialLayout U)).deleted.length ≤ D := by
  have h := mixedLayout_deleted_bound p (initialLayout U)
  simpa only [initialLayout,List.length_nil,Nat.zero_add] using h

end KroneckerMixedRetention
end

/- Original module: KroneckerMixedRecovery -/
section
/-! A concrete compressed RecoverySpec for the constructed mixed K/A/D map, with no structural premise. -/
set_option autoImplicit false
namespace KroneckerMixedRecovery
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerInputRecovery
open KroneckerMixedPrograms KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerRecoverySpecification
open KroneckerMixedExecution KroneckerMixedLayouts KroneckerMixedChangeLog KroneckerMixedRetention

noncomputable def mixedSpec {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) :
    RecoverySpec m (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) D
      (connectedSource m U c) (runMixed hm p c) :=
  taggedSpec (connectedSource m U c) (runMixed hm p c)
    (fun b : SurplusColorings m V => b.2.val) (mixedLayout p (initialLayout U))
    (mixedLog hm p (initialLayout U) c) (mixedLog_bound hm p (initialLayout U) c)
    (original_mixed_deleted_bound p) (original_mixed_retains hm p c)

theorem mixed_recover {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (g : ConnectedColorings m U c) :
    decodeInput (mixedSpec hm p c).deleted (mixedSpec hm p c).deleted_card
      ((mixedSpec hm p c).retained (runMixed hm p c g))
      (code (mixedSpec hm p c) g)=connectedSource m U c g :=
  recover_source (mixedSpec hm p c) g

end KroneckerMixedRecovery
end

/- Original module: KroneckerMixedFiber -/
section
/-! The full program uses one compressed code, including repeated changes and edits to inserted edges. -/
set_option autoImplicit false
namespace KroneckerMixedFiber
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerFiberBudget
open KroneckerMixedPrograms KroneckerMixedExecution KroneckerMixedRecovery
open KroneckerRecoverySpecification KroneckerReconstructionFiber

theorem mixed_code_injective {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) :
    Function.Injective (fun g : ConnectedColorings m U c =>
      (runMixed hm p c g,code (mixedSpec hm p c) g)) :=
  target_code_injective (mixedSpec hm p c) (connectedSource_injective m U c)

theorem mixed_fiber_bound {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (c : ℕ) (b : SurplusColorings m V) :
    Nat.card {g // runMixed hm p c g=b} ≤ fiberBudget m (U.count true) D := by
  classical
  simpa only [positions_card] using
    reconstruction_fiber_bound (mixedSpec hm p c) (connectedSource_injective m U c) b

end KroneckerMixedFiber
end

/- Original module: KroneckerZeroMixed -/
section
/-! Drain the surplus of an actual mixed K/A/D edit program on a fixed prescribed target path. -/
set_option autoImplicit false
namespace KroneckerZeroMixed
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerMixedPrograms KroneckerMixedExecution KroneckerMixedSurplus
open KroneckerCollarColoring KroneckerCollarConnected KroneckerCollarRecovery

noncomputable def zeroMixed {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) : ConnectedColorings m (collarPath pairs V) 0 := by
  let r := runMixed hm p 0 g
  have hr := (runMixed_surplus hm p 0 g).2
  have hz : r.1-pairs.length=0 := by dsimp [r]; omega
  refine ⟨collarColoring (by omega) pairs hp r.1 V r.2.val,?_⟩
  simpa only [hz] using collarColoring_connected (by omega) pairs hp r.1 V r.2.val r.2.property

theorem zeroMixed_recover {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    recoverCollar pairs V (zeroMixed hm p pairs hp hsize g).val=(runMixed hm p 0 g).2.val :=
  recover_collarColoring (by omega) pairs hp _ V _

end KroneckerZeroMixed
end

/- Original module: KroneckerZeroMixedRecovery -/
section
/-! A proved compressed decoder for the actual zero-surplus program map. -/
set_option autoImplicit false
namespace KroneckerZeroMixedRecovery
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber KroneckerInputRecovery
open KroneckerMixedPrograms KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerRecoverySpecification
open KroneckerMixedExecution KroneckerMixedLayouts KroneckerMixedChangeLog KroneckerMixedRetention
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerZeroMixed

noncomputable def zeroMixedSpec {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (zeroMixed hm p pairs hp hsize) :=
  taggedSpec (connectedSource m U 0) (zeroMixed hm p pairs hp hsize) Subtype.val
    (collarLayout pairs (mixedLayout p (initialLayout U)))
    (mixedLog hm p (initialLayout U) 0) (mixedLog_bound hm p (initialLayout U) 0)
    (by rw [collarLayout_deleted]; exact original_mixed_deleted_bound p)
    (fun g => collar_retains (by omega) (connectedSource m U 0 g) _ _ _
      (original_mixed_retains hm p 0 g) pairs hp (runMixed hm p 0 g).1)

theorem zeroMixed_decode {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (zeroMixedSpec hm p pairs hp hsize).deleted (zeroMixedSpec hm p pairs hp hsize).deleted_card
      ((zeroMixedSpec hm p pairs hp hsize).retained (zeroMixed hm p pairs hp hsize g))
      (code (zeroMixedSpec hm p pairs hp hsize) g)=connectedSource m U 0 g :=
  recover_source (zeroMixedSpec hm p pairs hp hsize) g

end KroneckerZeroMixedRecovery
end

/- Original module: KroneckerZeroMixedCount -/
section
/-! The actual multi-vertical-edit comparison with one B_m(n,D) factor and a single surplus-zero target. -/
set_option autoImplicit false
namespace KroneckerZeroMixedCount
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerMixedPrograms KroneckerCollarColoring KroneckerZeroMixed
open KroneckerZeroMixedRecovery KroneckerWordRecoveryCount KroneckerWordRecoveryFiber KroneckerFiberBudget

theorem zero_mixed_count {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 :=
  word_recovery_count_bound (zeroMixedSpec hm p pairs hp hsize)

theorem zero_mixed_real {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤ (pathCount m (collarPath pairs V) 0 : ℝ) :=
  word_recovery_real_bound (zeroMixedSpec hm p pairs hp hsize)

theorem zero_mixed_fiber {m : ℕ} (hm : 4 ≤ m) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m U V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hsize : K+m*D ≤ pairs.length)
    (b : ConnectedColorings m (collarPath pairs V) 0) :
    Nat.card {g // zeroMixed hm p pairs hp hsize g=b} ≤ fiberBudget m (U.count true) D :=
  word_recovery_fiber_bound (zeroMixedSpec hm p pairs hp hsize) b

end KroneckerZeroMixedCount
end

/- Original module: KroneckerPreparedMixedRecovery -/
section
/-! Preparation may add unlabelled edges without enlarging the original recovery alphabet. -/
set_option autoImplicit false
namespace KroneckerPreparedMixedRecovery
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerWordRecoveryFiber KroneckerOrientationPositions
open KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerMixedPrograms
open KroneckerMixedLayouts KroneckerMixedChangeLog KroneckerMixedRetention KroneckerMixedExecution
open KroneckerTaggedCollars KroneckerCollarPaletteRetention KroneckerCollarColoring KroneckerZeroMixed
open KroneckerInputRecovery KroneckerRecoverySpecification

noncomputable def preparedMixedSpec {m : ℕ} (hm : 4 ≤ m) {U W V : List Bool} {K A D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : MixedProgram m W V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length) :
    WordRecoverySpec (D:=D) U (collarPath pairs V) 0 0 (fun g => zeroMixed hm p pairs hp hs (prep g)) :=
  taggedSpec (connectedSource m U 0) (fun g => zeroMixed hm p pairs hp hs (prep g)) Subtype.val
    (collarLayout pairs (mixedLayout p L)) (fun g => mixedLog hm p L 0 (prep g))
    (fun g => mixedLog_bound hm p L 0 (prep g))
    (by rw [collarLayout_deleted]; have h := mixedLayout_deleted_bound p L; omega)
    (fun g => collar_retains (by omega) _ _ _ _ (mixed_retains hm p _ L 0 (prep g) (hk g))
      pairs hp (runMixed hm p 0 (prep g)).1)

theorem preparedMixed_decode {m : ℕ} (hm : 4 ≤ m) {U W V : List Bool} {K A D : ℕ}
    (prep : ConnectedColorings m U 0 → ConnectedColorings m W 0)
    (L : Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) W)
    (hd : L.deleted.length=0) (hk : ∀ g, Retains (connectedSource m U 0 g) [] L (prep g).val)
    (p : MixedProgram m W V K A D) (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length)
    (g : ConnectedColorings m U 0) :
    decodeInput (preparedMixedSpec hm prep L hd hk p pairs hp hs).deleted
      (preparedMixedSpec hm prep L hd hk p pairs hp hs).deleted_card
      ((preparedMixedSpec hm prep L hd hk p pairs hp hs).retained (zeroMixed hm p pairs hp hs (prep g)))
      (code (preparedMixedSpec hm prep L hd hk p pairs hp hs) g)=connectedSource m U 0 g :=
  recover_source (preparedMixedSpec hm prep L hd hk p pairs hp hs) g

end KroneckerPreparedMixedRecovery
end

/- Original module: KroneckerBufferedMixedCount -/
section
/-! Two initial buffers cost no additional original horizontal positions in B_m(n,D). -/
set_option autoImplicit false
namespace KroneckerBufferedMixedCount
open KroneckerProgramExecution
open KroneckerWordCounts KroneckerColoredShell KroneckerWrappedTags KroneckerTaggedLayout
open KroneckerMixedPrograms KroneckerCollarColoring KroneckerPreparedMixedRecovery
open KroneckerWordRecoveryCount KroneckerFiberBudget

theorem buffered_mixed_count {m u v : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m (shellPath u v U) V K A D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs V) 0 := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_count_bound (preparedMixedSpec hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)

theorem buffered_mixed_real {m u v : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {K A D : ℕ}
    (p : MixedProgram m (shellPath u v U) V K A D)
    (pairs : List (ℕ×ℕ)) (hp : LegalPairs m pairs) (hs : K+m*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤
      (pathCount m (collarPath pairs V) 0 : ℝ) := by
  let prep := unaryShell u v 0 (by omega : 3 ≤ m) (by omega) (by omega) U
  let L := wrapLayout u v (initialLayout U)
  exact word_recovery_real_bound (preparedMixedSpec hm prep L rfl
    (fun g => shellColoring_retains _ [] _ g.val (initialLayout_retains U g.val)
      u v (by omega) (by omega) (by omega) hv.1) p pairs hp hs)

end KroneckerBufferedMixedCount
end

/- Original module: KroneckerRawMixedPrograms -/
section
/-! Color-independent raw middle edit lists, with complete runs and vertical edits in arbitrary order. -/
set_option autoImplicit false
namespace KroneckerRawMixedPrograms
open KroneckerListInsertion KroneckerListDeletion KroneckerCompleteRunPalette

inductive RawProgram (m : ℕ) (U : List Bool) : List Bool → ℕ → ℕ → ℕ → Type
  | nil : RawProgram m U U 0 0 0
  | complete {V : List Bool} {K A D : ℕ} (p : RawProgram m U V K A D) (r i : ℕ)
      (hr : 1 ≤ r ∧ r ≤ m-2) (hi : i ≤ V.length) : RawProgram m U (completePath r i V) (K+1) A D
  | insert {V : List Bool} {K A D : ℕ} (p : RawProgram m U V K A D) (i : ℕ) (hi : i ≤ V.length) :
      RawProgram m U (insertAt i false V) K (A+1) D
  | delete {V : List Bool} {K A D : ℕ} (p : RawProgram m U V K A D) (i : ℕ)
      (hi : i < V.length) (hv : V[i]=false) : RawProgram m U (removeAt i V) K A (D+1)

def steps {m : ℕ} {U V : List Bool} {K A D : ℕ} : RawProgram m U V K A D → ℕ
  | .nil => 0
  | .complete p _ _ _ _ => steps p+1
  | .insert p _ _ => steps p+1
  | .delete p _ _ _ => steps p+1

theorem raw_steps {m : ℕ} {U V : List Bool} {K A D : ℕ} (p : RawProgram m U V K A D) :
    steps p=K+A+D := by
  induction p with
  | nil => rfl
  | complete p r i hr hi ih => simp only [steps,ih]; omega
  | insert p i hi ih => simp only [steps,ih]; omega
  | delete p i hi hv ih => simp only [steps,ih]; omega

end KroneckerRawMixedPrograms
end
