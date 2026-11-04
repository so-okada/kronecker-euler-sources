import KroneckerGeometricExchange
import KroneckerVerticalInsertionRuns
import KroneckerRunDeletionPosition
import KroneckerScaffoldCounts
import KroneckerGeometricCounts

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace KroneckerPaperPathGradings
open KroneckerPaperPaths KroneckerInsertionPalette KroneckerDeletionColoring

theorem operational_inverse_palette (m : ℕ) (P : TNEPath) (c : ℕ)
    (d : KroneckerWordCounts.ConnectedColorings m P.steps c) :
    paletteEncoding ((operationalConnectedEquiv m P c).symm d).val = d.val := by
  exact congrArg Subtype.val ((operationalConnectedEquiv m P c).apply_symm_apply d)

def wrappedInsertion (m u v i c : ℕ) (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m - 2) (hv : 1 ≤ v ∧ v ≤ m - 2)
    (P : TNEPath) (hi : 1 ≤ i ∧ i ≤ P.steps.length) :
    ConnectedColorings m P c →
      ConnectedColorings m (ofSteps (insertedPath u v i P.steps) 0) c :=
  fun d => (operationalConnectedEquiv m _ c).symm
    (KroneckerVerticalInsertionMap.verticalInsertion u v i c hm hu hv P.steps hi
      (operationalConnectedEquiv m P c d))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem wrappedInsertion_palette (m u v i c : ℕ) (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m - 2) (hv : 1 ≤ v ∧ v ≤ m - 2)
    (P : TNEPath) (hi : 1 ≤ i ∧ i ≤ P.steps.length) (d : ConnectedColorings m P c) :
    List.ofFn (paletteEncoding (wrappedInsertion m u v i c hm hu hv P hi d).val) =
      insertedColors u v i (by omega) (by omega) (by omega)
        (List.ofFn (paletteEncoding d.val)) := by
  rw [wrappedInsertion, operational_inverse_palette]
  simp only [KroneckerVerticalInsertionMap.verticalInsertion, insertionColoring,
    KroneckerColoredShell.fromList_colors, operationalConnectedEquiv_colors]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem wrappedInsertion_injective (m u v i c : ℕ) (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m - 2) (hv : 1 ≤ v ∧ v ≤ m - 2)
    (P : TNEPath) (hi : 1 ≤ i ∧ i ≤ P.steps.length) :
    Function.Injective (wrappedInsertion m u v i c hm hu hv P hi) := by
  intro d e h
  apply (operationalConnectedEquiv m P c).injective
  apply Subtype.ext
  apply KroneckerInsertionColorRecovery.insertionColoring_injective
    u v i (by omega) (by omega) (by omega) hv.1 P.steps hi.2
  have he := congrArg (fun d => paletteEncoding d.val) h
  simpa only [wrappedInsertion, operational_inverse_palette,
    KroneckerVerticalInsertionMap.verticalInsertion] using he

theorem wrappedInsertion_target (u v i : ℕ) (hu : 0 < u) (hv : 0 < v) (P : TNEPath) :
    ofSteps (insertedPath u v i P.steps) 0 =
      concat (simpleRun u hu) (concat (insert P i (ofSteps [false] 0)) (simpleRun v hv)) := by
  apply TNEPath.ext
  · simp [insertedPath, KroneckerStack.runShape, KroneckerListInsertion.insertAt,
      List.append_assoc]
  · simp [concat, ofSteps, simpleRun, insertedPath, KroneckerStack.runShape]

theorem geometric_deletion_exists (m u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m - 1) (hv : 1 ≤ v ∧ v ≤ m - 1)
    (P : TNEPath) (k : Edge P) (hk : P.steps.get k = false)
    (d : ConnectedColorings m P c) :
    ∃ j : Fin k.val, P.steps[j.val]'(lt_trans j.isLt k.isLt) = true ∧
      0 < (d.val.1 (edgeEquiv P ⟨j.val, lt_trans j.isLt k.isLt⟩)).val ∧
      ∃ e : ConnectedColorings m (ofSteps (deletionPath u v P.steps k.val) 0)
        (c + (d.val.1 (edgeEquiv P k)).val),
        paletteEncoding e.val = deletionColoring u v (by omega) (by omega)
          (by omega) hv.1 P.steps k.val k.isLt j (paletteEncoding d.val) := by
  have hu' : u+1 ≤ m := by omega
  have hv' : v-1 ≤ m := by omega
  have hm' : 2 ≤ m := by omega
  have hd : KroneckerStack.Connected m
      (KroneckerWordCounts.pathWord P.steps (paletteEncoding d.val)) c :=
    (operationalConnectedEquiv m P c d).property
  obtain ⟨j,hj,hp,he⟩ := KroneckerDeletionColorExists.deletion_color_exists
    u v c hu' hv' hm' hv.1 P.steps k.val k.isLt
    (by simpa only [List.get_eq_getElem] using hk) (paletteEncoding d.val) hd
  have hgrade : KroneckerColoring.grade (paletteEncoding d.val k) =
      (d.val.1 (edgeEquiv P k)).val := rfl
  rw [hgrade] at he
  let b := deletionColoring u v hu' hv' hm' hv.1 P.steps k.val k.isLt j (paletteEncoding d.val)
  let e : KroneckerWordCounts.ConnectedColorings m
      (deletionPath u v P.steps k.val) (c + (d.val.1 (edgeEquiv P k)).val) := ⟨b,he⟩
  refine ⟨j,hj,?_,(operationalConnectedEquiv m
    (ofSteps (deletionPath u v P.steps k.val) 0) _).symm e,?_⟩
  · exact hp
  · exact operational_inverse_palette m (ofSteps (deletionPath u v P.steps k.val) 0) _ e

theorem geometric_deletion_target (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (P : TNEPath) (k : Edge P) (hk : P.steps.get k = false) :
    ofSteps (deletionPath u v P.steps k.val) 0 =
      concat (simpleRun u hu) (concat (deleteVertical P k hk) (simpleRun v hv)) := by
  apply TNEPath.ext
  · simp [deletionPath, KroneckerColoredShell.shellPath, KroneckerListDeletion.removeAt,
      KroneckerStack.runShape, List.append_assoc]
  · simp [concat, ofSteps, simpleRun, deletionPath, KroneckerColoredShell.shellPath,
      KroneckerStack.runShape]

theorem geometric_separated_count (m : ℕ) (hm : 3 ≤ m)
    {w : List KroneckerHoleGrammar.Piece} {n : ℕ} (hw : KroneckerHoleChains.Chain w n)
    (a b c d e f : ℕ) (o : LatticePoint)
    (hl : KroneckerHoleGrammar.Legal m (.guard a :: .guard b :: .guard c :: w ++
      [.guard d, .guard e, .guard f])) :
    ((KroneckerHoleChains.holes w).map (fun X => connectedCount m (runPath X 0) 0)).prod ≤
      connectedCount m (runPath (a :: b :: c :: KroneckerHoleGrammar.expand w ++ [d,e,f]) o) 0 := by
  simpa only [connectedCount_runPath] using
    KroneckerScaffoldCounts.scaffold_product_bound m hm hw a b c d e f hl

end KroneckerPaperPathGradings

#print axioms KroneckerPaperPathGradings.wrappedInsertion_injective
#print axioms KroneckerPaperPathGradings.geometric_deletion_exists
#print axioms KroneckerPaperPathGradings.geometric_separated_count
