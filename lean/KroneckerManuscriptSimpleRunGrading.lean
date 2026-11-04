import KroneckerRecolorConstructions
import KroneckerRecolOperations
import KroneckerOneRun

/-! The fixed simple-run grading and color one on every edge.
The same palette is used by the one-run bound and the insertion map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptSimpleRunGrading
open KroneckerPaperPaths KroneckerNaturalPathGradings
open KroneckerManuscriptRecolorMaps KroneckerColoring KroneckerColoredShell
open KroneckerOneRun KroneckerCompleteRunPalette

def grading (j : ℕ) (hj : 0 < j) : Grading (simpleRun j hj) :=
  fun e => if ((edgeEquiv _).symm e).val = 0 then j else 0

def colors (m j : ℕ) (hj : 0 < j) (hm : j ≤ m) : ColorFiber m (grading j hj) :=
  fun e => ⟨1,le_rfl,Nat.choose_pos (by unfold grading; split <;> omega)⟩

def palette (m j : ℕ) (hm : j ≤ m) : Coloring m (KroneckerStack.runShape j).length :=
  baseColoring m j hm ⟨0,Nat.choose_pos hm⟩

def colored (m j : ℕ) (hj : 0 < j) (hm : j ≤ m) : ColoredGrading m (simpleRun j hj) :=
  fromPalette (simpleRun j hj) (palette m j hm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem grade_at (m j : ℕ) (hj : 0 < j) (hm : j ≤ m) (k : Edge (simpleRun j hj)) :
    (colored m j hj hm).1 (edgeEquiv _ k) = if k.val=0 then j else 0 := by
  rw [colored,fromPalette_grade]
  by_cases hk : k.val=0 <;>
    simp [palette,baseColoring,baseColors,fromList,List.getElem_cons,hk,runColor,zeroColor,grade]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem color_at (m j : ℕ) (hj : 0 < j) (hm : j ≤ m) (k : Edge (simpleRun j hj)) :
    ((colored m j hj hm).2 (edgeEquiv _ k)).val = 1 := by
  rw [colored,fromPalette_color]
  have hmem : palette m j hm k ∈ childColors m j hm := by
    change (childColors m j hm)[k.val]'(by simpa [childColors] using k.isLt) ∈ childColors m j hm
    exact List.getElem_mem _
  have hz := KroneckerRecolOperations.child_zero hm _ hmem
  simp only [hz,zero_add]

theorem colored_grade (m j : ℕ) (hj : 0 < j) (hm : j ≤ m) :
    (colored m j hj hm).1 = grading j hj := by
  funext e
  obtain ⟨k,rfl⟩ := (edgeEquiv _).surjective e
  rw [grade_at]
  simp [grading]

theorem colored_connected (m j : ℕ) (hj : 0 < j) (hm : j ≤ m) :
    ConnectedGrading (grading j hj) ∧ Surp (simpleRun j hj) (grading j hj) = 0 := by
  have h := KroneckerRecolorConstructions.fromPalette_connected (simpleRun j hj) (palette m j hm)
    (baseColoring_connected (by omega : 1 ≤ j) hm ⟨0,Nat.choose_pos hm⟩)
  change ConnectedGrading (colored m j hj hm).1 ∧ Surp (simpleRun j hj) (colored m j hj hm).1 = 0 at h
  simpa only [colored_grade] using h

theorem palette_entries (m j : ℕ) (hm : j ≤ m) :
    List.ofFn (palette m j hm) = childColors m j hm := by
  rw [palette,baseColoring,fromList_colors]
  rfl

theorem insertion_uses_fixed_run {m : ℕ} (j i : ℕ) (hm : j ≤ m) (cs : List (Palette m)) :
    completeColors j i hm cs = KroneckerListSplice.splice i (List.ofFn (palette m j hm)) cs := by
  rw [palette_entries]
  rfl

theorem insertion_model {m : ℕ} (U : TNEPath) (i j : ℕ) (hi : i ≤ U.steps.length)
    (hj : 0 < j) (hm : j ≤ m) (c : Coloring m U.steps.length) :
    KroneckerRecolorConstructions.complete U i j hi hj hm c =
      fromPalette (insert U i (simpleRun j hj)) (completeColoring j i hm U.steps c) :=
  KroneckerRecolOperations.complete_eq U i j hi hj hm c

end KroneckerManuscriptSimpleRunGrading

#print axioms KroneckerManuscriptSimpleRunGrading.grading
#print axioms KroneckerManuscriptSimpleRunGrading.colors
#print axioms KroneckerManuscriptSimpleRunGrading.palette
#print axioms KroneckerManuscriptSimpleRunGrading.colored
#print axioms KroneckerManuscriptSimpleRunGrading.grade_at
#print axioms KroneckerManuscriptSimpleRunGrading.color_at
#print axioms KroneckerManuscriptSimpleRunGrading.colored_grade
#print axioms KroneckerManuscriptSimpleRunGrading.colored_connected
#print axioms KroneckerManuscriptSimpleRunGrading.palette_entries
#print axioms KroneckerManuscriptSimpleRunGrading.insertion_uses_fixed_run
#print axioms KroneckerManuscriptSimpleRunGrading.insertion_model
