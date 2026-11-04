import KroneckerManuscriptRecolorMaps
import KroneckerCompleteRunInjection
import KroneckerNaturalNodes

/-! Explicit applications of Recol to the prescribed target gradings.
The palette equivalence supplies the manuscript's one-based source colors. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerRecolorConstructions
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerColoring KroneckerColoredShell KroneckerInsertionPalette
open KroneckerDeletionColoring KroneckerCompleteRunPalette

/-- Equation (3.3), with the unary preserving shell grading. -/
def shell {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u + 1 ≤ m)
    (hv : v - 1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (c : Coloring m U.steps.length) : ColoredGrading m (ofSteps (shellPath u v U.steps) 0) :=
  let d := fromPalette _ (shellColoring u v hu hv hm hpos U.steps c)
  let b := fromPalette U c
  ⟨d.1, Recol U _ (edgeCopy (shellIndices U u v)) d.1 (color_grade_le d.2) b.1 b.2⟩

/-- Lemma 4.4(3): recoloring uses the original path as its source. -/
def insertion {m : ℕ} (U : TNEPath) (u v i : ℕ) (hu : u + 2 ≤ m)
    (hv : v - 1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (c : Coloring m U.steps.length) : ColoredGrading m (ofSteps (insertedPath u v i U.steps) 0) :=
  let d := fromPalette _ (insertionColoring u v i hu hv hm hpos U.steps c)
  let b := fromPalette U c
  ⟨d.1, Recol U _ (edgeCopy (insertionIndices U u v i)) d.1 (color_grade_le d.2) b.1 b.2⟩

/-- Lemma 4.6(3), for a specified earlier horizontal index j. -/
def deletion {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u + 1 ≤ m)
    (hv : v - 1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (r : Edge U) (j : Fin r.val)
    (c : Coloring m U.steps.length) : ColoredGrading m (ofSteps (deletionPath u v U.steps r.val) 0) :=
  let d := fromPalette _ (deletionColoring u v hu hv hm hpos U.steps r.val r.isLt j c)
  let b := fromPalette U c
  ⟨d.1, Recol U _ (partialEdgeCopy (deletionIndices U u v r)) d.1 (color_grade_le d.2) b.1 b.2⟩

/-- Lemma 4.7: insertion of a simple run. -/
def complete {m : ℕ} (U : TNEPath) (i j : ℕ) (hi : i ≤ U.steps.length)
    (hj : 0 < j) (hm : j ≤ m) (c : Coloring m U.steps.length) :
    ColoredGrading m (insert U i (simpleRun j hj)) :=
  let d := fromPalette (insert U i (simpleRun j hj)) (completeColoring j i hm U.steps c)
  let b := fromPalette U c
  ⟨d.1, Recol U _ (edgeCopy (completeIndices U i j hi hj)) d.1 (color_grade_le d.2) b.1 b.2⟩

theorem shell_grade {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u + 1 ≤ m)
    (hv : v - 1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (c : Coloring m U.steps.length) :
    (shell U u v hu hv hm hpos c).1 =
      (fromPalette _ (shellColoring u v hu hv hm hpos U.steps c)).1 := rfl

theorem insertion_grade {m : ℕ} (U : TNEPath) (u v i : ℕ) (hu : u + 2 ≤ m)
    (hv : v - 1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (c : Coloring m U.steps.length) :
    (insertion U u v i hu hv hm hpos c).1 =
      (fromPalette _ (insertionColoring u v i hu hv hm hpos U.steps c)).1 := rfl

theorem deletion_grade {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u + 1 ≤ m)
    (hv : v - 1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (r : Edge U) (j : Fin r.val)
    (c : Coloring m U.steps.length) :
    (deletion U u v hu hv hm hpos r j c).1 =
      (fromPalette _ (deletionColoring u v hu hv hm hpos U.steps r.val r.isLt j c)).1 := rfl

theorem complete_grade {m : ℕ} (U : TNEPath) (i j : ℕ) (hi : i ≤ U.steps.length)
    (hj : 0 < j) (hm : j ≤ m) (c : Coloring m U.steps.length) :
    (complete U i j hi hj hm c).1 =
      (fromPalette (insert U i (simpleRun j hj)) (completeColoring j i hm U.steps c)).1 := rfl

theorem fromPalette_connected {m d : ℕ} (U : TNEPath)
    (c : Coloring m U.steps.length)
    (hc : KroneckerStack.Connected m (KroneckerWordCounts.pathWord U.steps c) d) :
    ConnectedGrading (fromPalette U c).1 ∧ Surp U (fromPalette U c).1 = (d : ℤ) := by
  let b := (KroneckerPaperPathGradings.operationalConnectedEquiv m U d).symm ⟨c, hc⟩
  exact ((connectedColoringEquiv m U d).symm b).property

/-- Lemma 4.4(1): the explicit Recol construction has the checked insertion grading. -/
theorem insertion_connected {m d : ℕ} (U : TNEPath) (u v i : ℕ) (hu : u + 2 ≤ m)
    (hv : v - 1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (hi : 1 ≤ i ∧ i ≤ U.steps.length)
    (c : Coloring m U.steps.length)
    (hc : KroneckerStack.Connected m (KroneckerWordCounts.pathWord U.steps c) d) :
    ConnectedGrading (insertion U u v i hu hv hm hpos c).1 ∧
      Surp _ (insertion U u v i hu hv hm hpos c).1 = (d : ℤ) :=
  fromPalette_connected _ _
    (KroneckerInsertionColorConnected.insertionColoring_connected u v i d hu hv hm hpos U.steps hi c hc)

open KroneckerPaperPathGradings (Horizontal Vertical edgeIndex)

theorem precursor_index {m : ℕ} (U : TNEPath) (c : Coloring m U.steps.length)
    (p : Vertical U → Horizontal U) (hp : IsHPrecursor (fromPalette U c).1 p)
    (r : Vertical U) :
    edgeIndex (p r).val < edgeIndex r.val ∧ 0 < (fromPalette U c).1 (p r).val := by
  have h := ((KroneckerPaperPathGradings.isHPrecursor_iff
    (bounded (fromPalette U c).1) p).mp hp) r
  exact ⟨h.1, Nat.lt_of_le_of_lt (Nat.zero_le _) h.2.1⟩

/-- The precursor-based construction used in the manuscript proof of Lemma 4.6.
The compressed-index precursor identity is proved in KroneckerPrecursorDeletion.
The connectedness proof attached to deletion_exists is existential. -/
def deletionAtPrecursor {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u + 1 ≤ m)
    (hv : v - 1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (c : Coloring m U.steps.length) (p : Vertical U → Horizontal U)
    (hp : IsHPrecursor (fromPalette U c).1 p) (r : Vertical U) :
    ColoredGrading m (ofSteps (deletionPath u v U.steps (edgeIndex r.val)) 0) :=
  deletion U u v hu hv hm hpos ((edgeEquiv U).symm r.val)
    ⟨edgeIndex (p r).val, (precursor_index U c p hp r).1⟩ c

end KroneckerRecolorConstructions
