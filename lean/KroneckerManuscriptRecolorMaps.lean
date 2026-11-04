import KroneckerManuscriptRecolor
import KroneckerGeometricSurgery
import KroneckerPaletteRecolor

/-! Geometric copy maps for equations (3.3), (4.2), (4.10), and (4.16).
Fin indices are zero-based; manuscript edge indices are one-based. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerManuscriptRecolorMaps
open KroneckerPaperPaths KroneckerNaturalPathGradings

def edgeCopy {U V : TNEPath} (f : Edge U ↪ Edge V) :
    (Set.univ : Set (GeomEdge U)) ↪ GeomEdge V where
  toFun x := edgeEquiv V (f ((edgeEquiv U).symm x.val))
  inj' := by
    intro x y h
    apply Subtype.ext
    exact (edgeEquiv U).symm.injective (f.injective ((edgeEquiv V).injective h))

def partialEdgeCopy {U V : TNEPath} {S : Set (Edge U)} (f : S ↪ Edge V) :
    {e : GeomEdge U // (edgeEquiv U).symm e ∈ S} ↪ GeomEdge V where
  toFun x := edgeEquiv V (f ⟨(edgeEquiv U).symm x.val, x.property⟩)
  inj' := by
    intro x y h
    apply Subtype.ext
    apply (edgeEquiv U).symm.injective
    exact congrArg Subtype.val (f.injective ((edgeEquiv V).injective h))

def shellIndices (U : TNEPath) (u v : ℕ) :
    Edge U ↪ Edge (ofSteps (KroneckerColoredShell.shellPath u v U.steps) 0) where
  toFun k := ⟨u + 1 + k.val, by
    have := k.isLt
    simp only [ofSteps_steps, KroneckerColoredShell.shellPath, List.length_append,
      KroneckerStack.runShape, List.length_cons, List.length_replicate]
    omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

def insertionIndices (U : TNEPath) (u v i : ℕ) :
    Edge U ↪ Edge (ofSteps (KroneckerInsertionPalette.insertedPath u v i U.steps) 0) where
  toFun k := ⟨if k.val < i then u + 1 + k.val else u + 2 + k.val, by
    have := k.isLt
    simp only [ofSteps_steps, KroneckerInsertionPalette.insertedPath, List.length_append,
      KroneckerStack.runShape, List.length_cons, List.length_replicate,
      KroneckerListInsertion.insertAt_length]
    split <;> omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp at he
    split_ifs at he <;> omega

def completeIndices (U : TNEPath) (i j : ℕ) (hi : i ≤ U.steps.length) (hj : 0 < j) :
    Edge U ↪ Edge (insert U i (simpleRun j hj)) where
  toFun k := ⟨if k.val < i then k.val else k.val + j + 1, by
    have := k.isLt
    simp only [insert_steps, List.length_append, List.length_take, List.length_drop,
      simpleRun_steps, List.length_cons, List.length_replicate, Nat.min_eq_left hi]
    split <;> omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp at he
    split_ifs at he <;> omega

def deletionIndices (U : TNEPath) (u v : ℕ) (r : Edge U) :
    {k : Edge U // k ≠ r} ↪
      Edge (ofSteps (KroneckerDeletionColoring.deletionPath u v U.steps r.val) 0) where
  toFun k := ⟨if k.val.val < r.val then u + 1 + k.val.val else u + k.val.val, by
    have hk := k.val.isLt
    have hr := r.isLt
    have hn : k.val.val ≠ r.val := fun h => k.property (Fin.ext h)
    simp only [ofSteps_steps, KroneckerDeletionColoring.deletionPath,
      KroneckerColoredShell.shellPath, KroneckerListDeletion.removeAt, List.length_append,
      List.length_take, List.length_drop, KroneckerStack.runShape,
      List.length_cons, List.length_replicate, Nat.min_eq_left (Nat.le_of_lt hr)]
    split <;> omega⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    have ha : a.val.val ≠ r.val := fun h => a.property (Fin.ext h)
    have hb : b.val.val ≠ r.val := fun h => b.property (Fin.ext h)
    have he := congrArg Fin.val h
    dsimp at he
    split_ifs at he <;> omega

/-- A total copy map and unchanged source grades preserve every source color. -/
theorem copy_color {m : ℕ} {U V : TNEPath} (f : Edge U ↪ Edge V)
    (h : G V) (hh : h ∈ G_h V m) (g : G U) (γ : Col U g m)
    (k : Edge U) (hk : h (edgeEquiv V (f k)) = g (edgeEquiv U k)) :
    ((Recol U V (edgeCopy f) h hh g γ) (edgeEquiv V (f k))).val =
      (γ (edgeEquiv U k)).val := by
  have he : edgeCopy f ⟨edgeEquiv U k, Set.mem_univ _⟩ = edgeEquiv V (f k) := by
    change edgeEquiv V (f ((edgeEquiv U).symm (edgeEquiv U k))) = edgeEquiv V (f k)
    rw [Equiv.symm_apply_apply]
  exact (congrArg (fun e => ((Recol U V (edgeCopy f) h hh g γ) e).val) he.symm).trans
    (Recol_preserved (edgeCopy f) h hh g γ ⟨edgeEquiv U k, Set.mem_univ _⟩ (he ▸ hk))

/-- Conversion of the finite palette into the manuscript's geometric colored grading. -/
def fromPalette {m : ℕ} (U : TNEPath) (c : KroneckerColoring.Coloring m U.steps.length) :
    ColoredGrading m U :=
  (coloredGradingEquiv m U).symm
    ((KroneckerPaperPathGradings.coloredGradingEquiv m U).symm
      (KroneckerPaperColors.coloringEquiv m U.steps.length c))

@[simp] theorem fromPalette_grade {m : ℕ} (U : TNEPath)
    (c : KroneckerColoring.Coloring m U.steps.length) (k : Edge U) :
    (fromPalette U c).1 (edgeEquiv U k) = KroneckerColoring.grade (c k) := by
  change (c ((edgeEquiv U).symm (edgeEquiv U k))).1.val = (c k).1.val
  rw [Equiv.symm_apply_apply]

@[simp] theorem fromPalette_color {m : ℕ} (U : TNEPath)
    (c : KroneckerColoring.Coloring m U.steps.length) (k : Edge U) :
    ((fromPalette U c).2 (edgeEquiv U k)).val = (c k).2.val + 1 := by
  change (c ((edgeEquiv U).symm (edgeEquiv U k))).2.val + 1 = (c k).2.val + 1
  rw [Equiv.symm_apply_apply]

end KroneckerManuscriptRecolorMaps
