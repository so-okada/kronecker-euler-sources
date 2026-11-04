import KroneckerRecolShell

set_option autoImplicit false
noncomputable section
namespace KroneckerRecolConcatenation
open KroneckerColoring KroneckerColoredShell KroneckerWordCounts
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerExplicitShellCorrespondence KroneckerRecolShell

def paletteEquiv (m : ℕ) (X : TNEPath) : Coloring m X.steps.length ≃ ColoredGrading m X :=
  (KroneckerPaperColors.coloringEquiv m X.steps.length).trans
    (((KroneckerPaperPathGradings.coloredGradingEquiv m X).symm).trans
      (coloredGradingEquiv m X).symm)

theorem paletteEquiv_apply (m : ℕ) (X : TNEPath) (c : Coloring m X.steps.length) :
    paletteEquiv m X c = fromPalette X c := rfl

theorem fromPalette_surjective (m : ℕ) (X : TNEPath) : Function.Surjective (@fromPalette m X) :=
  (paletteEquiv m X).surjective

abbrev Factor (m : ℕ) := (U : List Bool) × Coloring m U.length

def colors {m : ℕ} (xs : List (Factor m)) : List (Palette m) :=
  xs.flatMap (fun p => List.ofFn p.2)

def steps {m : ℕ} (xs : List (Factor m)) : List Bool := xs.flatMap Sigma.fst

theorem colors_length {m : ℕ} (xs : List (Factor m)) : (colors xs).length = (steps xs).length := by
  induction xs with
  | nil => rfl
  | cons p xs ih => simpa [colors, steps] using ih

def concatenate {m : ℕ} (xs : List (Factor m)) : Coloring m (steps xs).length :=
  fromList (colors xs) (colors_length xs)

theorem concatenate_word {m : ℕ} (xs : List (Factor m)) :
    pathWord (steps xs) (concatenate xs) = xs.flatMap (fun p => pathWord p.1 p.2) := by
  rw [concatenate, fromList_word]
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [steps, colors, List.flatMap_cons] at *
    rw [List.zipWith_append (by simp), ih, ← word_zip]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The concatenated grading used in Definition 3.1 has the concatenated graded word. -/
theorem concatenated_grading_word {m : ℕ} (xs : List (Factor m)) :
    gradedWord (ofSteps (steps xs) 0) (fromPalette _ (concatenate xs)).1 =
      xs.flatMap (fun p => gradedWord (ofSteps p.1 0) (fromPalette _ p.2).1) := by
  simp only [gradedWord_fromPalette, ofSteps_steps, concatenate_word]

/-- Definition 3.1 followed by Recol agrees with the binary counted palette map. -/
theorem binary_palette {m : ℕ} (U V : List Bool) (c : Coloring m U.length)
    (d : Coloring m V.length) (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) :
    List.ofFn (shellPalette (ofSteps (steps [⟨U,c⟩,⟨V,d⟩]) 0) u v 3 hu hv hm hpos
      (concatenate [⟨U,c⟩,⟨V,d⟩])) =
    List.ofFn (KroneckerBinaryShell.binaryColoring u v hu hv hm hpos U V c d) := by
  have hs : List.ofFn (shellPalette (ofSteps (steps [⟨U,c⟩,⟨V,d⟩]) 0) u v 3 hu hv hm hpos
      (concatenate [⟨U,c⟩,⟨V,d⟩])) =
      prefixColors m u hu ++ (List.ofFn (concatenate [⟨U,c⟩,⟨V,d⟩]) ++ tailColors m v 3 hv hm) :=
    fromList_colors _ _
  have hb : List.ofFn (KroneckerBinaryShell.binaryColoring u v hu hv hm hpos U V c d) =
      KroneckerBinaryShell.binaryColors u v hu hv hm (List.ofFn c) (List.ofFn d) :=
    fromList_colors _ _
  have hc : List.ofFn (concatenate [⟨U,c⟩,⟨V,d⟩]) = colors [⟨U,c⟩,⟨V,d⟩] :=
    fromList_colors _ _
  rw [hs, hb, hc]
  simp only [colors, List.flatMap_cons, List.flatMap_nil, List.append_nil, tailColors,
    KroneckerBinaryShell.binaryColors, KroneckerBinaryShell.suffixColors, List.append_assoc]

end KroneckerRecolConcatenation
