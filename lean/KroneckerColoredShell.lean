import KroneckerWordCounts

/-! An explicit colored unary shell with recovery of every interior color.
All newly introduced colors are fixed; no additional color factor is claimed.
-/
set_option autoImplicit false
namespace KroneckerColoredShell
open KroneckerStack KroneckerColoring KroneckerWordCounts

/-- Decode a palette list of the correct length without changing any entry. -/
def fromList {m : ℕ} {U : List Bool} (cs : List (Palette m))
    (h : cs.length = U.length) : Coloring m U.length :=
  fun i => cs[i.val]'(by omega)

theorem fromList_colors {m : ℕ} {U : List Bool} (cs : List (Palette m))
    (h : cs.length = U.length) : List.ofFn (fromList cs h) = cs := by
  apply List.ext_getElem
  · simpa using h.symm
  · intro i hi hj
    simp [fromList]

theorem fromList_word {m : ℕ} (U : List Bool) (cs : List (Palette m))
    (h : cs.length = U.length) :
    pathWord U (fromList cs h) = List.zipWith paint U cs := by
  apply List.ext_getElem
  · simp [pathWord_length, List.length_zipWith, h]
  · intro i hi hj
    have hiU : i < U.length := by simpa [pathWord_length] using hi
    simp [pathWord, word, fromList, pathShape, List.getD]

theorem word_zip {m : ℕ} (U : List Bool) (g : Coloring m U.length) :
    pathWord U g = List.zipWith paint U (List.ofFn g) := by
  have hg : fromList (List.ofFn g) (by simp) = g := by
    funext i
    simp [fromList]
  simpa [hg] using fromList_word U (List.ofFn g) (by simp)

/-- Choose color zero at a specified legal grade. -/
def fixedColor (m g : ℕ) (hg : g ≤ m) : Palette m :=
  ⟨⟨g,by omega⟩,⟨0,Nat.choose_pos hg⟩⟩

@[simp]
theorem fixedColor_grade (m g : ℕ) (hg : g ≤ m) :
    grade (fixedColor m g hg) = g := rfl

def prefixColors (m u : ℕ) (hu : u + 1 ≤ m) : List (Palette m) :=
  fixedColor m (u+1) hu :: List.replicate u (zeroColor m)

def suffixColors (m v : ℕ) (hv : v-1 ≤ m) (hm : 2 ≤ m) : List (Palette m) :=
  fixedColor m (v-1) hv :: (List.replicate (v-1) (zeroColor m) ++ [fixedColor m 2 hm])

def shellPath (u v : ℕ) (U : List Bool) : List Bool :=
  runShape u ++ (U ++ runShape v)

def shellColors {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (cs : List (Palette m)) : List (Palette m) :=
  prefixColors m u hu ++ (cs ++ suffixColors m v hv hm)

theorem prefix_length (m u : ℕ) (hu : u+1 ≤ m) :
    (prefixColors m u hu).length = (runShape u).length := by
  simp [prefixColors, runShape]

theorem suffix_length (m v : ℕ) (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) :
    (suffixColors m v hv hm).length = (runShape v).length := by
  simp [suffixColors, runShape]
  omega

theorem shellColors_length {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (cs : List (Palette m))
    (hcs : cs.length = U.length) :
    (shellColors u v hu hv hm cs).length = (shellPath u v U).length := by
  simp [shellColors, shellPath, List.length_append, prefix_length, suffix_length _ _ _ _ hpos, hcs]

theorem prefix_word (m u : ℕ) (hu : u+1 ≤ m) :
    List.zipWith paint (runShape u) (prefixColors m u hu) =
      .H (u+1) :: List.replicate u (.V 0) := by
  simp [runShape, prefixColors, paint]

theorem suffix_word (m v : ℕ) (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) :
    List.zipWith paint (runShape v) (suffixColors m v hv hm) =
      .H (v-1) :: (List.replicate (v-1) (.V 0) ++ [.V 2]) := by
  have hrep : List.replicate v false = List.replicate (v-1) false ++ [false] := by
    rw [← List.replicate_succ']
    congr 1
    omega
  simp only [runShape, suffixColors, List.zipWith_cons_cons, hrep]
  rw [List.zipWith_append (by simp)]
  simp [paint]

def shellColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (g : Coloring m U.length) :
    Coloring m (shellPath u v U).length :=
  fromList (shellColors u v hu hv hm (List.ofFn g))
    (shellColors_length u v hu hv hm hpos U _ (by simp))

theorem shellColoring_word {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (g : Coloring m U.length) :
    pathWord (shellPath u v U) (shellColoring u v hu hv hm hpos U g) =
      shell u (v-1) 0 [(pathWord U g,c)] := by
  rw [shellColoring, fromList_word]
  unfold shellPath shellColors
  rw [List.zipWith_append (prefix_length m u hu).symm]
  rw [List.zipWith_append (by simp)]
  rw [prefix_word, suffix_word _ _ _ _ hpos, ← word_zip]
  simp [shell, List.append_assoc]

/-- Restriction to the original interior positions, preserving both grade and color. -/
def recover {m : ℕ} (u v : ℕ) (U : List Bool)
    (g : Coloring m (shellPath u v U).length) : Coloring m U.length :=
  fun i => g ⟨(u+1)+i.val,by simp [shellPath, runShape]; omega⟩

theorem recover_shellColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (g : Coloring m U.length) :
    recover u v U (shellColoring u v hu hv hm hpos U g) = g := by
  funext i
  simp only [recover, shellColoring, fromList, shellColors]
  rw [List.getElem_append_right (by simp [prefixColors])]
  simp [prefixColors, List.getElem_append_left, i.isLt]

theorem shellColoring_injective {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) :
    Function.Injective (shellColoring u v hu hv hm hpos U) :=
  Function.LeftInverse.injective (recover_shellColoring u v hu hv hm hpos U)

theorem shellColoring_connected {m u v c : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (U : List Bool) (g : Coloring m U.length)
    (hg : Connected m (pathWord U g) c) :
    Connected m (pathWord (shellPath u v U)
      (shellColoring u v (by omega) (by omega) (by omega) hv.1 U g)) c := by
  rw [shellColoring_word u v c]
  have hs := manuscript_shell m u v 0 [(pathWord U g,c)] hm hu hv
    (by simpa using hg) (Or.inl ⟨by simp, rfl⟩)
  simpa using hs

/-- The finite colored map: all old palette entries are copied, and all new
entries use color zero at the shell's prescribed grades. -/
def unaryShell {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    ConnectedColorings m U c → ConnectedColorings m (shellPath u v U) c :=
  fun g => ⟨shellColoring u v (by omega) (by omega) (by omega) hv.1 U g.val,
    shellColoring_connected hm hu hv U g.val g.property⟩

theorem unaryShell_recover {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool)
    (g : ConnectedColorings m U c) :
    recover u v U (unaryShell u v c hm hu hv U g).val = g.val :=
  recover_shellColoring u v (by omega) (by omega) (by omega) hv.1 U g.val

theorem unaryShell_injective {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    Function.Injective (unaryShell u v c hm hu hv U) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg (fun z => recover u v U z.val) hxy
  simpa only [unaryShell_recover] using h

theorem unary_pathCount_le {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    pathCount m U c ≤ pathCount m (shellPath u v U) c := by
  classical
  simp only [pathCount, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective (unaryShell u v c hm hu hv U)
    (unaryShell_injective u v c hm hu hv U)

theorem shellPath_runWord (u v : ℕ) (rs : List ℕ) :
    shellPath u v (runWord rs) = runWord (u :: rs ++ [v]) := by
  simp [shellPath, runWord]

/-- The fixed-color unary-shell counting inequality on the same runCount
defined in Cycle 001. No extra color multiplicity is asserted here. -/
theorem unary_runCount_le {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (rs : List ℕ) :
    runCount m rs c ≤ runCount m (u :: rs ++ [v]) c := by
  simpa only [runCount, shellPath_runWord] using
    unary_pathCount_le u v c hm hu hv (runWord rs)

end KroneckerColoredShell
