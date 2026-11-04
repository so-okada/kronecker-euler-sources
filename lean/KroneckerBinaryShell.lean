import KroneckerColoredShell

/-! A binary colored shell with exact recovery of both connected interiors. -/
set_option autoImplicit false
namespace KroneckerBinaryShell
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell

def binaryPath (u v : ℕ) (U V : List Bool) : List Bool :=
  runShape u ++ (U ++ (V ++ runShape v))

def suffixColors (m v : ℕ) (hv : v-1 ≤ m) (hm : 3 ≤ m) : List (Palette m) :=
  fixedColor m (v-1) hv ::
    (List.replicate (v-1) (zeroColor m) ++ [fixedColor m 3 hm])

def binaryColors {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (cs ds : List (Palette m)) : List (Palette m) :=
  prefixColors m u hu ++ (cs ++ (ds ++ suffixColors m v hv hm))

theorem suffix_length (m v : ℕ) (hv : v-1 ≤ m) (hm : 3 ≤ m) (hpos : 1 ≤ v) :
    (suffixColors m v hv hm).length = (runShape v).length := by
  simp [suffixColors, runShape]
  omega

theorem binaryColors_length {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (U V : List Bool) (cs ds : List (Palette m))
    (hc : cs.length = U.length) (hd : ds.length = V.length) :
    (binaryColors u v hu hv hm cs ds).length = (binaryPath u v U V).length := by
  simp [binaryColors, binaryPath, prefix_length, suffix_length _ _ _ _ hpos, hc, hd]

theorem suffix_word (m v : ℕ) (hv : v-1 ≤ m) (hm : 3 ≤ m) (hpos : 1 ≤ v) :
    List.zipWith paint (runShape v) (suffixColors m v hv hm) =
      .H (v-1) :: (List.replicate (v-1) (.V 0) ++ [.V 3]) := by
  have hrep : List.replicate v false = List.replicate (v-1) false ++ [false] := by
    rw [← List.replicate_succ']
    congr 1
    omega
  simp only [runShape, suffixColors, List.zipWith_cons_cons, hrep]
  rw [List.zipWith_append (by simp)]
  simp [paint]

def binaryColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (U V : List Bool)
    (f : Coloring m U.length) (g : Coloring m V.length) :
    Coloring m (binaryPath u v U V).length :=
  fromList (binaryColors u v hu hv hm (List.ofFn f) (List.ofFn g))
    (binaryColors_length u v hu hv hm hpos U V _ _ (by simp) (by simp))

theorem binaryColoring_word {m : ℕ} (u v c d : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (U V : List Bool)
    (f : Coloring m U.length) (g : Coloring m V.length) :
    pathWord (binaryPath u v U V) (binaryColoring u v hu hv hm hpos U V f g) =
      shell u (v-1) 0 [(pathWord U f,c), (pathWord V g,d)] := by
  rw [binaryColoring, fromList_word]
  unfold binaryPath binaryColors
  rw [List.zipWith_append (prefix_length m u hu).symm]
  rw [List.zipWith_append (by simp), List.zipWith_append (by simp)]
  rw [prefix_word, suffix_word _ _ _ _ hpos, ← word_zip, ← word_zip]
  simp [shell, List.append_assoc]

def recoverLeft {m : ℕ} (u v : ℕ) (U V : List Bool)
    (g : Coloring m (binaryPath u v U V).length) : Coloring m U.length :=
  fun i => g ⟨(u+1)+i.val, by simp [binaryPath, runShape]; omega⟩

def recoverRight {m : ℕ} (u v : ℕ) (U V : List Bool)
    (g : Coloring m (binaryPath u v U V).length) : Coloring m V.length :=
  fun i => g ⟨(u+1)+U.length+i.val, by simp [binaryPath, runShape]; omega⟩

theorem recoverLeft_binaryColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (U V : List Bool)
    (f : Coloring m U.length) (g : Coloring m V.length) :
    recoverLeft u v U V (binaryColoring u v hu hv hm hpos U V f g) = f := by
  funext i
  simp only [recoverLeft, binaryColoring, fromList, binaryColors]
  rw [List.getElem_append_right (by simp [prefixColors])]
  simp [prefixColors, List.getElem_append_left, i.isLt]

theorem recoverRight_binaryColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (U V : List Bool)
    (f : Coloring m U.length) (g : Coloring m V.length) :
    recoverRight u v U V (binaryColoring u v hu hv hm hpos U V f g) = g := by
  funext i
  simp only [recoverRight, binaryColoring, fromList, binaryColors]
  rw [List.getElem_append_right (by simp [prefixColors]; omega)]
  simp only [prefixColors, List.length_cons, List.length_replicate]
  have hsub : u+1+U.length+i.val-(u+1) = U.length+i.val := by omega
  simp only [hsub]
  rw [List.getElem_append_right (by simp)]
  simp [List.getElem_append_left, i.isLt]

theorem binaryColoring_connected {m u v c d : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U V : List Bool)
    (f : Coloring m U.length) (g : Coloring m V.length)
    (hf : Connected m (pathWord U f) c) (hg : Connected m (pathWord V g) d) :
    Connected m (pathWord (binaryPath u v U V)
      (binaryColoring u v (by omega) (by omega) hm hv.1 U V f g)) (c+d) := by
  rw [binaryColoring_word u v c d]
  have hs := manuscript_shell m u v 0 [(pathWord U f,c), (pathWord V g,d)] hm hu hv
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hf
      · exact hg)
    (Or.inl ⟨by simp, rfl⟩)
  simpa using hs

def binaryShell {m : ℕ} (u v c d : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U V : List Bool) :
    ConnectedColorings m U c × ConnectedColorings m V d →
      ConnectedColorings m (binaryPath u v U V) (c+d) :=
  fun x => ⟨binaryColoring u v (by omega) (by omega) hm hv.1 U V x.1.val x.2.val,
    binaryColoring_connected hm hu hv U V x.1.val x.2.val x.1.property x.2.property⟩

theorem binaryShell_injective {m : ℕ} (u v c d : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U V : List Bool) :
    Function.Injective (binaryShell u v c d hm hu hv U V) := by
  intro x y hxy
  apply Prod.ext
  · apply Subtype.ext
    have h := congrArg (fun z => recoverLeft u v U V z.val) hxy
    simpa only [binaryShell, recoverLeft_binaryColoring] using h
  · apply Subtype.ext
    have h := congrArg (fun z => recoverRight u v U V z.val) hxy
    simpa only [binaryShell, recoverRight_binaryColoring] using h

theorem binary_pathCount_bound {m : ℕ} (u v c d : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U V : List Bool) :
    pathCount m U c * pathCount m V d ≤ pathCount m (binaryPath u v U V) (c+d) := by
  classical
  have h := Fintype.card_le_of_injective (binaryShell u v c d hm hu hv U V)
    (binaryShell_injective u v c d hm hu hv U V)
  simpa only [Fintype.card_prod, pathCount, Nat.card_eq_fintype_card] using h

theorem binaryPath_runWord (u v : ℕ) (xs ys : List ℕ) :
    binaryPath u v (runWord xs) (runWord ys) = runWord (u :: (xs ++ ys) ++ [v]) := by
  simp [binaryPath, runWord, List.append_assoc]

theorem binary_runCount_bound {m : ℕ} (u v c d : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (xs ys : List ℕ) :
    runCount m xs c * runCount m ys d ≤ runCount m (u :: (xs ++ ys) ++ [v]) (c+d) := by
  simpa only [runCount, binaryPath_runWord] using
    binary_pathCount_bound u v c d hm hu hv (runWord xs) (runWord ys)

end KroneckerBinaryShell
