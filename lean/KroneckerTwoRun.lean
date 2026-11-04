import KroneckerOneRun

/-! The two-run colored base from the nullary shell. Its final grade-one
vertical edge carries any of the m colors, and that color is recovered exactly. -/
set_option autoImplicit false
namespace KroneckerTwoRun
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerOneRun

def gradeOneColor (m : ℕ) (hm : 1 ≤ m) (k : Fin m) : Palette m :=
  runColor m 1 hm ⟨k.val, by simp⟩

@[simp]
theorem gradeOneColor_grade (m : ℕ) (hm : 1 ≤ m) (k : Fin m) :
    grade (gradeOneColor m hm k) = 1 := rfl

theorem gradeOneColor_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (gradeOneColor m hm) := by
  intro k l h
  apply Fin.ext
  exact congrArg (fun p : Palette m => p.2.val) h

def suffixColors (m v : ℕ) (hv : v-1 ≤ m) (hm : 1 ≤ m) (k : Fin m) :
    List (Palette m) :=
  fixedColor m (v-1) hv ::
    (List.replicate (v-1) (zeroColor m) ++ [gradeOneColor m hm k])

def baseColors (m u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 1 ≤ m) (k : Fin m) : List (Palette m) :=
  prefixColors m u hu ++ suffixColors m v hv hm k

theorem suffix_length (m v : ℕ) (hv : v-1 ≤ m) (hm : 1 ≤ m)
    (hpos : 1 ≤ v) (k : Fin m) :
    (suffixColors m v hv hm k).length = (runShape v).length := by
  simp [suffixColors, runShape]
  omega

theorem baseColors_length (m u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 1 ≤ m) (hpos : 1 ≤ v) (k : Fin m) :
    (baseColors m u v hu hv hm k).length = (runWord [u,v]).length := by
  simp [baseColors, runWord, prefix_length, suffix_length _ _ _ _ hpos]

theorem suffix_word (m v : ℕ) (hv : v-1 ≤ m) (hm : 1 ≤ m)
    (hpos : 1 ≤ v) (k : Fin m) :
    List.zipWith paint (runShape v) (suffixColors m v hv hm k) =
      .H (v-1) :: (List.replicate (v-1) (.V 0) ++ [.V 1]) := by
  have hrep : List.replicate v false = List.replicate (v-1) false ++ [false] := by
    rw [← List.replicate_succ']
    congr 1
    omega
  simp only [runShape, suffixColors, List.zipWith_cons_cons, hrep]
  rw [List.zipWith_append (by simp)]
  simp [paint]

def baseColoring (m u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 1 ≤ m) (hpos : 1 ≤ v) (k : Fin m) :
    Coloring m (runWord [u,v]).length :=
  fromList (baseColors m u v hu hv hm k) (baseColors_length m u v hu hv hm hpos k)

theorem baseColoring_word (m u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 1 ≤ m) (hpos : 1 ≤ v) (k : Fin m) :
    pathWord (runWord [u,v]) (baseColoring m u v hu hv hm hpos k) =
      shell u (v-1) 0 [] := by
  rw [baseColoring, fromList_word]
  simp only [runWord, List.flatMap_cons, List.flatMap_nil, List.append_nil, baseColors]
  rw [List.zipWith_append (prefix_length m u hu).symm]
  rw [prefix_word, suffix_word _ _ _ _ hpos]
  simp [shell, List.append_assoc]

/-- Read the actual final palette entry in the two-run word. -/
def recoverLast {m : ℕ} (u v : ℕ)
    (g : Coloring m (runWord [u,v]).length) : Palette m :=
  g ⟨(u+1)+v, by simp [runWord, runShape]; omega⟩

theorem recoverLast_baseColoring (m u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 1 ≤ m) (hpos : 1 ≤ v) (k : Fin m) :
    recoverLast u v (baseColoring m u v hu hv hm hpos k) = gradeOneColor m hm k := by
  simp only [recoverLast, baseColoring, fromList, baseColors]
  rw [List.getElem_append_right (by simp [prefixColors])]
  simp only [prefixColors, List.length_cons, List.length_replicate,
    Nat.add_sub_cancel_left]
  have hv' : v ≠ 0 := by omega
  simp [suffixColors, List.getElem_cons, hv', List.getElem_append_right]

theorem baseColoring_connected {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (k : Fin m) :
    Connected m (pathWord (runWord [u,v])
      (baseColoring m u v (by omega) (by omega) (by omega) hv.1 k)) 0 := by
  rw [baseColoring_word]
  have hs := manuscript_shell m u v 0 [] hm hu hv (by simp) (Or.inl ⟨by simp, rfl⟩)
  simpa using hs

/-- A direct nullary-shell map; no connected empty interior is assumed. -/
def twoRun {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) :
    Fin m → ConnectedColorings m (runWord [u,v]) 0 :=
  fun k => ⟨baseColoring m u v (by omega) (by omega) (by omega) hv.1 k,
    baseColoring_connected hm hu hv k⟩

theorem twoRun_recoverLast {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (k : Fin m) :
    recoverLast u v (twoRun hm hu hv k).val = gradeOneColor m (by omega) k :=
  recoverLast_baseColoring m u v (by omega) (by omega) (by omega) hv.1 k

theorem twoRun_injective {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) :
    Function.Injective (twoRun hm hu hv) := by
  intro k l hkl
  apply gradeOneColor_injective m (by omega)
  have h := congrArg (fun z => recoverLast u v z.val) hkl
  simpa only [twoRun_recoverLast] using h

/-- The two-run base on the same literal finite colored count as Cycle 001. -/
theorem two_run_lower_bound {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) :
    m ≤ runCount m [u,v] 0 := by
  classical
  have h := Fintype.card_le_of_injective (twoRun hm hu hv) (twoRun_injective hm hu hv)
  simpa only [Fintype.card_fin, runCount, pathCount, Nat.card_eq_fintype_card] using h

end KroneckerTwoRun
