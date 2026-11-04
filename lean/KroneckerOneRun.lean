import KroneckerColoredShell

/-! The one-run colored base case. Every horizontal grade-r color gives
a connected zero-surplus filling of R_r, and that color is recoverable. -/
set_option autoImplicit false
namespace KroneckerOneRun
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell

def runColor (m r : ℕ) (hbound : r ≤ m) (k : Fin (Nat.choose m r)) : Palette m :=
  ⟨⟨r, by omega⟩, k⟩

@[simp]
theorem runColor_grade (m r : ℕ) (hbound : r ≤ m) (k : Fin (Nat.choose m r)) :
    grade (runColor m r hbound k) = r := rfl

theorem runColor_injective (m r : ℕ) (hbound : r ≤ m) :
    Function.Injective (runColor m r hbound) := by
  intro k l h
  apply Fin.ext
  exact congrArg (fun p : Palette m => p.2.val) h

def baseColors (m r : ℕ) (hbound : r ≤ m) (k : Fin (Nat.choose m r)) :
    List (Palette m) :=
  runColor m r hbound k :: List.replicate r (zeroColor m)

theorem baseColors_length (m r : ℕ) (hbound : r ≤ m) (k : Fin (Nat.choose m r)) :
    (baseColors m r hbound k).length = (runShape r).length := by
  simp [baseColors, runShape]

def baseColoring (m r : ℕ) (hbound : r ≤ m) (k : Fin (Nat.choose m r)) :
    Coloring m (runShape r).length :=
  fromList (baseColors m r hbound k) (baseColors_length m r hbound k)

theorem baseColoring_word (m r : ℕ) (hbound : r ≤ m) (k : Fin (Nat.choose m r)) :
    pathWord (runShape r) (baseColoring m r hbound k) =
      .H r :: List.replicate r (.V 0) := by
  rw [baseColoring, fromList_word]
  simp [runShape, baseColors, paint]

/-- Read the full horizontal palette entry, retaining its binomial color. -/
def recoverFirst {m : ℕ} (r : ℕ) (g : Coloring m (runShape r).length) : Palette m :=
  g ⟨0, by simp [runShape]⟩

theorem recoverFirst_baseColoring (m r : ℕ) (hbound : r ≤ m)
    (k : Fin (Nat.choose m r)) :
    recoverFirst r (baseColoring m r hbound k) = runColor m r hbound k := by
  simp [recoverFirst, baseColoring, fromList, baseColors]

theorem baseColoring_connected {m r : ℕ} (hr : 1 ≤ r) (hbound : r ≤ m)
    (k : Fin (Nat.choose m r)) :
    Connected m (pathWord (runShape r) (baseColoring m r hbound k)) 0 := by
  rw [baseColoring_word]
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  apply node_connected (one_run_node s)
  intro edge h
  simp only [List.mem_cons, List.mem_replicate] at h
  rcases h with h | ⟨_, h⟩ <;> subst edge
  · exact hbound
  · exact Nat.zero_le m

/-- Vary the horizontal color while fixing every vertical entry at grade zero. -/
def oneRun {m r : ℕ} (hr : 1 ≤ r) (hbound : r ≤ m) :
    Fin (Nat.choose m r) → ConnectedColorings m (runShape r) 0 :=
  fun k => ⟨baseColoring m r hbound k, baseColoring_connected hr hbound k⟩

theorem oneRun_recover {m r : ℕ} (hr : 1 ≤ r) (hbound : r ≤ m)
    (k : Fin (Nat.choose m r)) :
    recoverFirst r (oneRun hr hbound k).val = runColor m r hbound k :=
  recoverFirst_baseColoring m r hbound k

theorem oneRun_injective {m r : ℕ} (hr : 1 ≤ r) (hbound : r ≤ m) :
    Function.Injective (oneRun hr hbound) := by
  intro k l hkl
  apply runColor_injective m r hbound
  have h := congrArg (fun z => recoverFirst r z.val) hkl
  simpa only [oneRun_recover] using h

theorem choose_le_pathCount {m r : ℕ} (hr : 1 ≤ r) (hbound : r ≤ m) :
    Nat.choose m r ≤ pathCount m (runShape r) 0 := by
  classical
  have h := Fintype.card_le_of_injective (oneRun hr hbound) (oneRun_injective hr hbound)
  simpa only [Fintype.card_fin, pathCount, Nat.card_eq_fintype_card] using h

theorem choose_le_runCount {m r : ℕ} (hr : 1 ≤ r) (hbound : r ≤ m) :
    Nat.choose m r ≤ runCount m [r] 0 := by
  simpa [runCount, runWord] using choose_le_pathCount hr hbound

/-- Every nontrivial binomial coefficient in row m is at least m. -/
theorem self_le_choose {m r : ℕ} (hr : 1 ≤ r) (hbound : r < m) :
    m ≤ Nat.choose m r := by
  induction m generalizing r with
  | zero => omega
  | succ m ih =>
    by_cases hlast : r = m
    · subst r
      simp [Nat.choose_succ_self_right]
    cases r with
    | zero => omega
    | succ r =>
      rw [Nat.choose_succ_succ]
      change m + 1 ≤ Nat.choose m r + Nat.choose m (r+1)
      by_cases hzero : r = 0
      · subst r
        simp [Nat.add_comm]
      have hsmall := ih (by omega : 1 ≤ r) (by omega : r < m)
      have hpos := Nat.choose_pos (by omega : r+1 ≤ m)
      omega

/-- The one-run lower bound; the stronger domain 1 ≤ r < m includes the
manuscript's m ≥ 3 and 1 ≤ r ≤ m-1. -/
theorem one_run_lower_bound {m r : ℕ} (hr : 1 ≤ r) (hbound : r < m) :
    m ≤ runCount m [r] 0 :=
  (self_le_choose hr hbound).trans (choose_le_runCount hr (Nat.le_of_lt hbound))

end KroneckerOneRun
