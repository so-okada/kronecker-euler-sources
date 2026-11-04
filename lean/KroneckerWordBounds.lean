import KroneckerTwoRun

/- Original module: KroneckerShellColors -/
section
/-! An independent final-edge color in the unary shell, with exact recovery
of both that color and the entire interior palette. -/
set_option autoImplicit false
namespace KroneckerShellColors
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell

/-- Every binomial color is allowed at the final vertical edge of grade two. -/
def gradeTwoColor (m : ℕ) (hm : 2 ≤ m) (k : Fin (Nat.choose m 2)) : Palette m :=
  ⟨⟨2, by omega⟩, k⟩

@[simp]
theorem gradeTwoColor_grade (m : ℕ) (hm : 2 ≤ m) (k : Fin (Nat.choose m 2)) :
    grade (gradeTwoColor m hm k) = 2 := rfl

theorem gradeTwoColor_injective (m : ℕ) (hm : 2 ≤ m) :
    Function.Injective (gradeTwoColor m hm) := by
  intro k l h
  apply Fin.ext
  exact congrArg (fun p : Palette m => p.2.val) h

def suffixColors (m v : ℕ) (hv : v-1 ≤ m) (hm : 2 ≤ m)
    (k : Fin (Nat.choose m 2)) : List (Palette m) :=
  fixedColor m (v-1) hv ::
    (List.replicate (v-1) (zeroColor m) ++ [gradeTwoColor m hm k])

def shellColors {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (k : Fin (Nat.choose m 2)) (cs : List (Palette m)) :
    List (Palette m) :=
  prefixColors m u hu ++ (cs ++ suffixColors m v hv hm k)

theorem suffix_length (m v : ℕ) (hv : v-1 ≤ m) (hm : 2 ≤ m)
    (hpos : 1 ≤ v) (k : Fin (Nat.choose m 2)) :
    (suffixColors m v hv hm k).length = (runShape v).length := by
  simp [suffixColors, runShape]
  omega

theorem shellColors_length {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (k : Fin (Nat.choose m 2))
    (U : List Bool) (cs : List (Palette m)) (hcs : cs.length = U.length) :
    (shellColors u v hu hv hm k cs).length = (shellPath u v U).length := by
  simp [shellColors, shellPath, List.length_append, prefix_length,
    suffix_length _ _ _ _ hpos, hcs]

theorem suffix_word (m v : ℕ) (hv : v-1 ≤ m) (hm : 2 ≤ m)
    (hpos : 1 ≤ v) (k : Fin (Nat.choose m 2)) :
    List.zipWith paint (runShape v) (suffixColors m v hv hm k) =
      .H (v-1) :: (List.replicate (v-1) (.V 0) ++ [.V 2]) := by
  have hrep : List.replicate v false = List.replicate (v-1) false ++ [false] := by
    rw [← List.replicate_succ']
    congr 1
    omega
  simp only [runShape, suffixColors, List.zipWith_cons_cons, hrep]
  rw [List.zipWith_append (by simp)]
  simp [paint]

def shellColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool)
    (k : Fin (Nat.choose m 2)) (g : Coloring m U.length) :
    Coloring m (shellPath u v U).length :=
  fromList (shellColors u v hu hv hm k (List.ofFn g))
    (shellColors_length u v hu hv hm hpos k U _ (by simp))

theorem shellColoring_word {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool)
    (k : Fin (Nat.choose m 2)) (g : Coloring m U.length) :
    pathWord (shellPath u v U) (shellColoring u v hu hv hm hpos U k g) =
      shell u (v-1) 0 [(pathWord U g,c)] := by
  rw [shellColoring, fromList_word]
  unfold shellPath shellColors
  rw [List.zipWith_append (prefix_length m u hu).symm]
  rw [List.zipWith_append (by simp)]
  rw [prefix_word, suffix_word _ _ _ _ hpos, ← word_zip]
  simp [shell, List.append_assoc]

theorem recover_shellColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool)
    (k : Fin (Nat.choose m 2)) (g : Coloring m U.length) :
    recover u v U (shellColoring u v hu hv hm hpos U k g) = g := by
  funext i
  simp only [recover, shellColoring, fromList, shellColors]
  rw [List.getElem_append_right (by simp [prefixColors])]
  simp [prefixColors, List.getElem_append_left, i.isLt]

/-- Read the actual final palette entry; this does not discard its color. -/
def recoverLast {m : ℕ} (u v : ℕ) (U : List Bool)
    (g : Coloring m (shellPath u v U).length) : Palette m :=
  g ⟨(u+1)+U.length+v, by simp [shellPath, runShape]; omega⟩

theorem recoverLast_shellColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool)
    (k : Fin (Nat.choose m 2)) (g : Coloring m U.length) :
    recoverLast u v U (shellColoring u v hu hv hm hpos U k g) =
      gradeTwoColor m hm k := by
  simp only [recoverLast, shellColoring, fromList, shellColors]
  rw [List.getElem_append_right (by simp [prefixColors]; omega)]
  simp only [prefixColors, List.length_cons, List.length_replicate]
  have hsub : u + 1 + U.length + v - (u + 1) = U.length + v := by omega
  simp only [hsub]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  have hv' : v ≠ 0 := by omega
  simp [suffixColors, List.getElem_cons, hv', List.getElem_append_right]

theorem shellColoring_joint_injective {m : ℕ} (u v : ℕ)
    (hu : u+1 ≤ m) (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) :
    Function.Injective (fun x : Fin (Nat.choose m 2) × Coloring m U.length =>
      shellColoring u v hu hv hm hpos U x.1 x.2) := by
  intro x y hxy
  apply Prod.ext
  · apply gradeTwoColor_injective m hm
    have h := congrArg (recoverLast u v U) hxy
    simpa only [recoverLast_shellColoring] using h
  · have h := congrArg (recover u v U) hxy
    simpa only [recover_shellColoring] using h

theorem shellColoring_connected {m u v c : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (U : List Bool) (k : Fin (Nat.choose m 2)) (g : Coloring m U.length)
    (hg : Connected m (pathWord U g) c) :
    Connected m (pathWord (shellPath u v U)
      (shellColoring u v (by omega) (by omega) (by omega) hv.1 U k g)) c := by
  rw [shellColoring_word u v c]
  have hs := manuscript_shell m u v 0 [(pathWord U g,c)] hm hu hv
    (by simpa using hg) (Or.inl ⟨by simp, rfl⟩)
  simpa using hs

/-- The final-edge color and the connected interior coloring vary independently. -/
def unaryShell {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    Fin (Nat.choose m 2) × ConnectedColorings m U c →
      ConnectedColorings m (shellPath u v U) c :=
  fun x => ⟨shellColoring u v (by omega) (by omega) (by omega) hv.1 U x.1 x.2.val,
    shellColoring_connected hm hu hv U x.1 x.2.val x.2.property⟩

theorem unaryShell_recover {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool)
    (x : Fin (Nat.choose m 2) × ConnectedColorings m U c) :
    recover u v U (unaryShell u v c hm hu hv U x).val = x.2.val :=
  recover_shellColoring u v (by omega) (by omega) (by omega) hv.1 U x.1 x.2.val

theorem unaryShell_recoverLast {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool)
    (x : Fin (Nat.choose m 2) × ConnectedColorings m U c) :
    recoverLast u v U (unaryShell u v c hm hu hv U x).val =
      gradeTwoColor m (by omega) x.1 :=
  recoverLast_shellColoring u v (by omega) (by omega) (by omega) hv.1 U x.1 x.2.val

theorem unaryShell_injective {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    Function.Injective (unaryShell u v c hm hu hv U) := by
  intro x y hxy
  apply Prod.ext
  · apply gradeTwoColor_injective m (by omega)
    have h := congrArg (fun z => recoverLast u v U z.val) hxy
    simpa only [unaryShell_recoverLast] using h
  · apply Subtype.ext
    have h := congrArg (fun z => recover u v U z.val) hxy
    simpa only [unaryShell_recover] using h

theorem unary_pathCount_factor {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (U : List Bool) :
    Nat.choose m 2 * pathCount m U c ≤ pathCount m (shellPath u v U) c := by
  classical
  have h := Fintype.card_le_of_injective (unaryShell u v c hm hu hv U)
    (unaryShell_injective u v c hm hu hv U)
  simpa only [Fintype.card_prod, Fintype.card_fin, pathCount,
    Nat.card_eq_fintype_card] using h

/-- The unary-shell multiplicity on the actual finite colored run counts. -/
theorem unary_runCount_factor {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (rs : List ℕ) :
    Nat.choose m 2 * runCount m rs c ≤ runCount m (u :: rs ++ [v]) c := by
  simpa only [runCount, shellPath_runWord] using
    unary_pathCount_factor u v c hm hu hv (runWord rs)

end KroneckerShellColors
end

/- Original module: KroneckerWordBounds -/
section
/-! Quantitative word bounds on actual finite colored counts.
The positive lower bound explicitly requires a nonempty run word. -/
set_option autoImplicit false
namespace KroneckerWordBounds
open KroneckerWordCounts KroneckerOneRun KroneckerTwoRun KroneckerShellColors

theorem unary_runCount_step {m u v : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (rs : List ℕ) :
    m * runCount m rs 0 ≤ runCount m (u :: rs ++ [v]) 0 := by
  calc
    m * runCount m rs 0 ≤ Nat.choose m 2 * runCount m rs 0 :=
      Nat.mul_le_mul_right _ (self_le_choose (by omega) (by omega))
    _ ≤ runCount m (u :: rs ++ [v]) 0 := unary_runCount_factor u v 0 hm hu hv rs

theorem runCount_lower_bound (m : ℕ) (hm : 3 ≤ m) (rs : List ℕ) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) :
    m ^ ((rs.length+1)/2) ≤ runCount m rs 0 := by
  have hb : ∀ n : ℕ, ∀ rs : List ℕ, rs.length = n → rs ≠ [] →
      (∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) →
      m ^ ((rs.length+1)/2) ≤ runCount m rs 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro rs hn hne hr
      cases rs with
      | nil => contradiction
      | cons u tail =>
        have hu := hr u (by simp)
        by_cases ht : tail = []
        · subst tail
          simpa using one_run_lower_bound hu.1 (by omega : u < m)
        · obtain ⟨mid, v, htail⟩ : ∃ mid v, tail = mid ++ [v] :=
            ⟨tail.dropLast, tail.getLast ht, (List.dropLast_append_getLast ht).symm⟩
          subst tail
          have hv := hr v (by simp)
          by_cases hmid : mid = []
          · subst mid
            simpa using two_run_lower_bound hm hu hv
          · have hlt : mid.length < n := by simp at hn; omega
            have hinner := ih mid.length hlt mid rfl hmid
              (by intro r hmem; exact hr r (by simp [hmem]))
            have hexp : ((u :: (mid ++ [v])).length+1)/2 = (mid.length+1)/2+1 := by
              simp
              omega
            rw [hexp, pow_succ]
            calc
              m ^ ((mid.length+1)/2) * m ≤ runCount m mid 0 * m :=
                Nat.mul_le_mul_right m hinner
              _ = m * runCount m mid 0 := Nat.mul_comm _ _
              _ ≤ runCount m (u :: (mid ++ [v])) 0 := by
                simpa only [List.cons_append] using unary_runCount_step hm hu hv mid
  exact hb rs.length rs rfl hne hr

theorem runCount_pos (m : ℕ) (hm : 3 ≤ m) (rs : List ℕ) (hne : rs ≠ [])
    (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ m-1) :
    0 < runCount m rs 0 :=
  lt_of_lt_of_le (pow_pos (by omega : 0 < m) _)
    (runCount_lower_bound m hm rs hne hr)

/-- Both inequalities of the manuscript word bound, with the necessary
nonemptiness condition stated explicitly. -/
theorem runCount_bounds (m L : ℕ) (hm : 3 ≤ m) (hL : L ≤ m-1)
    (rs : List ℕ) (hne : rs ≠ []) (hr : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ L) :
    m ^ ((rs.length+1)/2) ≤ runCount m rs 0 ∧
      runCount m rs 0 ≤ 2 ^ (m * (L+1) * rs.length) := by
  exact ⟨runCount_lower_bound m hm rs hne
      (fun r h => ⟨(hr r h).1, (hr r h).2.trans hL⟩),
    runCount_upper_bound m L 0 rs (fun r h => (hr r h).2)⟩

end KroneckerWordBounds
end
