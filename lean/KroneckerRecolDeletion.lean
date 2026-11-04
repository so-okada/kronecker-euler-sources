import KroneckerRecolOperations

set_option autoImplicit false
noncomputable section
namespace KroneckerRecolDeletion
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerColoring KroneckerColoredShell KroneckerRecolPaletteBridge
open KroneckerDeletionColoring KroneckerDeletionInteriorColors KroneckerLowerPalette
open KroneckerListDeletion KroneckerRecolOperations

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem deletion_copy {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (r : Edge U) (j : Fin r.val)
    (c : Coloring m U.steps.length) (k : {k : Edge U // k ≠ r}) :
    deletionColoring u v hu hv hm hpos U.steps r.val r.isLt j c
      (deletionIndices U u v r k) =
      if k.val.val = j.val then lowerPalette (c k.val) else c k.val := by
  have hk := k.val.isLt
  have hr := r.isLt
  have hj := j.isLt
  have hn : k.val.val ≠ r.val := fun h => k.property (Fin.ext h)
  let a : Fin (removeAt r.val U.steps).length :=
    ⟨if k.val.val < r.val then k.val.val else k.val.val-1, by
      simp only [removeAt, List.length_append, List.length_take, List.length_drop,
        Nat.min_eq_left (Nat.le_of_lt hr)]
      split_ifs <;> omega⟩
  have he : deletionIndices U u v r k =
      shellIndices (ofSteps (removeAt r.val U.steps) 0) u v a := by
    apply Fin.ext
    dsimp [deletionIndices, shellIndices, a]
    split_ifs <;> omega
  rw [he]
  change shellColoring u v hu hv hm hpos _ _ _ = _
  refine (shell_copy (ofSteps (removeAt r.val U.steps) 0) u v hu hv hm hpos
    (editedColoring U.steps r.val r.isLt j c) a).trans ?_
  unfold editedColoring fromList editedColors
  dsimp [a]
  split_ifs with h
  all_goals
    simp [List.getElem_append, List.getElem_set, List.length_take]
    split_ifs <;> try omega
    all_goals try simp only []
  all_goals try split_ifs <;> try omega
  all_goals
    first
    | rfl
    | (apply congrArg lowerPalette; apply congrArg c; apply Fin.ext; dsimp; omega)
    | (apply congrArg c; apply Fin.ext; dsimp; omega)
    | (have hne : k.val.val ≠ j.val := by omega
       rw [ite_eq_right hne]
       apply congrArg c; apply Fin.ext; dsimp; omega)

theorem lower_respects {m : ℕ} (p : Palette m) (hp : 0 < grade p) :
    RespectsRecol p (lowerPalette p) := by
  constructor
  · intro h
    change grade p - 1 = grade p at h
    omega
  · intro _
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem deletion_new {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (r : Edge U) (j : Fin r.val)
    (c : Coloring m U.steps.length)
    (k : Edge (ofSteps (deletionPath u v U.steps r.val) 0))
    (hk : k ∉ Set.range (deletionIndices U u v r)) :
    (deletionColoring u v hu hv hm hpos U.steps r.val r.isLt j c k).2.val = 0 := by
  apply shell_new (ofSteps (removeAt r.val U.steps) 0) u v hu hv hm hpos _ k
  rintro ⟨a, ha⟩
  apply hk
  have hr := r.isLt
  have hl := a.isLt
  simp only [ofSteps_steps, removeAt, List.length_append, List.length_take,
    List.length_drop, Nat.min_eq_left (Nat.le_of_lt hr)] at hl
  by_cases hb : a.val < r.val
  · refine ⟨⟨⟨a.val, by omega⟩, ?_⟩, ?_⟩
    · intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
    · rw [← ha]
      apply Fin.ext
      dsimp only [deletionIndices, shellIndices, Function.Embedding.coeFn_mk]
      split_ifs <;> omega
  · refine ⟨⟨⟨a.val+1, by omega⟩, ?_⟩, ?_⟩
    · intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
    · rw [← ha]
      apply Fin.ext
      simp only [deletionIndices, shellIndices, Function.Embedding.coeFn_mk]
      dsimp
      split_ifs <;> omega

theorem deletion_eq {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (r : Edge U) (j : Fin r.val)
    (c : Coloring m U.steps.length) (hj : 0 < grade (c ⟨j.val, lt_trans j.isLt r.isLt⟩)) :
    KroneckerRecolorConstructions.deletion U u v hu hv hm hpos r j c =
      fromPalette _ (deletionColoring u v hu hv hm hpos U.steps r.val r.isLt j c) := by
  apply fromPalette_recol
  · intro k
    apply (congrArg (RespectsRecol (c k.val))
      (deletion_copy U u v hu hv hm hpos r j c k)).mpr
    split_ifs with h
    · apply lower_respects
      have he : k.val = ⟨j.val, lt_trans j.isLt r.isLt⟩ := Fin.ext h
      simpa only [he] using hj
    · exact respects_self _
  · exact deletion_new U u v hu hv hm hpos r j c

/-- Lemma 4.6(1): existence for the literal Recol map. This proof uses the
checked backtrace and shell construction. The manuscript instead applies
Lemma 4.5, whose compressed-index identity is geometric_erasure, and then
checks the node balances directly. -/
theorem deletion_exists {m d : ℕ} (U : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (r : Edge U)
    (hr : U.steps[r.val] = false) (c : Coloring m U.steps.length)
    (hc : KroneckerStack.Connected m (KroneckerWordCounts.pathWord U.steps c) d) :
    ∃ j : Fin r.val, U.steps[j.val] = true ∧
      0 < grade (c ⟨j.val, lt_trans j.isLt r.isLt⟩) ∧
      ConnectedGrading (KroneckerRecolorConstructions.deletion U u v hu hv hm hpos r j c).1 ∧
      Surp _ (KroneckerRecolorConstructions.deletion U u v hu hv hm hpos r j c).1 =
        ((d + grade (c r) : ℕ) : ℤ) := by
  obtain ⟨j, hj, hp, hc'⟩ := KroneckerDeletionColorExists.deletion_color_exists
    u v d hu hv hm hpos U.steps r.val r.isLt hr c hc
  refine ⟨j, hj, hp, ?_⟩
  rw [deletion_eq U u v hu hv hm hpos r j c hp]
  exact KroneckerRecolorConstructions.fromPalette_connected _ _ hc'

end KroneckerRecolDeletion
