import KroneckerRecolPaletteBridge

set_option autoImplicit false
noncomputable section
namespace KroneckerRecolOperations
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerColoring KroneckerColoredShell KroneckerRecolPaletteBridge

theorem prefix_zero {m u : ℕ} (hu : u+1 ≤ m) (p : Palette m)
    (hp : p ∈ prefixColors m u hu) : p.2.val = 0 := by
  simp only [prefixColors, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | ⟨_, rfl⟩ <;> rfl

theorem suffix_zero {m v : ℕ} (hv : v-1 ≤ m) (hm : 2 ≤ m) (p : Palette m)
    (hp : p ∈ suffixColors m v hv hm) : p.2.val = 0 := by
  simp only [suffixColors, List.mem_cons, List.mem_append, List.mem_replicate,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | ⟨_, rfl⟩ | rfl <;> rfl

theorem shell_copy {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (c : Coloring m U.steps.length) (k : Edge U) :
    shellColoring u v hu hv hm hpos U.steps c (shellIndices U u v k) = c k :=
  congrFun (recover_shellColoring u v hu hv hm hpos U.steps c) k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem shell_new {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (c : Coloring m U.steps.length) (k : Edge (ofSteps (shellPath u v U.steps) 0))
    (hk : k ∉ Set.range (shellIndices U u v)) :
    (shellColoring u v hu hv hm hpos U.steps c k).2.val = 0 := by
  by_cases hl : k.val < u+1
  · dsimp only [shellColoring, fromList, shellColors]
    rw [List.getElem_append_left (by simpa [prefixColors] using hl)]
    exact prefix_zero hu _ (List.getElem_mem _)
  · have hr : u+1+U.steps.length ≤ k.val := by
      by_contra hn
      apply hk
      refine ⟨⟨k.val-(u+1), by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [shellIndices]
      omega
    dsimp only [shellColoring, fromList, shellColors]
    rw [List.getElem_append_right (by simpa [prefixColors] using (Nat.le_of_not_gt hl))]
    rw [List.getElem_append_right (by simp only [List.length_ofFn, prefixColors,
      List.length_cons, List.length_replicate]; omega)]
    exact suffix_zero hv hm _ (List.getElem_mem _)

theorem shell_eq {m : ℕ} (U : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (c : Coloring m U.steps.length) :
    KroneckerRecolorConstructions.shell U u v hu hv hm hpos c =
      fromPalette _ (shellColoring u v hu hv hm hpos U.steps c) := by
  apply fromPalette_recol_total
  · intro k
    rw [shell_copy]
    exact respects_self _
  · exact shell_new U u v hu hv hm hpos c

open KroneckerInsertionPalette KroneckerListInsertion

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem insertion_copy {m : ℕ} (U : TNEPath) (u v i : ℕ) (hu : u+2 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (hi : i ≤ U.steps.length)
    (c : Coloring m U.steps.length) (k : Edge U) :
    insertionColoring u v i hu hv hm hpos U.steps c (insertionIndices U u v i k) = c k := by
  have hk := k.isLt
  unfold insertionColoring fromList insertedColors insertionIndices
  dsimp
  split_ifs with h
  all_goals
    simp [extraPrefix, insertAt, List.getElem_cons, List.getElem_append,
      List.length_take, Nat.min_eq_left hi]
    split_ifs <;> try omega
    all_goals
      try simp_all only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      first | rfl | (apply congrArg c; apply Fin.ext; dsimp; omega)

theorem extraPrefix_zero {m u : ℕ} (hu : u+2 ≤ m) (p : Palette m)
    (hp : p ∈ extraPrefix m u hu) : p.2.val = 0 := by
  simp only [extraPrefix, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | ⟨_, rfl⟩ <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem insertion_new {m : ℕ} (U : TNEPath) (u v i : ℕ) (hu : u+2 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (hi : i ≤ U.steps.length)
    (c : Coloring m U.steps.length) (k : Edge (ofSteps (insertedPath u v i U.steps) 0))
    (hk : k ∉ Set.range (insertionIndices U u v i)) :
    (insertionColoring u v i hu hv hm hpos U.steps c k).2.val = 0 := by
  by_cases hl : k.val < u+1
  · dsimp only [insertionColoring, fromList, insertedColors]
    rw [List.getElem_append_left (by simpa [extraPrefix] using hl)]
    exact extraPrefix_zero hu _ (List.getElem_mem _)
  · by_cases hr : u+1+(U.steps.length+1) ≤ k.val
    · dsimp only [insertionColoring, fromList, insertedColors]
      rw [List.getElem_append_right (by simpa [extraPrefix] using (Nat.le_of_not_gt hl))]
      rw [List.getElem_append_right (by simp only [insertAt_length, List.length_ofFn,
        extraPrefix, List.length_cons, List.length_replicate]; omega)]
      exact suffix_zero hv hm _ (List.getElem_mem _)
    · have he : k.val = u+1+i := by
        by_contra hn
        apply hk
        by_cases hb : k.val < u+1+i
        · refine ⟨⟨k.val-(u+1), by omega⟩, ?_⟩
          apply Fin.ext
          simp only [insertionIndices, Function.Embedding.coeFn_mk]
          split_ifs <;> omega
        · refine ⟨⟨k.val-(u+2), by omega⟩, ?_⟩
          apply Fin.ext
          simp only [insertionIndices, Function.Embedding.coeFn_mk]
          split_ifs <;> omega
      have hp : insertionColoring u v i hu hv hm hpos U.steps c k = zeroColor m := by
        unfold insertionColoring fromList insertedColors
        simp [extraPrefix, insertAt, List.getElem_cons,
          List.length_take, Nat.min_eq_left hi, he]
      exact congrArg (fun p : Palette m => p.2.val) hp

theorem insertion_eq {m : ℕ} (U : TNEPath) (u v i : ℕ) (hu : u+2 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (hi : i ≤ U.steps.length)
    (c : Coloring m U.steps.length) :
    KroneckerRecolorConstructions.insertion U u v i hu hv hm hpos c =
      fromPalette _ (insertionColoring u v i hu hv hm hpos U.steps c) := by
  apply fromPalette_recol_total
  · intro k
    rw [insertion_copy U u v i hu hv hm hpos hi c k]
    exact respects_self _
  · exact insertion_new U u v i hu hv hm hpos hi c

open KroneckerCompleteRunPalette KroneckerListSplice

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem complete_copy {m : ℕ} (U : TNEPath) (i j : ℕ) (hi : i ≤ U.steps.length)
    (hj : 0 < j) (hm : j ≤ m) (c : Coloring m U.steps.length) (k : Edge U) :
    completeColoring j i hm U.steps c (completeIndices U i j hi hj k) = c k := by
  have hk := k.isLt
  unfold completeColoring fromList completeColors splice completeIndices
  dsimp
  split_ifs with h
  all_goals
    simp [childColors, List.getElem_cons, List.getElem_append, List.length_take,
      Nat.min_eq_left hi]
    split_ifs <;> try omega
    all_goals
      try simp_all only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      first | rfl | (apply congrArg c; apply Fin.ext; dsimp; omega)

theorem child_zero {m j : ℕ} (hm : j ≤ m) (p : Palette m)
    (hp : p ∈ childColors m j hm) : p.2.val = 0 := by
  simp only [childColors, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | ⟨_, rfl⟩ <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem complete_new {m : ℕ} (U : TNEPath) (i j : ℕ) (hi : i ≤ U.steps.length)
    (hj : 0 < j) (hm : j ≤ m) (c : Coloring m U.steps.length)
    (k : Edge (insert U i (simpleRun j hj)))
    (hk : k ∉ Set.range (completeIndices U i j hi hj)) :
    (completeColoring j i hm U.steps c k).2.val = 0 := by
  have hlen : k.val < U.steps.length+j+1 := by
    have := k.isLt
    simp only [insert_steps, simpleRun_steps, List.length_append, List.length_take,
      List.length_cons, List.length_replicate, List.length_drop, Nat.min_eq_left hi] at this
    omega
  have hl : i ≤ k.val := by
    by_contra hn
    apply hk
    refine ⟨⟨k.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [completeIndices, Function.Embedding.coeFn_mk]
    split_ifs <;> omega
  have hr : k.val < i+j+1 := by
    by_contra hn
    apply hk
    refine ⟨⟨k.val-(j+1), by omega⟩, ?_⟩
    apply Fin.ext
    simp only [completeIndices, Function.Embedding.coeFn_mk]
    split_ifs <;> omega
  dsimp only [completeColoring, fromList, completeColors, splice]
  rw [List.getElem_append_left (by simp only [List.length_append, List.length_take,
    List.length_ofFn, Nat.min_eq_left hi, childColors, List.length_cons, List.length_replicate]; omega)]
  rw [List.getElem_append_right (show (List.take i (List.ofFn c)).length ≤ k.val from
    (by simpa only [List.length_take, List.length_ofFn, Nat.min_eq_left hi] using hl))]
  exact child_zero hm _ (List.getElem_mem _)

theorem complete_eq {m : ℕ} (U : TNEPath) (i j : ℕ) (hi : i ≤ U.steps.length)
    (hj : 0 < j) (hm : j ≤ m) (c : Coloring m U.steps.length) :
    KroneckerRecolorConstructions.complete U i j hi hj hm c =
      fromPalette (insert U i (simpleRun j hj)) (completeColoring j i hm U.steps c) := by
  apply fromPalette_recol_total
  · intro k
    rw [complete_copy U i j hi hj hm c k]
    exact respects_self _
  · exact complete_new U i j hi hj hm c

end KroneckerRecolOperations
