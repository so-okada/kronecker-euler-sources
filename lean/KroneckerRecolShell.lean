import KroneckerRecolOperations
import KroneckerExplicitShellCorrespondence
import KroneckerDrainingShell

set_option autoImplicit false
noncomputable section
namespace KroneckerRecolShell
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerColoring KroneckerColoredShell KroneckerRecolPaletteBridge
open KroneckerExplicitShellCorrespondence

theorem gradedWord_fromPalette {m : ℕ} (X : TNEPath) (c : Coloring m X.steps.length) :
    gradedWord X (fromPalette X c).1 = KroneckerWordCounts.pathWord X.steps c := by
  apply List.ext_getElem
  · simp [KroneckerWordCounts.pathWord_length]
  · intro k hk hl
    have hx : k < X.steps.length := by simpa using hk
    simp only [gradedWord, List.getElem_ofFn, fromPalette_grade]
    rw [KroneckerPathWordIndex.pathWord_getElem X.steps c k hx]
    cases h : X.steps[k] <;> simp [paint]

theorem gradedWord_injective (X : TNEPath) : Function.Injective (gradedWord X) := by
  intro f g h
  funext e
  let k := (edgeEquiv X).symm e
  have he := congrArg (fun w : List KroneckerStack.Edge => w[k.val]?) h
  simp only [gradedWord, List.getElem?_ofFn, dite_eq_left k.isLt, Option.some.injEq] at he
  have hk : edgeEquiv X k = e := (edgeEquiv X).apply_symm_apply e
  cases hb : X.steps[k.val] <;> simpa [hb, hk] using he

def tailColors (m v t : ℕ) (hv : v-1 ≤ m) (ht : t ≤ m) : List (Palette m) :=
  fixedColor m (v-1) hv :: (List.replicate (v-1) (zeroColor m) ++ [fixedColor m t ht])

def shellPalette {m : ℕ} (X : TNEPath) (u v t : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (ht : t ≤ m) (hpos : 1 ≤ v) (c : Coloring m X.steps.length) :
    Coloring m (KroneckerManuscriptShell.path X u v).steps.length :=
  fromList (prefixColors m u hu ++ (List.ofFn c ++ tailColors m v t hv ht)) (by
    simp only [prefixColors, tailColors, List.length_append, List.length_cons,
      List.length_replicate, List.length_nil, List.length_ofFn,
      KroneckerManuscriptShell.path_length]
    omega)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem shellPalette_copy {m : ℕ} (X : TNEPath) (u v t : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (ht : t ≤ m) (hpos : 1 ≤ v) (c : Coloring m X.steps.length)
    (k : Edge X) : shellPalette X u v t hu hv ht hpos c (shellIndices X u v k) = c k := by
  simp only [shellPalette, fromList, shellIndices, Function.Embedding.coeFn_mk]
  rw [List.getElem_append_right (by simp [prefixColors])]
  simp [prefixColors, List.getElem_append_left, k.isLt]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem shellPalette_new {m : ℕ} (X : TNEPath) (u v t : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (ht : t ≤ m) (hpos : 1 ≤ v) (c : Coloring m X.steps.length)
    (k : Edge (KroneckerManuscriptShell.path X u v)) (hk : k ∉ Set.range (shellIndices X u v)) :
    (shellPalette X u v t hu hv ht hpos c k).2.val = 0 := by
  by_cases hl : k.val < u+1
  · dsimp only [shellPalette, fromList]
    rw [List.getElem_append_left (by simpa [prefixColors] using hl)]
    exact KroneckerRecolOperations.prefix_zero hu _ (List.getElem_mem _)
  · have hr : u+1+X.steps.length ≤ k.val := by
      by_contra hn
      apply hk
      refine ⟨⟨k.val-(u+1), by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [shellIndices]
      omega
    dsimp only [shellPalette, fromList]
    rw [List.getElem_append_right (by simpa [prefixColors] using (Nat.le_of_not_gt hl))]
    rw [List.getElem_append_right (by simp only [List.length_ofFn, prefixColors,
      List.length_cons, List.length_replicate]; omega)]
    have tail_zero (p : Palette m) (hp : p ∈ tailColors m v t hv ht) : p.2.val = 0 := by
      simp only [tailColors, List.mem_cons, List.mem_append, List.mem_replicate,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | ⟨_, rfl⟩ | rfl <;> rfl
    exact tail_zero _ (List.getElem_mem _)

theorem tail_word (m v t : ℕ) (hv : v-1 ≤ m) (ht : t ≤ m) (hpos : 1 ≤ v) :
    List.zipWith paint (KroneckerStack.runShape v) (tailColors m v t hv ht) =
      .H (v-1) :: (List.replicate (v-1) (.V 0) ++ [.V t]) := by
  have hrep : List.replicate v false = List.replicate (v-1) false ++ [false] := by
    rw [← List.replicate_succ']
    congr 1
    omega
  simp only [KroneckerStack.runShape, tailColors, List.zipWith_cons_cons, hrep]
  rw [List.zipWith_append (by simp)]
  simp [paint]

theorem shellPalette_word {m : ℕ} (X : TNEPath) (u v t : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (ht : t ≤ m) (hpos : 1 ≤ v) (c : Coloring m X.steps.length) :
    KroneckerWordCounts.pathWord (KroneckerManuscriptShell.path X u v).steps
      (shellPalette X u v t hu hv ht hpos c) =
      [.H (u+1)] ++ List.replicate u (.V 0) ++ KroneckerWordCounts.pathWord X.steps c ++
      [.H (v-1)] ++ List.replicate (v-1) (.V 0) ++ [.V t] := by
  rw [shellPalette, fromList_word]
  change List.zipWith paint (shellPath u v X.steps) _ = _
  unfold shellPath
  rw [List.zipWith_append (prefix_length m u hu).symm]
  rw [List.zipWith_append (by simp)]
  rw [prefix_word, tail_word _ _ _ _ _ hpos, ← word_zip]
  simp [List.append_assoc]

/-- The piecewise manuscript grading equals the operational palette grading. -/
theorem shellPalette_grade {m : ℕ} (X : TNEPath) (u v j ε : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (ht : j+1+ε ≤ m) (hpos : 1 ≤ v) (c : Coloring m X.steps.length) :
    KroneckerManuscriptShell.GShell X (fromPalette X c).1 u v j ε =
      (fromPalette _ (shellPalette X u v (j+1+ε) hu hv ht hpos c)).1 := by
  apply gradedWord_injective
  rw [gradedWord_shell _ _ _ _ _ _ hpos, gradedWord_fromPalette,
    gradedWord_fromPalette, shellPalette_word]

/-- Full colored equality for every permitted arity and final shell grade. -/
theorem explicit_shell_eq {m : ℕ} (X : TNEPath) (u v j ε : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (ht : j+1+ε ≤ m) (hpos : 1 ≤ v) (c : Coloring m X.steps.length) :
    KroneckerManuscriptShell.coloring X (fromPalette X c).1 (fromPalette X c).2
      u v j ε hu hv ht =
      fromPalette _ (shellPalette X u v (j+1+ε) hu hv ht hpos c) := by
  have h (f : G (KroneckerManuscriptShell.path X u v)) (hf : f ∈ G_h _ m)
      (he : f = (fromPalette _ (shellPalette X u v (j+1+ε) hu hv ht hpos c)).1) :
      (⟨f, Recol X _ (edgeCopy (shellIndices X u v)) f hf
        (fromPalette X c).1 (fromPalette X c).2⟩ : ColoredGrading m (KroneckerManuscriptShell.path X u v)) =
        fromPalette _ (shellPalette X u v (j+1+ε) hu hv ht hpos c) := by
    subst f
    apply fromPalette_recol_total
    · intro k
      exact (congrArg (RespectsRecol (c k))
        (shellPalette_copy X u v (j+1+ε) hu hv ht hpos c k)).mpr (respects_self _)
    · exact shellPalette_new X u v (j+1+ε) hu hv ht hpos c
  exact h _ _ (shellPalette_grade X u v j ε hu hv ht hpos c)

@[simp] theorem shellPalette_preserve {m : ℕ} (X : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (ht : 2 ≤ m) (hpos : 1 ≤ v) (c : Coloring m X.steps.length) :
    shellPalette X u v 2 hu hv ht hpos c = shellColoring u v hu hv ht hpos X.steps c := rfl

@[simp] theorem shellPalette_drain {m : ℕ} (X : TNEPath) (u v : ℕ) (hu : u+1 ≤ m)
    (hv : v-1 ≤ m) (ht : 3 ≤ m) (hpos : 1 ≤ v) (c : Coloring m X.steps.length) :
    shellPalette X u v 3 hu hv ht hpos c =
      KroneckerDrainingShell.drainColoring u v hu hv ht hpos X.steps c := by
  funext k
  simp [shellPalette, fromList, tailColors, KroneckerDrainingShell.drainColoring,
    KroneckerBinaryShell.binaryColoring, KroneckerBinaryShell.binaryColors,
    KroneckerBinaryShell.suffixColors]

end KroneckerRecolShell
