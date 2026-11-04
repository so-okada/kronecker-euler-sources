import KroneckerManuscriptRecolorMaps
import KroneckerManuscriptShell

/-! Definition 3.1: `path` is the shell path and `GShell` is its shell grading.
GShell takes the concatenated path X, its grading f, and the number j of
input paths. Its five branches are equation (3.1), with zero-based indices.
No color choices enter this operator. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerManuscriptShell
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps

def path (X : TNEPath) (u v : ℕ) : TNEPath :=
  ofSteps (KroneckerColoredShell.shellPath u v X.steps) 0

theorem path_length (X : TNEPath) (u v : ℕ) :
    (path X u v).steps.length = u + 1 + X.steps.length + v + 1 := by
  simp only [path, ofSteps_steps, KroneckerColoredShell.shellPath,
    KroneckerStack.runShape, List.length_append, List.length_cons, List.length_replicate]
  omega

def GShell (X : TNEPath) (f : G X) (u v j ε : ℕ) : G (path X u v) := fun e =>
  let k := ((edgeEquiv (path X u v)).symm e).val
  if k = 0 then u + 1
  else if hk : u + 1 ≤ k ∧ k < u + 1 + X.steps.length then
    f (edgeEquiv X ⟨k - (u + 1), by omega⟩)
  else if k = u + 1 + X.steps.length then v - 1
  else if k + 1 = (path X u v).steps.length then j + 1 + ε
  else 0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem GShell_copy (X : TNEPath) (f : G X) (u v j ε : ℕ) (k : Edge X) :
    GShell X f u v j ε (edgeEquiv (path X u v) (shellIndices X u v k)) =
      f (edgeEquiv X k) := by
  have hk := k.isLt
  have hn : u + 1 + k.val ≠ 0 := by omega
  have hi : u + 1 ≤ u + 1 + k.val ∧ u + 1 + k.val < u + 1 + X.steps.length := by omega
  simp only [GShell, Equiv.symm_apply_apply, shellIndices, Function.Embedding.coeFn_mk,
    ite_eq_right hn, dite_eq_left hi]
  apply congrArg f
  apply congrArg (edgeEquiv X)
  apply Fin.ext
  dsimp
  omega

theorem GShell_first (X : TNEPath) (f : G X) (u v j ε : ℕ) :
    GShell X f u v j ε (edgeEquiv (path X u v) ⟨0, by rw [path_length]; omega⟩) = u + 1 := by
  simp [GShell]

theorem GShell_right (X : TNEPath) (f : G X) (u v j ε : ℕ) :
    GShell X f u v j ε (edgeEquiv (path X u v)
      ⟨u + 1 + X.steps.length, by rw [path_length]; omega⟩) = v - 1 := by
  simp [GShell]

theorem GShell_last (X : TNEPath) (f : G X) (u v j ε : ℕ) (hv : 1 ≤ v) :
    GShell X f u v j ε (edgeEquiv (path X u v)
      ⟨u + 1 + X.steps.length + v, by rw [path_length]; omega⟩) = j + 1 + ε := by
  have hn : u + 1 + X.steps.length + v ≠ 0 := by omega
  have hi : ¬ (u + 1 ≤ u + 1 + X.steps.length + v ∧
      u + 1 + X.steps.length + v < u + 1 + X.steps.length) := by omega
  have hr : u + 1 + X.steps.length + v ≠ u + 1 + X.steps.length := by omega
  simp [GShell, path_length, Nat.ne_of_gt (show 0 < v by omega)]

theorem GShell_bound {m : ℕ} (X : TNEPath) (f : G X) (hf : f ∈ G_h X m)
    (u v j ε : ℕ) (hu : u + 1 ≤ m) (hv : v - 1 ≤ m) (hl : j + 1 + ε ≤ m) :
    GShell X f u v j ε ∈ G_h (path X u v) m := by
  intro e
  dsimp only [GShell]
  split_ifs <;> first | exact hu | exact hv | exact hl | exact hf _ | omega

/-- Equation (3.3) for arbitrary j, including the empty concatenation. -/
def coloring {m : ℕ} (X : TNEPath) (f : G X) (η : Col X f m)
    (u v j ε : ℕ) (hu : u + 1 ≤ m) (hv : v - 1 ≤ m) (hl : j + 1 + ε ≤ m) :
    ColoredGrading m (path X u v) :=
  ⟨GShell X f u v j ε,
    Recol X (path X u v) (edgeCopy (shellIndices X u v)) (GShell X f u v j ε)
      (GShell_bound X f (color_grade_le η) u v j ε hu hv hl) f η⟩

theorem coloring_copy {m : ℕ} (X : TNEPath) (f : G X) (η : Col X f m)
    (u v j ε : ℕ) (hu : u + 1 ≤ m) (hv : v - 1 ≤ m) (hl : j + 1 + ε ≤ m)
    (k : Edge X) :
    ((coloring X f η u v j ε hu hv hl).2
      (edgeEquiv (path X u v) (shellIndices X u v k))).val = (η (edgeEquiv X k)).val :=
  copy_color (shellIndices X u v) (GShell X f u v j ε)
    (GShell_bound X f (color_grade_le η) u v j ε hu hv hl)
    f η k (GShell_copy X f u v j ε k)

/-- Lemma 3.3(4): restriction recovers the concatenated input colored grading. -/
theorem coloring_injective {m : ℕ} (X : TNEPath) (u v j ε : ℕ)
    (hu : u + 1 ≤ m) (hv : v - 1 ≤ m) (hl : j + 1 + ε ≤ m) :
    Function.Injective (fun c : ColoredGrading m X =>
      coloring X c.1 c.2 u v j ε hu hv hl) := by
  rintro ⟨f, η⟩ ⟨f', η'⟩ he
  have hf : f = f' := by
    funext e
    obtain ⟨k, rfl⟩ := (edgeEquiv X).surjective e
    have h := congrArg (fun c : ColoredGrading m (path X u v) =>
      c.1 (edgeEquiv (path X u v) (shellIndices X u v k))) he
    change GShell X f u v j ε _ = GShell X f' u v j ε _ at h
    simpa only [GShell_copy] using h
  subst f'
  have hc : η = η' := by
    funext e
    apply Subtype.ext
    obtain ⟨k, rfl⟩ := (edgeEquiv X).surjective e
    have h := congrArg (fun c : ColoredGrading m (path X u v) =>
      (c.2 (edgeEquiv (path X u v) (shellIndices X u v k))).val) he
    simpa only [coloring_copy] using h
  subst η'
  rfl

end KroneckerManuscriptShell
