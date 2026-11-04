import KroneckerBinaryShell

/-! A colored draining shell lowers a positive surplus by one and retains
every interior palette entry. -/
set_option autoImplicit false
namespace KroneckerDrainingShell
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell

def drainColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (g : Coloring m U.length) :
    Coloring m (shellPath u v U).length :=
  KroneckerBinaryShell.binaryColoring u v hu hv hm hpos U [] g (fun i => Fin.elim0 i)

theorem drainColoring_word {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (g : Coloring m U.length) :
    pathWord (shellPath u v U) (drainColoring u v hu hv hm hpos U g) =
      shell u (v-1) 1 [(pathWord U g,c)] := by
  simpa [drainColoring, KroneckerBinaryShell.binaryPath, shellPath, shell, pathWord, word,
    List.append_assoc] using
    KroneckerBinaryShell.binaryColoring_word u v c 0 hu hv hm hpos U [] g (fun i => Fin.elim0 i)

theorem recover_drainColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (g : Coloring m U.length) :
    recover u v U (drainColoring u v hu hv hm hpos U g) = g :=
  KroneckerBinaryShell.recoverLeft_binaryColoring u v hu hv hm hpos U [] g _

theorem drainColoring_connected {m u v c : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (hc : 1 ≤ c)
    (U : List Bool) (g : Coloring m U.length) (hg : Connected m (pathWord U g) c) :
    Connected m (pathWord (shellPath u v U)
      (drainColoring u v (by omega) (by omega) hm hv.1 U g)) (c-1) := by
  rw [drainColoring_word u v c]
  have hs := manuscript_shell m u v 1 [(pathWord U g,c)] hm hu hv
    (by simpa using hg) (Or.inr ⟨by simp, rfl, by simpa using hc⟩)
  simpa using hs

def drainingShell {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (hc : 1 ≤ c) (U : List Bool) :
    ConnectedColorings m U c → ConnectedColorings m (shellPath u v U) (c-1) :=
  fun g => ⟨drainColoring u v (by omega) (by omega) hm hv.1 U g.val,
    drainColoring_connected hm hu hv hc U g.val g.property⟩

theorem drainingShell_injective {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (hc : 1 ≤ c) (U : List Bool) :
    Function.Injective (drainingShell u v c hm hu hv hc U) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg (fun z => recover u v U z.val) hxy
  simpa only [drainingShell, recover_drainColoring] using h

theorem draining_pathCount_le {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (hc : 1 ≤ c) (U : List Bool) :
    pathCount m U c ≤ pathCount m (shellPath u v U) (c-1) := by
  classical
  simp only [pathCount, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective (drainingShell u v c hm hu hv hc U)
    (drainingShell_injective u v c hm hu hv hc U)

theorem draining_runCount_le {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (hc : 1 ≤ c) (rs : List ℕ) :
    runCount m rs c ≤ runCount m (u :: rs ++ [v]) (c-1) := by
  simpa only [runCount, shellPath_runWord] using
    draining_pathCount_le u v c hm hu hv hc (runWord rs)

end KroneckerDrainingShell
