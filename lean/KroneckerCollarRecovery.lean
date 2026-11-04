import KroneckerRunDeletionPosition
import KroneckerDrainingShell

/- Original module: KroneckerRunDeletionCount -/
section
/-! An unconditional one-deletion count inequality for actual run colorings. -/
set_option autoImplicit false
namespace KroneckerRunDeletionCount
open KroneckerWordCounts KroneckerColoredShell KroneckerDeletionColoring
open KroneckerRunDeletionPosition KroneckerDeletionCount KroneckerOrientationPositions KroneckerFiberBudget
open scoped BigOperators

theorem deletionPath_runWord (u v : ℕ) (A B : List ℕ) (r : ℕ) :
    deletionPath u v (runWord (A++(r+1)::B)) (runDeletionIndex A r)=
      runWord (u::(A++r::B)++[v]) := by
  obtain ⟨hi,_,he⟩ := runDeletion_data A B r
  unfold deletionPath
  rw [he,shellPath_runWord]

theorem run_deletion_count_bound {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (A B : List ℕ) (r : ℕ) :
    runCount m (A++(r+1)::B) c ≤ fiberBudget m (A.length+1+B.length) 1*
      ∑ h : Fin (m+1),runCount m (u::(A++r::B)++[v]) (c+h.val) := by
  obtain ⟨hi,hv',_⟩ := runDeletion_data A B r
  have h := deletion_count_bound u v c hu hv hm hpos _ (runDeletionIndex A r) hi hv'
  simpa [runCount,deletionPath_runWord,runWord_horizontal_count,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end KroneckerRunDeletionCount
end

/- Original module: KroneckerAutomaticShell -/
section
/-! A shell drains a positive surplus and preserves surplus zero, retaining every interior color. -/
set_option autoImplicit false
namespace KroneckerAutomaticShell
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell KroneckerDrainingShell

def autoColoring {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (U : List Bool) (g : Coloring m U.length) : Coloring m (shellPath u v U).length :=
  if c=0 then shellColoring u v (by omega) (by omega) (by omega) hv.1 U g
  else drainColoring u v (by omega) (by omega) hm hv.1 U g

theorem autoColoring_recover {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (U : List Bool) (g : Coloring m U.length) :
    recover u v U (autoColoring u v c hm hu hv U g)=g := by
  unfold autoColoring
  split
  · exact recover_shellColoring u v _ _ _ hv.1 U g
  · exact recover_drainColoring u v _ _ hm hv.1 U g

theorem autoColoring_connected {m : ℕ} (u v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1)
    (U : List Bool) (g : Coloring m U.length) (hg : Connected m (pathWord U g) c) :
    Connected m (pathWord (shellPath u v U) (autoColoring u v c hm hu hv U g)) (c-1) := by
  by_cases hc : c=0
  · subst c
    simpa [autoColoring] using shellColoring_connected hm hu hv U g hg
  · simpa [autoColoring,hc] using drainColoring_connected hm hu hv (by omega) U g hg

end KroneckerAutomaticShell
end

/- Original module: KroneckerCollarColoring -/
section
/-! An explicit sequence of prescribed shell pairs, ordered from outside to inside. -/
set_option autoImplicit false
namespace KroneckerCollarColoring
open KroneckerColoring KroneckerWordCounts KroneckerColoredShell KroneckerAutomaticShell

def LegalPairs (m : ℕ) (L : List (ℕ×ℕ)) : Prop :=
  ∀ p ∈ L,(1 ≤ p.1 ∧ p.1 ≤ m-1) ∧ (1 ≤ p.2 ∧ p.2 ≤ m-1)

def collarPath : List (ℕ×ℕ) → List Bool → List Bool
  | [],U => U
  | p::L,U => shellPath p.1 p.2 (collarPath L U)

def collarColoring {m : ℕ} (hm : 3 ≤ m) :
    (L : List (ℕ×ℕ)) → LegalPairs m L → (c : ℕ) → (U : List Bool) →
    Coloring m U.length → Coloring m (collarPath L U).length
  | [],_,_,_,g => g
  | p::L,hL,c,U,g => autoColoring p.1 p.2 (c-L.length) hm (hL p (by simp)).1
      (hL p (by simp)).2 (collarPath L U)
      (collarColoring hm L (fun q hq => hL q (by simp [hq])) c U g)

theorem collarPath_runWord (L : List (ℕ×ℕ)) (rs : List ℕ) :
    collarPath L (runWord rs)=runWord ((L.map Prod.fst)++rs++(L.map Prod.snd).reverse) := by
  induction L with
  | nil => simp [collarPath]
  | cons p L ih =>
    simp only [collarPath,ih,shellPath_runWord,List.map_cons,List.reverse_cons]
    simp [List.append_assoc]

end KroneckerCollarColoring
end

/- Original module: KroneckerCollarConnected -/
section
/-! Each prescribed collar layer removes one unit of positive surplus. -/
set_option autoImplicit false
namespace KroneckerCollarConnected
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerAutomaticShell KroneckerCollarColoring

theorem collarColoring_connected {m : ℕ} (hm : 3 ≤ m) (L : List (ℕ×ℕ))
    (hL : LegalPairs m L) (c : ℕ) (U : List Bool) (g : Coloring m U.length)
    (hg : Connected m (pathWord U g) c) :
    Connected m (pathWord (collarPath L U) (collarColoring hm L hL c U g)) (c-L.length) := by
  induction L with
  | nil => simpa [collarPath,collarColoring] using hg
  | cons p L ih =>
    have ht : LegalPairs m L := fun q hq => hL q (by simp [hq])
    have hh := autoColoring_connected p.1 p.2 (c-L.length) hm (hL p (by simp)).1
      (hL p (by simp)).2 (collarPath L U) (collarColoring hm L ht c U g) (ih ht)
    simpa only [collarPath,collarColoring,List.length_cons,Nat.sub_sub,Nat.add_comm] using hh

end KroneckerCollarConnected
end

/- Original module: KroneckerCollarRecovery -/
section
/-! Restriction through every prescribed collar recovers all input palettes. -/
set_option autoImplicit false
namespace KroneckerCollarRecovery
open KroneckerColoring KroneckerWordCounts KroneckerColoredShell KroneckerAutomaticShell KroneckerCollarColoring

def recoverCollar {m : ℕ} : (L : List (ℕ×ℕ)) → (U : List Bool) →
    Coloring m (collarPath L U).length → Coloring m U.length
  | [],_,g => g
  | p::L,U,g => recoverCollar L U (recover p.1 p.2 (collarPath L U) g)

theorem recover_collarColoring {m : ℕ} (hm : 3 ≤ m) (L : List (ℕ×ℕ))
    (hL : LegalPairs m L) (c : ℕ) (U : List Bool) (g : Coloring m U.length) :
    recoverCollar L U (collarColoring hm L hL c U g)=g := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [collarColoring,recoverCollar,autoColoring_recover]
    exact ih _

theorem collarColoring_injective {m : ℕ} (hm : 3 ≤ m) (L : List (ℕ×ℕ))
    (hL : LegalPairs m L) (c : ℕ) (U : List Bool) :
    Function.Injective (collarColoring hm L hL c U) :=
  Function.LeftInverse.injective (recover_collarColoring hm L hL c U)

end KroneckerCollarRecovery
end
