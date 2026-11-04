import KroneckerGeometricOperations
import KroneckerRotatedCounts

set_option autoImplicit false

namespace KroneckerPaperPaths
open KroneckerWordCounts KroneckerPeriodicWords

theorem runPath_origin (rs : List ℕ) (o : LatticePoint) (hne : rs ≠ []) :
    (runPath rs o).origin = o := by
  apply ofSteps_origin_of_ne_nil
  intro h
  exact hne (runWord_injective h)

theorem exchangeRuns_adjacent (A B : List ℕ) (r s : ℕ) (o : LatticePoint) :
    exchangeRuns (runPath (A ++ [r, s] ++ B) o) A.length =
      runPath (A ++ [s, r] ++ B) o := by
  simp only [exchangeRuns, runPath_steps, decodeRuns_runWord]
  rw [runPath_origin _ o (by simp)]
  simp [List.append_assoc]

theorem exchangeRuns_involution (A B : List ℕ) (r s : ℕ) (o : LatticePoint) :
    exchangeRuns (exchangeRuns (runPath (A ++ [r, s] ++ B) o) A.length) A.length =
      runPath (A ++ [r, s] ++ B) o := by
  rw [exchangeRuns_adjacent, exchangeRuns_adjacent]

theorem exchangeRuns_origin (A B : List ℕ) (r s : ℕ) (o : LatticePoint) :
    (exchangeRuns (runPath (A ++ [r, s] ++ B) o) A.length).origin = o := by
  rw [exchangeRuns_adjacent, runPath_origin _ o (by simp)]

theorem rotateRuns_cut (rs : List ℕ) (o : LatticePoint) (j : ℕ) (hj : j ≤ rs.length) :
    rotateRuns (runPath rs o) j = concat (runPath (rs.drop j) o) (runPath (rs.take j) o) := by
  rw [rotateRuns_runPath, List.rotate_eq_drop_append_take hj, runPath_append]

theorem rotateRuns_origin (rs : List ℕ) (o : LatticePoint) (j : ℕ) (hne : rs ≠ []) :
    (rotateRuns (runPath rs o) j).origin = o := by
  rw [rotateRuns_runPath]
  apply runPath_origin
  intro h
  have he := congrArg List.length h
  simp only [List.length_rotate, List.length_nil] at he
  exact hne (List.length_eq_zero_iff.mp he)

@[simp] theorem rotateRuns_zero (rs : List ℕ) (o : LatticePoint) :
    rotateRuns (runPath rs o) 0 = runPath rs o := by
  simp [rotateRuns_runPath]

theorem rotateRuns_length (rs : List ℕ) (o : LatticePoint) :
    rotateRuns (runPath rs o) rs.length = runPath rs o := by
  simp [rotateRuns_runPath]

theorem runPath_east_count (rs : List ℕ) (o : LatticePoint) :
    (runPath rs o).steps.count true = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [runPath_steps, runWord, List.flatMap_cons, KroneckerStack.runShape,
      List.count_append, List.count_cons, List.length_cons] at ih ⊢
    simp [ih, List.count_replicate, Nat.add_comm]

theorem runPath_north_count (rs : List ℕ) (o : LatticePoint) :
    (runPath rs o).steps.count false = rs.sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [runPath_steps, runWord, List.flatMap_cons, KroneckerStack.runShape,
      List.count_append, List.count_cons, List.sum_cons] at ih ⊢
    simp [ih]

theorem rotation_preserves_counts (rs : List ℕ) (o : LatticePoint) (j : ℕ) :
    (rotateRuns (runPath rs o) j).steps.count true = (runPath rs o).steps.count true ∧
      (rotateRuns (runPath rs o) j).steps.count false = (runPath rs o).steps.count false := by
  simp only [rotateRuns_runPath, runPath_east_count, runPath_north_count, List.length_rotate]
  exact ⟨True.intro, (List.rotate_perm rs j).sum_eq⟩

theorem exchange_preserves_counts (A B : List ℕ) (r s : ℕ) (o : LatticePoint) :
    (exchangeRuns (runPath (A ++ [r,s] ++ B) o) A.length).steps.count true =
      (runPath (A ++ [r,s] ++ B) o).steps.count true ∧
    (exchangeRuns (runPath (A ++ [r,s] ++ B) o) A.length).steps.count false =
      (runPath (A ++ [r,s] ++ B) o).steps.count false := by
  rw [exchangeRuns_adjacent]
  simp only [runPath_east_count, runPath_north_count]
  simp [Nat.add_comm, Nat.add_left_comm]

end KroneckerPaperPaths
