import KroneckerRotatedCounts

/- Original module: KroneckerCyclicEmbedding -/
section
/-! A cyclic period power embeds into two-ended completion of the canonical period. -/
set_option autoImplicit false
namespace KroneckerCyclicEmbedding
open KroneckerPeriodicWords KroneckerRotatedWords

theorem conjugate_completion (A B : List ℕ) (n : ℕ) :
    A++repeatRuns (B++A) (n+1)++B=repeatRuns (A++B) (n+2) := by
  rw [repeat_conjugate]
  have h := repeatRuns_sandwich (A++B) n 0
  simpa [repeatRuns,List.append_assoc] using h

theorem rotated_power_sublist (W : List ℕ) (j n : ℕ) (hj : j ≤ W.length) :
    (repeatRuns (W.rotate j) (n+1)).Sublist (repeatRuns W (n+2)) := by
  rw [List.rotate_eq_drop_append_take hj]
  have h := (List.sublist_append_right (W.take j) (repeatRuns (W.drop j++W.take j) (n+1))).append_right (W.drop j)
  have h' := (List.sublist_append_left (repeatRuns (W.drop j++W.take j) (n+1)) (W.drop j)).trans h
  rw [conjugate_completion,List.take_append_drop] at h'
  exact h'

end KroneckerCyclicEmbedding
end

/- Original module: KroneckerPhasePieces -/
section
/-! An exact finite periodic piece records its rotation, full periods and remainder. -/
set_option autoImplicit false
namespace KroneckerPhasePieces
open KroneckerPeriodicWords

def PhasePiece (W X : List ℕ) : Prop :=
  ∃ j n r, j ≤ W.length ∧ r < W.length ∧
    X=repeatRuns (W.rotate j) n++(W.rotate j).take r

theorem phase_piece_length (W : List ℕ) (j n r : ℕ) (hr : r < W.length) :
    (repeatRuns (W.rotate j) n++(W.rotate j).take r).length=n*W.length+r := by
  simp only [List.length_append,repeatRuns_length,List.length_rotate,List.length_take]
  rw [Nat.min_eq_left hr.le]

end KroneckerPhasePieces
end
