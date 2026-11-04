import KroneckerPhasePieces

/- Original module: KroneckerCompletionConcatenation -/
section
/-! Subsequences of two period powers concatenate inside their summed power. -/
set_option autoImplicit false
namespace KroneckerCompletionConcatenation
open KroneckerPeriodicWords

theorem completion_append (W X Y : List ℕ) (s t : ℕ)
    (hX : X.Sublist (repeatRuns W s)) (hY : Y.Sublist (repeatRuns W t)) :
    (X++Y).Sublist (repeatRuns W (s+t)) := by
  rw [repeatRuns_add]
  exact hX.append hY

end KroneckerCompletionConcatenation
end

/- Original module: KroneckerPhasePieceCompletion -/
section
/-! Every periodic piece can be completed at a cost of at most two periods. -/
set_option autoImplicit false
namespace KroneckerPhasePieceCompletion
open KroneckerPeriodicWords KroneckerCyclicEmbedding KroneckerPhasePieces

theorem phase_piece_completion (W X : List ℕ) (h : PhasePiece W X) :
    ∃ t, X.Sublist (repeatRuns W t) ∧ t*W.length ≤ X.length+2*W.length := by
  obtain ⟨j,n,r,hj,hr,rfl⟩ := h
  refine ⟨n+2,?_,?_⟩
  · have hs := (List.Sublist.refl (repeatRuns (W.rotate j) n)).append
      (List.take_sublist r (W.rotate j))
    change (repeatRuns (W.rotate j) n++(W.rotate j).take r).Sublist
      (repeatRuns (W.rotate j) (n+1)) at hs
    exact hs.trans (rotated_power_sublist W j n hj)
  · rw [phase_piece_length W j n r hr]
    nlinarith

end KroneckerPhasePieceCompletion
end

/- Original module: KroneckerPiecesCompletion -/
section
/-! Complete any finite concatenation of periodic pieces with a linear piece budget. -/
set_option autoImplicit false
namespace KroneckerPiecesCompletion
open KroneckerPeriodicWords KroneckerPhasePieces KroneckerPhasePieceCompletion
open KroneckerCompletionConcatenation

theorem pieces_completion (W : List ℕ) (pieces : List (List ℕ))
    (h : ∀ X ∈ pieces, PhasePiece W X) :
    ∃ t, pieces.flatten.Sublist (repeatRuns W t) ∧
      t*W.length ≤ pieces.flatten.length+2*W.length*pieces.length := by
  induction pieces with
  | nil => exact ⟨0,List.Sublist.refl [],by simp⟩
  | cons X pieces ih =>
    obtain ⟨s,hs,hslen⟩ := phase_piece_completion W X (h X (by simp))
    obtain ⟨t,ht,htlen⟩ := ih (fun Y hY => h Y (by simp [hY]))
    refine ⟨s+t,?_,?_⟩
    · simpa only [List.flatten_cons] using completion_append W X pieces.flatten s t hs ht
    · simp only [List.flatten_cons,List.length_append,List.length_cons]
      nlinarith

end KroneckerPiecesCompletion
end
