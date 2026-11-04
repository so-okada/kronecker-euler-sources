import KroneckerExtractedChain

/-! Exact recovery of the original word from extracted holes and guards. -/
set_option autoImplicit false
namespace KroneckerExtractedRecovery
open KroneckerHoleGrammar KroneckerExtractedChain

theorem three_guard_decompose (X : List ℕ) (h : 3 ≤ X.length) :
    [X[0]?.getD 0, X[1]?.getD 0, X[2]?.getD 0]++X.drop 3 = X := by
  cases X with
  | nil => simp at h
  | cons a X =>
    cases X with
    | nil => simp at h
    | cons b X =>
      cases X with
      | nil => simp at h
      | cons c X => rfl

theorem extractChain_expand (L n : ℕ) (X : List ℕ) (h : n*(L+3) ≤ X.length) :
    expand (extractChain L n X) = X := by
  induction n generalizing X with
  | zero => simp [extractChain, expand, pieceWord]
  | succ n ih =>
    have hlen : L+3 ≤ X.length := by nlinarith
    have htail : n*(L+3) ≤ (X.drop (L+3)).length := by
      simp only [List.length_drop]
      have hsum : n*(L+3)+(L+3) ≤ X.length := by nlinarith
      omega
    change X.take L ++ ((X.drop L)[0]?.getD 0 :: (X.drop L)[1]?.getD 0 ::
      (X.drop L)[2]?.getD 0 :: expand (extractChain L n (X.drop (L+3)))) = X
    rw [ih _ htail]
    have hd : X.drop (L+3) = (X.drop L).drop 3 := by simp only [List.drop_drop]
    rw [hd]
    have hg := three_guard_decompose (X.drop L) (by simp only [List.length_drop]; omega)
    change X.take L ++ ([_,_,_]++(X.drop L).drop 3) = X
    rw [hg]
    exact List.take_append_drop L X

end KroneckerExtractedRecovery
