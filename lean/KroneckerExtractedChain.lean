import KroneckerHoleChains

/-! Extract ordered length-L holes separated by three guard runs; the final
hole absorbs the remaining word. Length hypotheses for exact recovery follow. -/
set_option autoImplicit false
namespace KroneckerExtractedChain
open KroneckerHoleGrammar KroneckerHoleChains

def extractChain (L : ℕ) : ℕ → List ℕ → List Piece
  | 0, X => [.hole X]
  | n+1, X =>
      .hole (X.take L) :: .guard ((X.drop L)[0]?.getD 0) ::
      .guard ((X.drop L)[1]?.getD 0) :: .guard ((X.drop L)[2]?.getD 0) ::
      extractChain L n (X.drop (L+3))

theorem extractChain_chain (L n : ℕ) (X : List ℕ) : Chain (extractChain L n X) (n+1) := by
  induction n generalizing X with
  | zero => exact Chain.one X
  | succ n ih => exact Chain.prepend _ _ _ _ (ih _)


end KroneckerExtractedChain
