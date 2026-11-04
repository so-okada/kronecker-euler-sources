import KroneckerPeriodicWords

/-! A fixed explicit collar choice for periodic completion; no asymptotic choices. -/
set_option autoImplicit false
namespace KroneckerCompletionPadding

def completionPadding (m q K : ℕ) : ℕ := K+2*q+m
def completionIndex (m q n t : ℕ) : ℕ := t+2+2*completionPadding m q (t*q-n)


theorem completion_index_positive (m q n t : ℕ) : 1 ≤ completionIndex m q n t := by
  unfold completionIndex
  omega


end KroneckerCompletionPadding
