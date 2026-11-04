import Mathlib.Data.List.Basic

/-! Any period of at least two runs has two literal endpoint buffers. -/
set_option autoImplicit false
namespace KroneckerPeriodEndpoints

theorem period_endpoints (W : List ℕ) (hW : 2 ≤ W.length) :
    ∃ u v T, W=u::(T++[v]) := by
  cases W with
  | nil => simp at hW
  | cons u X =>
    have hx : X ≠ [] := by intro h; simp [h] at hW
    refine ⟨u,X.getLast hx,X.dropLast,?_⟩
    rw [List.dropLast_append_getLast hx]

end KroneckerPeriodEndpoints
