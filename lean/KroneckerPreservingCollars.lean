import KroneckerColoredShell

/-! Prescribed equal-length collars around one connected colored word. -/
set_option autoImplicit false
namespace KroneckerPreservingCollars
open KroneckerWordCounts KroneckerColoredShell

theorem preserving_collars (m : ℕ) (hm : 3 ≤ m) (A : List ℕ) :
    ∀ (B : List ℕ), A.length = B.length →
      (∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) → (∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) →
      ∀ (rs : List ℕ) (c : ℕ),
      runCount m rs c ≤ runCount m (A ++ rs ++ B) c := by
  induction A with
  | nil =>
    intro B hlen _ _ rs c
    have hB : B = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    simp [hB]
  | cons u A ih =>
    intro B hlen hA hB rs c
    have hu := hA u (by simp)
    have hBne : B ≠ [] := by intro h; subst B; simp at hlen
    obtain ⟨Bs, v, htail⟩ : ∃ Bs v, B = Bs ++ [v] :=
      ⟨B.dropLast, B.getLast hBne, (List.dropLast_append_getLast hBne).symm⟩
    subst B
    have hv := hB v (by simp)
    have hsize : A.length = Bs.length := by simp at hlen; omega
    have hinner := ih Bs hsize (fun r h => hA r (by simp [h]))
      (fun r h => hB r (by simp [h])) rs c
    have houter := unary_runCount_le u v c hm hu hv (A ++ rs ++ Bs)
    simpa [List.append_assoc] using hinner.trans houter


end KroneckerPreservingCollars
