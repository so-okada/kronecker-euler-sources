import KroneckerBinaryShell

/- Original module: KroneckerCollars -/
section
/-! Prescribed collars with equal numbers of runs around two colored interiors. -/
set_option autoImplicit false
namespace KroneckerCollars
open KroneckerWordCounts KroneckerColoredShell KroneckerBinaryShell

theorem collar_runCount_bound (m : ℕ) (hm : 3 ≤ m) (A : List ℕ) :
    ∀ (B : List ℕ), A ≠ [] → A.length = B.length →
      (∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) → (∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) →
      ∀ (xs ys : List ℕ) (c d : ℕ),
      runCount m xs c * runCount m ys d ≤ runCount m (A ++ xs ++ ys ++ B) (c+d) := by
  induction A with
  | nil =>
    intro B hne
    exact (hne rfl).elim
  | cons u A ih =>
    intro B _ hlen hA hB xs ys c d
    have hu := hA u (by simp)
    have hBne : B ≠ [] := by intro h; subst B; simp at hlen
    obtain ⟨Bs, v, htail⟩ : ∃ Bs v, B = Bs ++ [v] :=
      ⟨B.dropLast, B.getLast hBne, (List.dropLast_append_getLast hBne).symm⟩
    subst B
    have hv := hB v (by simp)
    have hsize : A.length = Bs.length := by simp at hlen; omega
    by_cases hAs : A = []
    · subst A
      have hBs : Bs = [] := List.length_eq_zero_iff.mp (by simpa using hsize.symm)
      subst Bs
      simpa [List.append_assoc] using binary_runCount_bound u v c d hm hu hv xs ys
    · have hinner := ih Bs hAs hsize
        (fun r h => hA r (by simp [h])) (fun r h => hB r (by simp [h])) xs ys c d
      have houter := unary_runCount_le u v (c+d) hm hu hv (A ++ xs ++ ys ++ Bs)
      simpa [List.append_assoc] using hinner.trans houter

/-- The same prescribed word on both sides, as needed for periodic growth. -/
theorem sandwich_runCount_bound (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (xs ys : List ℕ) (c d : ℕ) :
    runCount m xs c * runCount m ys d ≤ runCount m (W ++ xs ++ ys ++ W) (c+d) :=
  collar_runCount_bound m hm W W hne rfl hr hr xs ys c d

end KroneckerCollars
end

/- Original module: KroneckerPeriodicWords -/
section
/-! Literal repetitions of a run word and the concrete periodic count sequence. -/
set_option autoImplicit false
namespace KroneckerPeriodicWords
open KroneckerWordCounts KroneckerCollars

def repeatRuns (W : List ℕ) : ℕ → List ℕ
  | 0 => []
  | j+1 => repeatRuns W j ++ W

theorem repeatRuns_length (W : List ℕ) (j : ℕ) :
    (repeatRuns W j).length = j * W.length := by
  induction j with
  | zero => simp [repeatRuns]
  | succ j ih => simp [repeatRuns, ih, Nat.add_mul]

theorem repeatRuns_add (W : List ℕ) (i j : ℕ) :
    repeatRuns W (i+j) = repeatRuns W i ++ repeatRuns W j := by
  induction j with
  | zero => simp [repeatRuns]
  | succ j ih => simp [repeatRuns, ih, List.append_assoc]

theorem repeatRuns_succ_left (W : List ℕ) (j : ℕ) :
    repeatRuns W (j+1) = W ++ repeatRuns W j := by
  simpa [Nat.add_comm, repeatRuns] using repeatRuns_add W 1 j

theorem mem_repeatRuns (W : List ℕ) (j : ℕ) {r : ℕ}
    (h : r ∈ repeatRuns W j) : r ∈ W := by
  induction j with
  | zero => simp [repeatRuns] at h
  | succ j ih =>
    simp only [repeatRuns, List.mem_append] at h
    exact h.elim ih id

theorem repeatRuns_ne_nil (W : List ℕ) (hne : W ≠ []) (j : ℕ) (hj : 1 ≤ j) :
    repeatRuns W j ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [repeatRuns_length]
  exact Nat.mul_pos (by omega) (List.length_pos_iff.mpr hne)

theorem repeatRuns_sandwich (W : List ℕ) (i j : ℕ) :
    W ++ repeatRuns W i ++ repeatRuns W j ++ W = repeatRuns W (i+j+2) := by
  rw [← repeatRuns_succ_left, ← repeatRuns_add]
  change repeatRuns W (i+1+j+1) = repeatRuns W (i+j+2)
  congr 1
  omega

noncomputable def periodicCount (m : ℕ) (W : List ℕ) (j : ℕ) : ℕ :=
  runCount m (repeatRuns W j) 0

theorem periodicCount_zero (m : ℕ) (W : List ℕ) : periodicCount m W 0 = 0 := by
  simp [periodicCount, repeatRuns, runCount_nil]

/-- Shifted supermultiplicativity for the actual finite colored counts.
The statement also covers index zero, where the corresponding count is zero. -/
theorem periodicCount_supermultiplicative (m : ℕ) (hm : 3 ≤ m)
    (W : List ℕ) (hne : W ≠ []) (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (i j : ℕ) :
    periodicCount m W i * periodicCount m W j ≤ periodicCount m W (i+j+2) := by
  simpa only [periodicCount, repeatRuns_sandwich, Nat.add_zero] using
    sandwich_runCount_bound m hm W hne hr (repeatRuns W i) (repeatRuns W j) 0 0

end KroneckerPeriodicWords
end
