import KroneckerPeriodicWords
import Mathlib.Data.List.Rotate
import KroneckerOneRun
import KroneckerPreservingCollars

section

/-! Exact word identities exposing a periodic interior in a rotated word. -/
set_option autoImplicit false
namespace KroneckerRotatedWords
open KroneckerPeriodicWords

theorem repeat_conjugate (A B : List ℕ) (t : ℕ) :
    repeatRuns (B ++ A) (t+1) = B ++ repeatRuns (A ++ B) t ++ A := by
  induction t with
  | zero => simp [repeatRuns]
  | succ t ih =>
    rw [repeatRuns, ih, repeatRuns]
    simp [List.append_assoc]

theorem rotated_interior (A B : List ℕ) (t : ℕ) :
    repeatRuns (B ++ A) (t+3) =
      ((B ++ A) ++ B) ++ repeatRuns (A ++ B) t ++ (A ++ (B ++ A)) := by
  have h := repeatRuns_sandwich (B ++ A) (t+1) 0
  have hz : repeatRuns (B ++ A) 0 = [] := rfl
  simp only [hz, List.append_nil, Nat.add_zero] at h
  rw [show t+3 = (t+1)+2 by omega, ← h, repeat_conjugate]
  simp [List.append_assoc]

theorem rotated_collars_balanced (A B : List ℕ) :
    ((B ++ A) ++ B).length ≤ 2*(A ++ (B ++ A)).length ∧
      (A ++ (B ++ A)).length ≤ 2*((B ++ A) ++ B).length := by
  simp only [List.length_append]
  omega


end KroneckerRotatedWords
end

section

/- Original module: KroneckerUnequalContexts -/
section
/-! Prescribed (2,1) and (1,2) collar contexts preserve a connected surplus. -/
set_option autoImplicit false
namespace KroneckerUnequalContexts
open KroneckerWordCounts KroneckerBinaryShell KroneckerOneRun

theorem left_two_context (m u r v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hr : 1 ≤ r ∧ r ≤ m-1)
    (hv : 1 ≤ v ∧ v ≤ m-1) (rs : List ℕ) :
    runCount m rs c ≤ runCount m (u :: r :: rs ++ [v]) c := by
  have hbase := one_run_lower_bound (m := m) (r := r) hr.1 (by omega : r < m)
  have hpositive : 1 ≤ runCount m [r] 0 := by omega
  have hprod : runCount m rs c ≤ runCount m [r] 0 * runCount m rs c := by nlinarith
  have hs := binary_runCount_bound u v 0 c hm hu hv [r] rs
  simpa using hprod.trans hs

theorem right_two_context (m u r v c : ℕ) (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hr : 1 ≤ r ∧ r ≤ m-1)
    (hv : 1 ≤ v ∧ v ≤ m-1) (rs : List ℕ) :
    runCount m rs c ≤ runCount m (u :: rs ++ [r,v]) c := by
  have hbase := one_run_lower_bound (m := m) (r := r) hr.1 (by omega : r < m)
  have hpositive : 1 ≤ runCount m [r] 0 := by omega
  have hprod : runCount m rs c ≤ runCount m rs c * runCount m [r] 0 := by nlinarith
  have hs := binary_runCount_bound u v c 0 hm hu hv rs [r]
  simpa [List.append_assoc] using hprod.trans hs

end KroneckerUnequalContexts
end

/- Original module: KroneckerBalancedCollars -/
section
/-! Arbitrary prescribed collars with lengths within a factor of two. -/
set_option autoImplicit false
namespace KroneckerBalancedCollars
open KroneckerWordCounts KroneckerUnequalContexts KroneckerPreservingCollars

theorem balanced_collars_aux (m : ℕ) (hm : 3 ≤ m) (n : ℕ) :
    ∀ (A B : List ℕ), A.length+B.length=n →
      A.length ≤ 2*B.length → B.length ≤ 2*A.length →
      (∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) → (∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) →
      ∀ (rs : List ℕ) (c : ℕ), runCount m rs c ≤ runCount m (A ++ rs ++ B) c := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A B hn hAB hBA hA hB rs c
    by_cases heq : A.length = B.length
    · exact preserving_collars m hm A B heq hA hB rs c
    cases A with
    | nil =>
      simp only [List.length_nil, Nat.mul_zero] at hBA
      have hBnil : B = [] := List.length_eq_zero_iff.mp (by omega)
      simp [hBnil]
    | cons u A =>
      have hu := hA u (by simp)
      have hBne : B ≠ [] := by intro h; subst B; simp at hAB
      obtain ⟨Bs, v, htail⟩ : ∃ Bs v, B = Bs ++ [v] :=
        ⟨B.dropLast, B.getLast hBne, (List.dropLast_append_getLast hBne).symm⟩
      subst B
      have hv := hB v (by simp)
      simp only [List.length_cons, List.length_append] at hn hAB hBA heq
      by_cases hleft : Bs.length < A.length
      · cases A with
        | nil => simp at hleft
        | cons r As =>
          have hr := hA r (by simp)
          have hsmall : As.length+Bs.length<n := by simp at hn; omega
          have hinner := ih (As.length+Bs.length) hsmall As Bs rfl
            (by simp at hAB; omega) (by simp at hleft; omega)
            (fun t ht => hA t (by simp [ht])) (fun t ht => hB t (by simp [ht])) rs c
          have houter := left_two_context m u r v c hm hu hr hv (As ++ rs ++ Bs)
          simpa [List.append_assoc] using hinner.trans houter
      · have hright : A.length < Bs.length := by
          simp only [List.length_nil] at heq
          omega
        have hBsne : Bs ≠ [] := by intro h; subst Bs; simp at hright
        obtain ⟨Bt, r, ht⟩ : ∃ Bt r, Bs = Bt ++ [r] :=
          ⟨Bs.dropLast, Bs.getLast hBsne, (List.dropLast_append_getLast hBsne).symm⟩
        subst Bs
        have hr := hB r (by simp)
        have hsmall : A.length+Bt.length<n := by simp at hn; omega
        have hinner := ih (A.length+Bt.length) hsmall A Bt rfl
          (by simp at hright; omega) (by simp at hBA; omega)
          (fun t ht => hA t (by simp [ht])) (fun t ht => hB t (by simp [ht])) rs c
        have houter := right_two_context m u r v c hm hu hr hv (A ++ rs ++ Bt)
        simpa [List.append_assoc] using hinner.trans houter

theorem balanced_collars (m : ℕ) (hm : 3 ≤ m) (A B rs : List ℕ) (c : ℕ)
    (hAB : A.length ≤ 2*B.length) (hBA : B.length ≤ 2*A.length)
    (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) (hB : ∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) :
    runCount m rs c ≤ runCount m (A ++ rs ++ B) c :=
  balanced_collars_aux m hm (A.length+B.length) A B rfl hAB hBA hA hB rs c

end KroneckerBalancedCollars
end

/- Original module: KroneckerRotatedCounts -/
section
/-! A rotation of t+3 periods contains at least the colored count of t
unrotated periods, with a fixed prescribed prefix and suffix. -/
set_option autoImplicit false
namespace KroneckerRotatedCounts
open KroneckerWordCounts KroneckerPeriodicWords KroneckerRotatedWords KroneckerBalancedCollars

theorem conjugate_count_bound (m : ℕ) (hm : 3 ≤ m) (A B : List ℕ) (t c : ℕ)
    (hA : ∀ r ∈ A, 1 ≤ r ∧ r ≤ m-1) (hB : ∀ r ∈ B, 1 ≤ r ∧ r ≤ m-1) :
    runCount m (repeatRuns (A ++ B) t) c ≤ runCount m (repeatRuns (B ++ A) (t+3)) c := by
  rw [rotated_interior]
  apply balanced_collars m hm _ _ _ c
    (rotated_collars_balanced A B).1 (rotated_collars_balanced A B).2
  · intro r hr
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hB r hr
    · exact hA r hr
    · exact hB r hr
  · intro r hr
    simp only [List.mem_append] at hr
    rcases hr with hr | hr | hr
    · exact hA r hr
    · exact hB r hr
    · exact hA r hr

theorem rotation_count_bound (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (j t c : ℕ)
    (hj : j ≤ W.length) (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) :
    runCount m (repeatRuns W t) c ≤ runCount m (repeatRuns (W.rotate j) (t+3)) c := by
  have h := conjugate_count_bound m hm (W.take j) (W.drop j) t c
    (fun r h => hr r (List.mem_of_mem_take h)) (fun r h => hr r (List.mem_of_mem_drop h))
  simpa only [List.take_append_drop, List.rotate_eq_drop_append_take hj] using h

theorem periodic_hole_bound (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (j J : ℕ)
    (hj : j ≤ W.length) (hJ : 3 ≤ J) (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) :
    periodicCount m W (J-3) ≤ periodicCount m (W.rotate j) J := by
  have h := rotation_count_bound m hm W j (J-3) 0 hj hr
  have heq : J-3+3 = J := by omega
  simpa only [periodicCount, heq] using h

end KroneckerRotatedCounts
end
end

