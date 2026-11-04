import KroneckerRawRunSteps

/-! Every legal run subsequence is completed by actual complete-run edits. -/
set_option autoImplicit false
namespace KroneckerSublistPrograms
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRawConcatenation
open KroneckerRawRunSteps

theorem sublist_program {m : ℕ} {X Y : List ℕ} (h : X.Sublist Y)
    (hY : ∀ r ∈ Y, 1 ≤ r ∧ r ≤ m-2) (pre post : List ℕ) :
    Nonempty (RawProgram m (runWord (pre++X++post)) (runWord (pre++Y++post))
      (Y.length-X.length) 0 0) := by
  induction h generalizing pre with
  | slnil => exact ⟨RawProgram.nil⟩
  | @cons X Y r h ih =>
    have hr := hY r (by simp)
    have htail : ∀ s ∈ Y, 1 ≤ s ∧ s ≤ m-2 := fun s hs => hY s (by simp [hs])
    obtain ⟨p⟩ := ih htail pre
    simp only [List.append_assoc] at p
    let q := insertCompleteRun pre (Y++post) r hr
    have hlen := h.length_le
    have he : Y.length-X.length+1=(r::Y).length-X.length := by simp only [List.length_cons]; omega
    exact ⟨by simpa only [List.append_assoc,List.cons_append,Nat.add_zero,he] using appendRaw p q⟩
  | @cons_cons X Y r h ih =>
    have htail : ∀ s ∈ Y, 1 ≤ s ∧ s ≤ m-2 := fun s hs => hY s (by simp [hs])
    obtain ⟨p⟩ := ih htail (pre++[r])
    exact ⟨by simpa only [List.append_assoc,List.singleton_append,List.length_cons,
      Nat.add_sub_add_right] using p⟩

end KroneckerSublistPrograms
