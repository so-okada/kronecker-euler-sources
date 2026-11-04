import KroneckerMechanicalWindows

/-! Literal natural-valued mechanical run words, connected to the integer
floor increments without changing their values in the nonnegative regime. -/
set_option autoImplicit false
namespace KroneckerMechanicalWords
open KroneckerMechanicalRuns KroneckerMechanicalBounds

noncomputable def natRun (s u : ℝ) (i : ℕ) : ℕ := (mechanicalRun s u i).toNat

noncomputable def mechanicalWord (s u : ℝ) (start n : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => natRun s u (start+i.val))

theorem mechanical_nonnegative (s u : ℝ) (i : ℕ) (hs : 0 ≤ s) : 0 ≤ mechanicalRun s u i := by
  rw [mechanical_run_increment]
  have h := Int.floor_mono (show u+(i : ℝ)*s ≤ (u+(i : ℝ)*s)+s by linarith)
  omega

theorem natRun_cast (s u : ℝ) (i : ℕ) (hs : 0 ≤ s) : (natRun s u i : ℤ) = mechanicalRun s u i := by
  exact Int.toNat_of_nonneg (mechanical_nonnegative s u i hs)

theorem natRun_legal (s u : ℝ) (i M : ℕ) (hs : 1 ≤ s) (hM : s ≤ (M : ℝ)) :
    1 ≤ natRun s u i ∧ natRun s u i ≤ M := by
  have hi := mechanical_run_legal s u i M hs hM
  have hc := natRun_cast s u i (by linarith)
  omega

theorem mechanicalWord_length (s u : ℝ) (start n : ℕ) : (mechanicalWord s u start n).length = n := by
  simp [mechanicalWord]

theorem mechanicalWord_legal (s u : ℝ) (start n M : ℕ) (hs : 1 ≤ s) (hM : s ≤ (M : ℝ)) :
    ∀ r ∈ mechanicalWord s u start n, 1 ≤ r ∧ r ≤ M := by
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  exact natRun_legal s u (start+i.val) M hs hM

end KroneckerMechanicalWords
