import KroneckerBoundaryVisits
import KroneckerNormalizationPrograms

section

/- Original module: KroneckerMechanicalBoundaryCost -/
section
/-! The local mechanical edit cost is at most twice the number of boundary visits. -/
set_option autoImplicit false
namespace KroneckerMechanicalBoundaryCost
open KroneckerMechanicalRuns KroneckerMechanicalVariation KroneckerAlignedOrbitError
open KroneckerBoundaryVisits

theorem mechanical_boundary_cost (s u t v ε : ℝ) (n : ℕ)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) (hε : ε ≤ 1)
    (hclose : |u-v|+(n : ℝ)*|s-t| < ε) :
    (∑ i ∈ Finset.range n, |(mechanicalRun s u i : ℝ)-(mechanicalRun t v i : ℝ)|) ≤
      2*(visits s u ε n : ℝ) := by
  have h := discrepancy_mass_le_visits s u t v ε n hε
    (fun i hi => block_orbit_error s u t v ε n (i+1) (by omega) hclose)
  exact (mechanical_variation s u t v n hu hv).trans (by linarith)

end KroneckerMechanicalBoundaryCost
end

/- Original module: KroneckerPairedRunCosts -/
section
/-! Exact directed costs for changing a run list into an equally long prescribed run list. -/
set_option autoImplicit false
namespace KroneckerPairedRunCosts

def rises (X Y : List ℕ) : ℕ := (List.zipWith (fun r s => s-r) X Y).sum
def falls (X Y : List ℕ) : ℕ := rises Y X
def cost (X Y : List ℕ) : ℕ := rises X Y+falls X Y

theorem directed_cost_real (r s : ℕ) :
    ((s-r : ℕ) : ℝ)+((r-s : ℕ) : ℝ)=|(r : ℝ)-(s : ℝ)| := by
  rcases le_total r s with h|h
  · rw [Nat.sub_eq_zero_of_le h,Nat.cast_zero,add_zero,Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.sub_eq_zero_of_le h,Nat.cast_zero,zero_add,Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

theorem paired_cost_real (X Y : List ℕ) :
    (cost X Y : ℝ)=(List.zipWith (fun r s : ℕ => |(r : ℝ)-(s : ℝ)|) X Y).sum := by
  induction X generalizing Y with
  | nil => simp [cost,rises,falls]
  | cons r X ih =>
    cases Y with
    | nil => simp [cost,rises,falls]
    | cons s Y =>
      have h := ih Y
      simp only [cost,falls,rises,List.zipWith_cons_cons,List.sum_cons,Nat.cast_add] at h ⊢
      linarith [directed_cost_real r s]

end KroneckerPairedRunCosts
end

/- Original module: KroneckerPairedRunPrograms -/
section
/-! Actual deterministic vertical edit programs realize the exact paired costs. -/
set_option autoImplicit false
namespace KroneckerPairedRunPrograms
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRawConcatenation
open KroneckerAdjustRun KroneckerPairedRunCosts

theorem paired_program (m : ℕ) (X Y pre : List ℕ) (hlen : X.length=Y.length) :
    Nonempty (RawProgram m (runWord (pre++X)) (runWord (pre++Y)) 0 (rises X Y) (falls X Y)) := by
  induction X generalizing Y pre with
  | nil =>
    have hy : Y=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst Y
    exact ⟨RawProgram.nil⟩
  | cons r X ih =>
    cases Y with
    | nil => simp at hlen
    | cons s Y =>
      obtain ⟨p⟩ := ih Y (pre++[s]) (by simpa using hlen)
      simp only [List.append_assoc,List.singleton_append] at p
      obtain ⟨q⟩ := adjust_run_exists m pre X r s
      exact ⟨by simpa [rises,falls] using appendRaw q p⟩

end KroneckerPairedRunPrograms
end
end

section

/-! Costs add over aligned concatenated blocks, with the alignment hypothesis explicit. -/
set_option autoImplicit false
namespace KroneckerPairedCostsAppend
open KroneckerPairedRunCosts

theorem rises_append (X Y A B : List ℕ) (h : X.length=Y.length) :
    rises (X++A) (Y++B)=rises X Y+rises A B := by
  simp only [rises,List.zipWith_append h,List.sum_append]

theorem falls_append (X Y A B : List ℕ) (h : X.length=Y.length) :
    falls (X++A) (Y++B)=falls X Y+falls A B := by
  exact rises_append Y X B A h.symm

theorem cost_append (X Y A B : List ℕ) (h : X.length=Y.length) :
    cost (X++A) (Y++B)=cost X Y+cost A B := by
  unfold cost
  rw [rises_append X Y A B h,falls_append X Y A B h]
  omega

end KroneckerPairedCostsAppend
end

section

/-! The list edit cost equals the floor-increment discrepancy sum exactly. -/
set_option autoImplicit false
namespace KroneckerPairedMechanicalCost
open KroneckerPairedRunCosts KroneckerPairedCostsAppend KroneckerMechanicalRuns
open KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem paired_mechanical_cost (s u t v : ℝ) (n : ℕ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (cost (mechanicalWord s u 0 n) (mechanicalWord t v 0 n) : ℝ) =
      ∑ i ∈ Finset.range n, |(mechanicalRun s u i : ℝ)-(mechanicalRun t v i : ℝ)| := by
  induction n with
  | zero => simp [cost,rises,falls,mechanicalWord]
  | succ n ih =>
    rw [mechanicalWord_append s u 0 n 1,mechanicalWord_append t v 0 n 1,
      cost_append _ _ _ _ (by simp [mechanicalWord_length]),Nat.cast_add,ih,
      mechanicalWord_one,mechanicalWord_one,paired_cost_real,Finset.sum_range_succ]
    simp only [Nat.zero_add,List.zipWith_cons_cons,List.zipWith_nil_left,List.sum_cons,List.sum_nil,add_zero]
    have h₁ : (natRun s u n : ℝ)=(mechanicalRun s u n : ℝ) := by
      exact_mod_cast natRun_cast s u n hs
    have h₂ : (natRun t v n : ℝ)=(mechanicalRun t v n : ℝ) := by
      exact_mod_cast natRun_cast t v n ht
    rw [h₁,h₂]

end KroneckerPairedMechanicalCost
end

