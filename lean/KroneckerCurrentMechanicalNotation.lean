import KroneckerManuscriptExplicitNotation
import KroneckerMechanicalWordSums

/-! Definitions 5.2 and 5.4 in the 24 October manuscript.
`RunFactor` uses the manuscript's one-based first-run index.
`MechRunFactor` applies it to the finite prefix of the mechanical sequence.
The run phase is `KroneckerManuscriptMechanicalDefinitions.RunPhase`.
-/
set_option autoImplicit false
noncomputable section
namespace KroneckerCurrentMechanicalNotation
open KroneckerPaperPaths KroneckerWordCounts
open KroneckerManuscriptMechanicalDefinitions KroneckerMechanicalWords
open KroneckerMechanicalWordSums KroneckerFiniteWindows

def RunFactor (rs : List ℕ) (r ℓ : ℕ) (o : LatticePoint) : TNEPath :=
  ccsRunFactor rs (r-1) ℓ o

theorem RunFactor_steps (rs : List ℕ) (r ℓ : ℕ) (o : LatticePoint) :
    (RunFactor rs r ℓ o).steps = runWord ((rs.drop (r-1)).take ℓ) :=
  ccsRunFactor_steps rs (r-1) ℓ o

theorem RunFactor_horizontal_length (rs : List ℕ) (r ℓ : ℕ) (o : LatticePoint)
    (h : r-1+ℓ ≤ rs.length) :
    (RunFactor rs r ℓ o).steps.count true = ℓ :=
  ccsRunFactor_horizontal_length rs (r-1) ℓ o h

theorem RunFactor_vertical_length (rs : List ℕ) (r ℓ : ℕ) (o : LatticePoint) :
    (RunFactor rs r ℓ o).steps.count false = ((rs.drop (r-1)).take ℓ).sum :=
  ccsRunFactor_vertical_length rs (r-1) ℓ o

theorem RunFactor_one (rs : List ℕ) (o : LatticePoint) :
    RunFactor rs 1 rs.length o = runPath rs o := by
  simp only [RunFactor, Nat.sub_self, ccsRunFactor, Nat.zero_add,
    List.take_length, List.take_zero]
  change subpath (runPath rs o) 0 (runPath rs o).steps.length = runPath rs o
  have hfull (P : TNEPath) : subpath P 0 P.steps.length = P := by
    apply TNEPath.ext
    · simp
    · simp only [subpath, ofSteps, vertex, List.drop_zero, Nat.sub_zero,
        List.take_length, List.take_zero, displacement_nil, add_zero]
      split_ifs with h
      · exact (P.empty_origin h).symm
      · rfl
  exact hfull _

def MechRunFactor (σ u : ℝ) (r ℓ : ℕ) : TNEPath :=
  RunFactor (mechanicalWord σ u 0 (r-1+ℓ)) r ℓ 0

theorem MechRunFactor_one (σ u : ℝ) (T : ℕ) :
    MechRunFactor σ u 1 T = runPath (mechanicalWord σ u 0 T) 0 := by
  simpa only [MechRunFactor, Nat.sub_self, Nat.zero_add, mechanicalWord_length]
    using RunFactor_one (mechanicalWord σ u 0 T) 0

theorem MechRunFactor_steps (σ u : ℝ) (r ℓ : ℕ) :
    (MechRunFactor σ u r ℓ).steps = runWord (mechanicalWord σ u (r-1) ℓ) := by
  rw [MechRunFactor, RunFactor_steps, mechanicalWord_append]
  simp [mechanicalWord_length]
  rw [List.take_of_length_le (le_of_eq (mechanicalWord_length σ u (r-1) ℓ))]

/-- The explicit floor-prefix identity used in Lemma 5.3. -/
theorem MechRunFactor_vertical_length (σ u : ℝ) (r ℓ : ℕ) (hσ : 0 ≤ σ) :
    ((MechRunFactor σ u r ℓ).steps.count false : ℤ) =
      ⌊u + ((r-1+ℓ : ℕ) : ℝ)*σ⌋ - ⌊u + ((r-1 : ℕ) : ℝ)*σ⌋ := by
  rw [MechRunFactor_steps]
  have h := runPath_north_count (mechanicalWord σ u (r-1) ℓ) 0
  rw [show (runWord (mechanicalWord σ u (r-1) ℓ)).count false =
      (mechanicalWord σ u (r-1) ℓ).sum from h]
  exact mechanicalWord_sum_cast σ u (r-1) ℓ hσ

/-- Both the numerator p and denominator q are arguments of D_bad. -/
abbrev Dbad (rs : List ℕ) (p : ℤ) (q : ℕ) : ℕ := badWordWindows rs p q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem Dbad_formula (rs : List ℕ) (p : ℤ) (q : ℕ) (o : LatticePoint) :
    Dbad rs p q = ((Finset.range (rs.length+1-q)).filter
      (fun i => ((RunFactor rs (i+1) q o).steps.count false : ℤ) ≠ p)).card := by
  simp only [Dbad, badWordWindows, RunFactor_vertical_length,
    Nat.add_sub_cancel, wordWindowSum]

end KroneckerCurrentMechanicalNotation
