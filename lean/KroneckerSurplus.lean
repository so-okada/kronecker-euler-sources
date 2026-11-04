import KroneckerHPrecursor

/-! Manuscript notation for the surplus of a path equipped with a grading. -/
namespace KroneckerPaperPathGradings
noncomputable section
open KroneckerPaperPaths KroneckerWeights KroneckerSourceGradingDictionary

/-- Surplus: number of horizontal edges minus one minus the total vertical grade. -/
def Surp {m : ℕ} (U : TNEPath) (g : Grading m U) : ℤ := surplus g

theorem surp_formula {m : ℕ} (U : TNEPath) (g : Grading m U) :
    Surp U g = KroneckerColoring.HEdges (KroneckerWordCounts.pathShape U.steps) U.steps.length - 1 -
      KroneckerColoring.VTotal (KroneckerWordCounts.pathShape U.steps)
        (representative (gradingEquiv m U g)) := surplus_formula g

theorem connectedGrade_surp {m : ℕ} {U : TNEPath} {d : ℕ}
    {g : Grading m U} (h : ConnectedGrade d g) : Surp U g = (d : ℤ) :=
  connectedGrade_surplus h

theorem connectedGrade_surp_nonnegative {m : ℕ} {U : TNEPath} {d : ℕ}
    {g : Grading m U} (h : ConnectedGrade d g) : 0 ≤ Surp U g := by
  rw [connectedGrade_surp h]
  exact Int.natCast_nonneg d

@[simp] theorem surp_translate {m : ℕ} (U : TNEPath) (g : Grading m U)
    (t : ℤ × ℤ) : Surp (translate U t) (translateGrading g t) = Surp U g :=
  surplus_translate g t

end
end KroneckerPaperPathGradings
