import KroneckerManuscriptGradingSets
import KroneckerRecoveryCode

/-! Grade differences on surviving edges and the recovery vector.
Both arguments of Diff are gradings on the same geometric path.
A partial edge correspondence is extended by grade zero at deleted edges. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths

/-- The grading called h-hat in the recovery proof. -/
def recoveryGrading {U V : TNEPath}
    (correspondence : GeomEdge U → Option (GeomEdge V)) (h : G V) : G U :=
  fun e => match correspondence e with
    | some f => h f
    | none => 0

theorem recoveryGrading_surviving {U V : TNEPath}
    (correspondence : GeomEdge U → Option (GeomEdge V)) (h : G V)
    (e : GeomEdge U) (f : GeomEdge V) (he : correspondence e = some f) :
    recoveryGrading correspondence h e = h f := by
  simp [recoveryGrading, he]

theorem recoveryGrading_deleted {U V : TNEPath}
    (correspondence : GeomEdge U → Option (GeomEdge V)) (h : G V)
    (e : GeomEdge U) (he : correspondence e = none) :
    recoveryGrading correspondence h e = 0 := by
  simp [recoveryGrading, he]

theorem Diff_surviving {U V : TNEPath}
    (correspondence : GeomEdge U → Option (GeomEdge V)) (g : G U) (h : G V)
    (e : GeomEdge U) (f : GeomEdge V) (he : correspondence e = some f) :
    Diff U g (recoveryGrading correspondence h) e = (g e : ℤ) - (h f : ℤ) := by
  rw [Diff, recoveryGrading_surviving correspondence h e f he]

/-- Integer differences coincide with the natural-number recovery entries
when the corresponding grade does not increase. -/
theorem Diff_natCast (U : TNEPath) (g h : G U) (e : GeomEdge U)
    (hle : h e ≤ g e) : Diff U g h e = ((g e - h e : ℕ) : ℤ) := by
  unfold Diff
  omega

def gradeDifferenceVector {U : TNEPath} {n D : ℕ}
    (g h : G U) (edges : Fin n → GeomEdge U)
    (budget : ∑ i, (g (edges i) - h (edges i)) ≤ D) :
    KroneckerDecrementSlack.Decrements n D :=
  ⟨fun i => g (edges i) - h (edges i), budget⟩

theorem gradeDifferenceVector_spec {U : TNEPath} {n D : ℕ}
    (g h : G U) (edges : Fin n → GeomEdge U)
    (budget : ∑ i, (g (edges i) - h (edges i)) ≤ D)
    (hle : ∀ i, h (edges i) ≤ g (edges i)) (i : Fin n) :
    ((gradeDifferenceVector g h edges budget).val i : ℤ) =
      Diff U g h (edges i) := (Diff_natCast U g h (edges i) (hle i)).symm

theorem gradeDifferenceVector_recovery {U : TNEPath} {n D : ℕ}
    (g h : G U) (edges : Fin n → GeomEdge U)
    (budget : ∑ i, (g (edges i) - h (edges i)) ≤ D)
    (hle : ∀ i, h (edges i) ≤ g (edges i)) (i : Fin n) :
    g (edges i) = h (edges i) + (gradeDifferenceVector g h edges budget).val i := by
  have hi := hle i
  change g (edges i) = h (edges i) + (g (edges i) - h (edges i))
  omega

theorem gradeDifferenceVector_card (n D : ℕ) :
    Fintype.card (KroneckerDecrementSlack.Decrements n D) = (n+D).choose D :=
  KroneckerDecrementCardinality.decrements_card n D

end KroneckerNaturalPathGradings
