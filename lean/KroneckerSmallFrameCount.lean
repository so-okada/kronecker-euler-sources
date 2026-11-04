import KroneckerSmallFrameClassification

set_option autoImplicit false

namespace KroneckerSmallFrameClassification
noncomputable section
open KroneckerStack KroneckerWeights KroneckerColoring KroneckerWordCounts KroneckerPaperPathGradings
open scoped BigOperators

def shape : List Bool := [true, false, true, false, true, false]

def gradingA (m : ℕ) (hm : 3 ≤ m) : Grades m 6 :=
  ![⟨2, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨2, by omega⟩]

def gradingB (m : ℕ) (hm : 3 ≤ m) : Grades m 6 :=
  ![⟨3, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨2, by omega⟩]

def gradingC (m : ℕ) (hm : 3 ≤ m) : Grades m 6 :=
  ![⟨3, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩, ⟨1, by omega⟩]

theorem represented_word {m : ℕ} (g : Grades m 6) :
    word (pathShape shape) (representative g) =
      [.H (g 0).val, .V (g 1).val, .H (g 2).val, .V (g 3).val, .H (g 4).val, .V (g 5).val] := rfl

theorem grading_classification (m : ℕ) (hm : 3 ≤ m) (g : Grades m 6) :
    KroneckerPaperColors.ConnectedGrade (pathShape shape) 0 g ↔
      g = gradingA m hm ∨ g = gradingB m hm ∨ g = gradingC m hm := by
  rw [KroneckerPaperColors.connectedGrade_iff_operational, connected_iff,
    and_iff_left (word_grade_bounds (pathShape shape) (representative g)),
    represented_word, node_classification]
  constructor
  · intro h
    rcases h with h | h | h
    · left
      rcases h with ⟨h0,h2,h4,h1,h3,h5⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [gradingA]
    · right; left
      rcases h with ⟨h0,h2,h4,h1,h3,h5⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [gradingB]
    · right; right
      rcases h with ⟨h0,h2,h4,h1,h3,h5⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [gradingC]
  · rintro (rfl | rfl | rfl) <;> simp [threeCases, gradingA, gradingB, gradingC]

theorem three_run_count (m : ℕ) (hm : 3 ≤ m) :
    pathCount m shape 0 = m * (m.choose 2) ^ 2 + m.choose 3 * (m.choose 2 + m ^ 2) := by
  classical
  have hf : Finset.univ.filter (KroneckerPaperColors.ConnectedGrade (pathShape shape) 0) =
      ({gradingA m hm, gradingB m hm, gradingC m hm} : Finset (Grades m 6)) := by
    ext g
    simp [grading_classification m hm g]
  rw [KroneckerPaperColors.pathCount_binomial_sum, ← Finset.sum_filter]
  change (∑ a ∈ (Finset.univ.filter (KroneckerPaperColors.ConnectedGrade (pathShape shape) 0) :
    Finset (Grades m 6)), ∏ v : Fin 6, m.choose (a v).val) = _
  rw [hf]
  simp [Fin.prod_univ_succ, gradingA, gradingB, gradingC]
  ring

theorem geometric_three_run_count (m : ℕ) (hm : 3 ≤ m) :
    connectedCount m (KroneckerPaperPaths.power (KroneckerPaperPaths.simpleRun 1 (by decide)) 3) 0 =
      m * (m.choose 2) ^ 2 + m.choose 3 * (m.choose 2 + m ^ 2) := by
  rw [connectedCount_eq_pathCount]
  exact three_run_count m hm

theorem three_arrow_count :
    connectedCount 3 (KroneckerPaperPaths.power (KroneckerPaperPaths.simpleRun 1 (by decide)) 3) 0 = 39 := by
  rw [geometric_three_run_count 3 (by decide)]
  norm_num

end
end KroneckerSmallFrameClassification
