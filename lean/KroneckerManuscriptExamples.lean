import KroneckerSmallFrameCount
import KroneckerFiniteCoefficientIntegration

set_option autoImplicit false

namespace KroneckerManuscriptExamples
noncomputable section
open KroneckerPaperPaths KroneckerPaperPathGradings KroneckerWeights
open KroneckerWordCounts KroneckerSourceGradingDictionary KroneckerColoring

def balancePath : TNEPath := ofSteps [true, true, false, true, false] 0

def balanceGrades : Grades 3 5 := ![2, 0, 1, 1, 2]

def balanceColors : KroneckerPaperColors.PaperColorFiber balanceGrades :=
  fun i => ⟨(![3, 1, 2, 1, 3] : Fin 5 → ℕ) i, by
    fin_cases i <;> norm_num [balanceGrades]⟩

def balanceGrading : ColoredGrading 3 balancePath :=
  (coloredGradingEquiv 3 balancePath).symm ⟨balanceGrades, balanceColors⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem example_boundary_balances (i : Fin 6) :
    boundaryBalance balanceGrading.1 i = (![0, 1, 2, 1, 2, 0] : Fin 6 → ℤ) i := by
  unfold boundaryBalance balanceGrading
  rw [coloredGradingEquiv_symm_grades]
  fin_cases i <;> norm_num [balancePath, balanceGrades, rawTrace,
    KroneckerCompatibility.balance, KroneckerCompatibility.walk, pathShape,
    KroneckerStack.Edge.credit, Finset.sum_range_succ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem example_edge_balances (i : Fin 5) :
    edgeBalance balanceGrading.1 (edgeEquiv balancePath i) =
      (![1, 2, 1, 2, 0] : Fin 5 → ℤ) i := by
  simp only [edgeBalance, Equiv.symm_apply_apply]
  rw [example_boundary_balances]
  fin_cases i <;> rfl

def predecessorWord (i : Fin 5) : KroneckerStack.Edge :=
  if i.val = 0 then .H 2 else if i.val = 1 then .H 1 else .V 0

def predecessorTable (i : Fin 5) : Fin 5 := if i.val = 2 then 1 else 0

theorem example_predecessor_valid :
    KroneckerPredecessor.ValidThrough predecessorWord predecessorTable 5 := by
  have hu : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
  simp [KroneckerPredecessor.ValidThrough, Fin.forall_fin_succ,
    predecessorWord, predecessorTable, KroneckerPredecessor.IsHorizontal,
    KroneckerPredecessor.load, KroneckerPredecessor.prefixEdges,
    KroneckerStack.Edge.grade, hu]
  norm_num [Finset.filter_insert, Finset.filter_singleton, Fin.lt_def]

theorem example_predecessor_values (p : Fin 5 → Fin 5)
    (hp : KroneckerPredecessor.ValidThrough predecessorWord p 5) :
    p 2 = 1 ∧ p 3 = 0 ∧ p 4 = 0 := by
  have h := KroneckerPredecessor.valid_unique predecessorWord p predecessorTable hp
    example_predecessor_valid
  exact ⟨h 2 (by decide) (by decide), h 3 (by decide) (by decide),
    h 4 (by decide) (by decide)⟩

def smallFrame : KroneckerFrameIdentity.Parameters where
  m := 3
  a := 2
  b := 3
  d₁ := 3
  d₂ := 4
  k := 1
  hm := by decide
  ha := by decide
  hab := by decide
  coprime := by decide
  hd₁ := by decide
  hd₂ := by decide
  determinant := by norm_num
  length_eq := rfl

theorem small_frame_word : KroneckerFrameBadDensity.frameWord 2 3 3 = [1, 1, 1] := by
  norm_num [KroneckerFrameBadDensity.frameWord, KroneckerMechanicalWords.mechanicalWord,
    KroneckerMechanicalWords.natRun, KroneckerMechanicalRuns.mechanicalRun,
    KroneckerMechanicalRuns.mechanicalPrefix, KroneckerFrameSlope.frameSlope,
    List.range_succ]

theorem small_frame_euler (G : KroneckerScopedModuli.Geometry)
    (S : KroneckerFiniteCoefficientIntegration.FiniteEnumeration G) :
    KroneckerManuscriptTarget.euler (KroneckerScopedCanonicalPublishedEuler.family G) 3 2 3 = 13 := by
  have h := KroneckerScopedActualFrameApplication.literal_identity G
    (KroneckerFiniteCoefficientIntegration.application G S) smallFrame
  change (runCount 3 (KroneckerFrameBadDensity.frameWord 2 3 3) 0 : ℤ) =
    3 * KroneckerManuscriptTarget.euler (KroneckerScopedCanonicalPublishedEuler.family G) 3 2 3 at h
  rw [small_frame_word] at h
  have hc := KroneckerSmallFrameClassification.three_run_count 3 (by decide)
  have hc' : runCount 3 [1, 1, 1] 0 = 39 := by
    norm_num [KroneckerSmallFrameClassification.shape] at hc
    exact hc
  rw [hc'] at h
  omega

end
end KroneckerManuscriptExamples
