import KroneckerExample25Classification
import KroneckerSourceNaturalGradings
import KroneckerFiniteCoefficientIntegration

/-! Example 2.19: exact binomial count, including grades exceeding m,
whose binomial factors vanish; the three-arrow Euler value follows from
exactly the existing finite-model interfaces. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerExample25
open KroneckerStack KroneckerWeights KroneckerColoring KroneckerWordCounts
open KroneckerSourceGradingDictionary KroneckerSourceBinomialTruncation
open KroneckerPaperColors KroneckerSourceGradeBounds
attribute [local instance] Classical.propDecidable
open scoped BigOperators

def shape : List Bool := [true,false,false,true,false,false,true,false]

def g0 : Grades 5 8 := ![3, 0, 0, 2, 0, 0, 0, 2]

def g1 : Grades 5 8 := ![4, 0, 0, 1, 0, 0, 0, 2]

def g2 : Grades 5 8 := ![4, 0, 0, 1, 0, 1, 0, 1]

def g3 : Grades 5 8 := ![5, 0, 0, 0, 0, 0, 0, 2]

def g4 : Grades 5 8 := ![5, 0, 0, 0, 1, 0, 0, 1]

def g5 : Grades 5 8 := ![5, 0, 0, 0, 0, 1, 0, 1]

theorem represented_word {m : ℕ} (g : Grades m 8) :
    word (pathShape shape) (representative g) =
      [.H (g 0).val, .V (g 1).val, .V (g 2).val, .H (g 3).val,
       .V (g 4).val, .V (g 5).val, .H (g 6).val, .V (g 7).val] := rfl

theorem grading_classification (g : Grades 5 8) :
    ConnectedGrade (pathShape shape) 0 g ↔
      g = g0 ∨ g = g1 ∨ g = g2 ∨ g = g3 ∨ g = g4 ∨ g = g5 := by
  rw [connectedGrade_iff_operational, connected_iff,
    and_iff_left (word_grade_bounds (pathShape shape) (representative g)),
    represented_word, node_classification]
  constructor
  · intro h
    rcases h with h0 | h1 | h2 | h3 | h4 | h5
    · left
      rcases h0 with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [g0]
    · right; left
      rcases h1 with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [g1]
    · right; right; left
      rcases h2 with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [g2]
    · right; right; right; left
      rcases h3 with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [g3]
    · right; right; right; right; left
      rcases h4 with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [g4]
    · right; right; right; right; right; 
      rcases h5 with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> simp_all [g5]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [sixCases, g0, g1, g2, g3, g4, g5]

theorem grading_bound {m : ℕ} (g : Grades m 8)
    (hg : ConnectedGrade (pathShape shape) 0 g) : Within 5 g := by
  have hn := connected_node ((connectedGrade_iff_operational _ _ g).mp hg)
  rw [represented_word, node_classification] at hn
  rcases hn with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ | ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ | ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ | ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ | ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ | ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ <;>
    intro i <;> fin_cases i <;> simp_all

theorem connected_congr {K M : ℕ} {g : Grades K 8} {h : Grades M 8}
    (he : ∀ i, (g i).val = (h i).val) :
    ConnectedGrade (pathShape shape) 0 g ↔ ConnectedGrade (pathShape shape) 0 h := by
  unfold ConnectedGrade
  rw [rawTrace_congr (pathShape shape) he]

theorem fixed_sum (m : ℕ) :
    (∑ g : Grades 5 8, if ConnectedGrade (pathShape shape) 0 g then binomialWeight m g else 0) =
      m.choose 3 * (m.choose 2)^2 + m * m.choose 4 * (m.choose 2 + m^2) +
        m.choose 5 * (m.choose 2 + 2*m^2) := by
  classical
  have hf : Finset.univ.filter (ConnectedGrade (pathShape shape) 0) =
      ({g0, g1, g2, g3, g4, g5} : Finset (Grades 5 8)) := by
    ext g
    simp [grading_classification]
  rw [← Finset.sum_filter, hf]
  simp [binomialWeight, Fin.prod_univ_succ, g0, g1, g2, g3, g4, g5]
  ring

theorem count (m : ℕ) :
    pathCount m shape 0 =
      m.choose 3 * (m.choose 2)^2 + m * m.choose 4 * (m.choose 2 + m^2) +
        m.choose 5 * (m.choose 2 + 2*m^2) := by
  classical
  let L := max m 5
  have hmL : m ≤ L := le_max_left _ _
  have h5L : 5 ≤ L := le_max_right _ _
  have hmcut := finite_sum_restrict (N := 8) hmL (ConnectedGrade (pathShape shape) 0)
  have h5cut := sum_restrict_of_zero (N := 8) h5L
    (fun g => if ConnectedGrade (pathShape shape) 0 g then binomialWeight m g else 0)
    (by
      intro g hn
      split_ifs with hg
      · exact False.elim (hn (grading_bound g hg))
      · rfl)
  have hcong_m : ∀ g : Grades m 8,
      ConnectedGrade (pathShape shape) 0 (embed hmL g) ↔ ConnectedGrade (pathShape shape) 0 g :=
    fun _ => connected_congr (fun _ => rfl)
  have hcong_5 : ∀ g : Grades 5 8,
      ConnectedGrade (pathShape shape) 0 (embed h5L g) ↔ ConnectedGrade (pathShape shape) 0 g :=
    fun _ => connected_congr (fun _ => rfl)
  simp only [hcong_m, weight] at hmcut
  simp only [hcong_5, weight_embed] at h5cut
  rw [pathCount_binomial_sum]
  change (∑ g : Grades m 8, if ConnectedGrade (pathShape shape) 0 g then
    ∏ i : Fin 8, m.choose (g i).val else 0) = _
  exact hmcut.symm.trans (h5cut.trans (fixed_sum m))

theorem three_arrow_count : pathCount 3 shape 0 = 9 := by
  rw [count]
  norm_num [Nat.choose]

theorem geometric_count (m : ℕ) (o : KroneckerPaperPaths.LatticePoint) :
    KroneckerPaperPathGradings.connectedCount m (KroneckerPaperPaths.runPath [2,2,1] o) 0 =
      m.choose 3 * (m.choose 2)^2 + m * m.choose 4 * (m.choose 2 + m^2) +
        m.choose 5 * (m.choose 2 + 2*m^2) := by
  rw [KroneckerPaperPathGradings.connectedCount_runPath]
  exact count m

def parameters : KroneckerFrameIdentity.Parameters where
  m := 3
  a := 2
  b := 5
  d₁ := 3
  d₂ := 7
  k := 2
  hm := by decide
  ha := by decide
  hab := by decide
  coprime := by decide
  hd₁ := by decide
  hd₂ := by decide
  determinant := by norm_num
  length_eq := rfl

theorem frame_word : KroneckerFrameBadDensity.frameWord 2 5 3 = [2,2,1] := by
  norm_num [KroneckerFrameBadDensity.frameWord, KroneckerMechanicalWords.mechanicalWord,
    KroneckerMechanicalWords.natRun, KroneckerMechanicalRuns.mechanicalRun,
    KroneckerMechanicalRuns.mechanicalPrefix, KroneckerFrameSlope.frameSlope,
    List.range_succ, Int.toNat]

theorem euler (G : KroneckerScopedModuli.Geometry)
    (S : KroneckerFiniteCoefficientIntegration.FiniteEnumeration G) :
    KroneckerManuscriptTarget.euler (KroneckerScopedCanonicalPublishedEuler.family G) 3 2 5 = 3 := by
  have h := KroneckerScopedActualFrameApplication.literal_identity G
    (KroneckerFiniteCoefficientIntegration.application G S) parameters
  change (runCount 3 (KroneckerFrameBadDensity.frameWord 2 5 3) 0 : ℤ) =
    3 * KroneckerManuscriptTarget.euler (KroneckerScopedCanonicalPublishedEuler.family G) 3 2 5 at h
  rw [frame_word] at h
  have hc : runCount 3 [2,2,1] 0 = 9 := three_arrow_count
  rw [hc] at h
  omega

end KroneckerExample25
