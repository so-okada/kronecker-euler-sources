import KroneckerPaperNotation
import KroneckerPaperConnected
import KroneckerWordCounts

/-!
# Binomial colors for literal connected gradings

The counted objects here are pairs of an uncolored grading and a color
function with labels from one through the corresponding binomial coefficient.
Connectedness is the literal predecessor/node predicate and depends only on
the grading. The surplus is the terminal balance minus one.
-/
set_option autoImplicit false
namespace KroneckerPaperColors
noncomputable section

open KroneckerStack KroneckerColoring KroneckerWeights
open KroneckerSourceGradingDictionary
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The paper's positive integer color labels for a given uncolored grading. -/
abbrev PaperColorFiber {m n : ℕ} (g : Grades m n) :=
  (v : Fin n) → {c : ℕ // 1 ≤ c ∧ c ≤ Nat.choose m (g v).val}

/-- A colored grading is the pair of its grade function and color function. -/
abbrev PaperColoredGrading (m n : ℕ) := (g : Grades m n) × PaperColorFiber g

def colorFiberEquiv {m n : ℕ} (g : Grades m n) :
    ColorFiber g ≃ PaperColorFiber g :=
  Equiv.piCongrRight fun v => KroneckerPaper.paperColorEquiv (Nat.choose m (g v).val)

def coloringEquiv (m n : ℕ) : Coloring m n ≃ PaperColoredGrading m n :=
  (KroneckerWeights.colorEquiv m n).trans
    (Equiv.sigmaCongrRight fun g => colorFiberEquiv g)

@[simp] theorem coloringEquiv_grades {m n : ℕ} (c : Coloring m n) :
    (coloringEquiv m n c).1 = grades c := rfl

@[simp] theorem coloringEquiv_symm_grades {m n : ℕ} (c : PaperColoredGrading m n) :
    grades ((coloringEquiv m n).symm c) = c.1 := rfl

/-- Literal connectedness with the specified integer surplus. -/
def ConnectedGrade {m n : ℕ} (shape : ℕ → Bool) (d : ℕ) (g : Grades m n) : Prop :=
  KroneckerPaperConnected.Connected (rawTrace shape g) n ∧
    KroneckerCompatibility.balance (rawTrace shape g) n = (d : ℤ) + 1

/-- Terminal balance minus one is precisely the paper's surplus formula. -/
theorem surplus_formula {m n : ℕ} (shape : ℕ → Bool) (g : Grades m n) :
    KroneckerCompatibility.balance (rawTrace shape g) n - 1 =
      HEdges shape n - 1 - VTotal shape (representative g) := by
  have h := KroneckerSourceIntervalCounts.balance_interval
    (trace shape (representative g)) 0 n (Nat.zero_le n)
  rw [hCount_edges, vWeight_total] at h
  simp only [KroneckerCompatibility.balance, KroneckerCompatibility.walk,
    sub_zero] at h
  rw [raw_eq_representative]
  change KroneckerCompatibility.walk Edge.credit (trace shape (representative g)) n - 1 = _
  omega

theorem connectedGrade_iff_surplus {m n : ℕ} (shape : ℕ → Bool) (d : ℕ)
    (g : Grades m n) : ConnectedGrade shape d g ↔
      KroneckerPaperConnected.Connected (rawTrace shape g) n ∧
        HEdges shape n - 1 - VTotal shape (representative g) = (d : ℤ) := by
  have hr := surplus_formula shape g
  unfold ConnectedGrade
  constructor <;> rintro ⟨hc, hd⟩ <;> exact ⟨hc, by omega⟩

/-- The exact colored set appearing in the manuscript's C_d(U). -/
abbrev ConnectedColorings {m n : ℕ} (shape : ℕ → Bool) (d : ℕ) :=
  {c : PaperColoredGrading m n // ConnectedGrade shape d c.1}

def connectedColoringEquiv {m n : ℕ} (shape : ℕ → Bool) (d : ℕ) :
    {c : Coloring m n // ConnectedGrade shape d (grades c)} ≃
      @ConnectedColorings m n shape d where
  toFun c := ⟨coloringEquiv m n c.val, c.property⟩
  invFun c := ⟨(coloringEquiv m n).symm c.val, c.property⟩
  left_inv c := by
    apply Subtype.ext
    exact (coloringEquiv m n).left_inv c.val
  right_inv c := by
    apply Subtype.ext
    exact (coloringEquiv m n).right_inv c.val

theorem grading_color_count {m n : ℕ} (g : Grades m n) :
    Nat.card (PaperColorFiber g) = ∏ v : Fin n, Nat.choose m (g v).val := by
  rw [Nat.card_congr (colorFiberEquiv g).symm, Nat.card_eq_fintype_card]
  exact KroneckerPaper.grading_color_count g

/-- Colors impose no extra condition on a literal connected grading. -/
theorem literal_connected_colored_count {m n : ℕ} (shape : ℕ → Bool) (d : ℕ) :
    Nat.card (@ConnectedColorings m n shape d) =
      weightedCount (ConnectedGrade (m := m) (n := n) shape d) := by
  rw [Nat.card_congr (connectedColoringEquiv (m := m) (n := n) shape d).symm]
  exact colored_count (ConnectedGrade shape d)

/-- The binomial product formula for the literal connected colored set. -/
theorem literal_connected_binomial_sum {m n : ℕ} (shape : ℕ → Bool) (d : ℕ) :
    Nat.card (@ConnectedColorings m n shape d) =
      ∑ g : Grades m n, if ConnectedGrade shape d g then
        ∏ v : Fin n, Nat.choose m (g v).val else 0 := by
  classical
  exact literal_connected_colored_count shape d

theorem wordList_rawTrace {m n : ℕ} (shape : ℕ → Bool) (g : Grades m n) :
    KroneckerPaperConnected.wordList (rawTrace shape g) n =
      word shape (representative g) := by
  rw [KroneckerPaperConnected.wordList,
    KroneckerPaperExecutionTrace.orderedList_eq_segment, raw_eq_representative]
  exact (word_eq_segment shape (representative g)).symm

/-- Literal connectedness and its specified surplus agree with acceptance
for every bounded uncolored grading. -/
theorem connectedGrade_iff_operational {m n : ℕ} (shape : ℕ → Bool)
    (d : ℕ) (g : Grades m n) :
    ConnectedGrade shape d g ↔
      KroneckerStack.Connected m (word shape (representative g)) d := by
  have hlegal : ∀ e ∈ KroneckerPaperConnected.wordList (rawTrace shape g) n,
      e.grade ≤ m := by
    rw [wordList_rawTrace]
    exact word_grade_bounds shape (representative g)
  simpa only [ConnectedGrade, wordList_rawTrace] using
    KroneckerPaperConnected.connected_surplus_iff (c := d) hlegal

theorem colored_connected_iff_operational {m n : ℕ} (shape : ℕ → Bool)
    (d : ℕ) (c : Coloring m n) :
    ConnectedGrade shape d (grades c) ↔
      KroneckerStack.Connected m (word shape c) d :=
  connectedGrade_iff_operational shape d (grades c)

/-- An explicit equivalence of the literal colored set and the
operational colored set; this transfers cardinalities without identifying
different predicates by a notation alias. -/
def operationalColoringEquiv {m n : ℕ} (shape : ℕ → Bool) (d : ℕ) :
    @ConnectedColorings m n shape d ≃
      {c : Coloring m n // KroneckerStack.Connected m (word shape c) d} :=
  (connectedColoringEquiv shape d).symm.trans
    { toFun := fun c => ⟨c.val, (colored_connected_iff_operational shape d c.val).mp c.property⟩
      invFun := fun c => ⟨c.val, (colored_connected_iff_operational shape d c.val).mpr c.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem literal_count_eq_operational {m n : ℕ} (shape : ℕ → Bool) (d : ℕ) :
    Nat.card (@ConnectedColorings m n shape d) =
      Nat.card {c : Coloring m n // KroneckerStack.Connected m (word shape c) d} :=
  Nat.card_congr (operationalColoringEquiv shape d)

/-- For an arbitrary finite character word, the manuscript's literal colored
count equals the operational path count used by the entropy theorems. -/
theorem literal_count_eq_pathCount (m d : ℕ) (U : List Bool) :
    Nat.card (@ConnectedColorings m U.length (KroneckerWordCounts.pathShape U) d) =
      KroneckerWordCounts.pathCount m U d :=
  literal_count_eq_operational (KroneckerWordCounts.pathShape U) d

theorem pathCount_binomial_sum (m d : ℕ) (U : List Bool) :
    KroneckerWordCounts.pathCount m U d =
      ∑ g : Grades m U.length,
        if ConnectedGrade (KroneckerWordCounts.pathShape U) d g then
          ∏ v : Fin U.length, Nat.choose m (g v).val else 0 := by
  rw [← literal_count_eq_pathCount m d U]
  exact literal_connected_binomial_sum (KroneckerWordCounts.pathShape U) d

end
end KroneckerPaperColors
