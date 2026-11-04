import KroneckerTight

/-! Literal finite paths and run-word colored counts.

The edge orientations are data of a finite list. The counted objects are the
existing finite binomial colorings satisfying the existing stack predicate.
No enumeration or growth estimate is introduced as a hypothesis.
-/
set_option autoImplicit false
namespace KroneckerWordCounts
open KroneckerStack KroneckerColoring KroneckerWeights KroneckerTight

/-- Extend the literal finite orientation list beyond its end by vertical edges.
Only values strictly before its length are used to form the colored word. -/
def pathShape (U : List Bool) (i : ℕ) : Bool := U.getD i false

def pathWord {m : ℕ} (U : List Bool) (g : Coloring m U.length) : List Edge :=
  word (pathShape U) g

/-- The actual finite set counted by the manuscript's C_c(U). -/
abbrev ConnectedColorings (m : ℕ) (U : List Bool) (c : ℕ) :=
  {g : Coloring m U.length // Connected m (pathWord U g) c}

noncomputable def pathCount (m : ℕ) (U : List Bool) (c : ℕ) : ℕ :=
  Nat.card (ConnectedColorings m U c)

def runWord (rs : List ℕ) : List Bool := rs.flatMap runShape

noncomputable def runCount (m : ℕ) (rs : List ℕ) (c : ℕ) : ℕ :=
  pathCount m (runWord rs) c

@[simp]
theorem paint_orientation {m : ℕ} (h : Bool) (x : Palette m) :
    (paint h x).isHorizontal = h := by
  cases h <;> rfl


theorem pathWord_length {m : ℕ} (U : List Bool) (g : Coloring m U.length) :
    (pathWord U g).length = U.length := by
  simp [pathWord, word]

theorem pathCount_bound (m c : ℕ) (U : List Bool) :
    pathCount m U c ≤ (2 ^ m) ^ U.length :=
  connected_count_bound (pathShape U)

theorem pathCount_nil (m c : ℕ) : pathCount m [] c = 0 := by
  simp [pathCount, ConnectedColorings, pathWord, word, Connected, accept]

theorem runCount_nil (m c : ℕ) : runCount m [] c = 0 := by
  simpa [runCount, runWord] using pathCount_nil m c


theorem runWord_length_bound (L : ℕ) (rs : List ℕ)
    (hr : ∀ r ∈ rs, r ≤ L) :
    (runWord rs).length ≤ (L + 1) * rs.length := by
  induction rs with
  | nil => simp [runWord]
  | cons r rs ih =>
    have hfirst := hr r (by simp)
    have htail := ih (by intro t ht; exact hr t (by simp [ht]))
    simp only [runWord, List.flatMap_cons, List.length_append, runShape,
      List.length_cons, List.length_replicate] at *
    nlinarith


/-- The upper inequality of the manuscript's word-bound lemma, with arbitrary
surplus and without the unnecessary positivity or alphabet restrictions. -/
theorem runCount_upper_bound (m L c : ℕ) (rs : List ℕ)
    (hr : ∀ r ∈ rs, r ≤ L) :
    runCount m rs c ≤ 2 ^ (m * (L + 1) * rs.length) := by
  calc
    runCount m rs c ≤ (2 ^ m) ^ (runWord rs).length :=
      pathCount_bound m c (runWord rs)
    _ = 2 ^ (m * (runWord rs).length) := (pow_mul 2 m _).symm
    _ ≤ 2 ^ (m * ((L + 1) * rs.length)) := by
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left m (runWord_length_bound L rs hr))
    _ = 2 ^ (m * (L + 1) * rs.length) := by rw [Nat.mul_assoc]

end KroneckerWordCounts
