import KroneckerSourceGradingDictionary

/-!
Internal sequence operations and colors for the path-counting model.

Finite indices represent edge occurrences; the values of a word can repeat.
The mathematical color labels 1,...,choose(m,g) are explicitly equivalent
to the zero-based Fin palette used in the internal proofs.
`S`, `L`, `R`, and `App` are internal sequence helpers, not manuscript notation.
`Bal` is the boundary balance. The separate per-node `Debt` is defined in
KroneckerPaperPredecessor; the global walk called `debt` in
KroneckerCompatibility is not that per-node quantity.
-/
set_option autoImplicit false
namespace KroneckerPaper
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerWeights

abbrev EdgeOccurrence (n : ℕ) := Fin n
abbrev CharacterBoundary (n : ℕ) := Fin (n+1)

def S {n : ℕ} (v : EdgeOccurrence n) : ℕ := v.val

theorem starting_boundary_injective (n : ℕ) :
    Function.Injective (@S n) := by
  intro x y h
  exact Fin.ext h

theorem starting_boundary_lt {n : ℕ} (v : EdgeOccurrence n) : S v < n := v.isLt

/-- Prefix and suffix lists in traversal order. -/
def L {α : Type*} (U : List α) (i : ℕ) : List α := U.take i
def R {α : Type*} (U : List α) (i : ℕ) : List α := U.drop i

def Ins {α : Type*} (U : List α) (i : ℕ) (V : List α) : List α := L U i ++ V ++ R U i

def Del {α : Type*} (U : List α) (i : ℕ) : List α := L U i ++ R U (i+1)

/-- The ungraded simple run; true denotes E and false denotes N. -/
def simpleRun (j : ℕ) : List Bool := true :: List.replicate j false

/-- Internal list concatenation. -/
def App (U V : List Bool) : List Bool := U ++ V

theorem prefix_suffix {α : Type*} (U : List α) (i : ℕ) : L U i ++ R U i = U :=
  List.take_append_drop i U

theorem insertion_formula {α : Type*} (U V : List α) (i : ℕ) :
    Ins U i V = U.take i ++ V ++ U.drop i := rfl

theorem deletion_formula {α : Type*} (U : List α) (i : ℕ) :
    Del U i = U.take i ++ U.drop (i+1) := rfl

def paperColorEquiv (k : ℕ) : Fin k ≃ {c : ℕ // 1 ≤ c ∧ c ≤ k} where
  toFun c := ⟨c.val+1, by have := c.isLt; omega⟩
  invFun c := ⟨c.val-1, by have := c.property; omega⟩
  left_inv c := by apply Fin.ext; simp
  right_inv c := by apply Subtype.ext; have := c.property; simp only; omega

/-- Balance after the specified number of edges. -/
def Bal {m n : ℕ} (shape : ℕ → Bool) (g : Grades m n)
    (i : CharacterBoundary n) : ℤ :=
  balance (KroneckerSourceGradingDictionary.rawTrace shape g) i.val

theorem balance_formula {m n : ℕ} (shape : ℕ → Bool) (g : Grades m n)
    (i : CharacterBoundary n) :
    Bal shape g i =
      intervalSum hCount (KroneckerSourceGradingDictionary.rawTrace shape g) 0 i.val -
      intervalSum vGrade (KroneckerSourceGradingDictionary.rawTrace shape g) 0 i.val := by
  simpa [Bal, balance, walk] using
    balance_interval (KroneckerSourceGradingDictionary.rawTrace shape g) 0 i.val

theorem colored_balance_eq {m n : ℕ} (shape : ℕ → Bool) (g : Coloring m n)
    (i : CharacterBoundary n) :
    balance (trace shape g) i.val = Bal shape (grades g) i := by
  rw [KroneckerSourceGradingDictionary.trace_eq_raw_grades]
  rfl

/-- The cardinality identity uses connectedness only through the grades. -/
theorem connected_colored_count {m n d : ℕ} (shape : ℕ → Bool) :
    Nat.card {g : Coloring m n // Connected m (word shape g) d} =
      weightedCount (fun g : Grades m n => Connected m (word shape (representative g)) d) :=
  colored_count (fun g : Grades m n => Connected m (word shape (representative g)) d)

/-- Each uncolored grading has exactly the product of its binomial palettes. -/
theorem grading_color_count {m n : ℕ} (g : Grades m n) :
    Fintype.card (ColorFiber g) = ∏ v : Fin n, Nat.choose m (g v).val :=
  fiber_card g

end KroneckerPaper
