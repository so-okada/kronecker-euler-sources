import KroneckerGeometricPrograms

/-! Definition 4.1. Each operation has a run as its source; its target
need not be a run. The identity is the empty list, not a primitive operation. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerPaperPaths

def IsRun (U : TNEPath) : Prop :=
  ∃ rs : List ℕ, rs ≠ [] ∧ (∀ r ∈ rs, 0 < r) ∧ U = runPath rs U.origin

inductive RunEdit : TNEPath → TNEPath → Type
  | north (U : TNEPath) (hU : IsRun U) (i : ℕ) (hi : i ≤ U.steps.length) :
      RunEdit U (insert U i (ofSteps [false] 0))
  | delete (U : TNEPath) (hU : IsRun U) (v : Edge U)
      (hv : U.steps.get v = false) : RunEdit U (deleteVertical U v hv)
  | complete (U : TNEPath) (hU : IsRun U) (i r : ℕ)
      (hi : i ≤ U.steps.length) (hr : 0 < r) :
      RunEdit U (insert U i (simpleRun r hr))
  | exchange (U : TNEPath) (hU : IsRun U) (A B : List ℕ) (r s : ℕ)
      (h : U = runPath (A ++ [r, s] ++ B) U.origin) :
      RunEdit U (exchangeRuns U A.length)

def RunEdit.IsVertical {U V : TNEPath} : RunEdit U V → Prop
  | .north .. => True
  | .delete .. => True
  | .complete .. => False
  | .exchange .. => False

theorem RunEdit.source_isRun {U V : TNEPath} (t : RunEdit U V) : IsRun U := by
  cases t <;> assumption

inductive RunEditList (U : TNEPath) : TNEPath → ℕ → Type
  | nil (hU : IsRun U) : RunEditList U U 0
  | snoc {V W : TNEPath} {n : ℕ} (ts : RunEditList U V n) (t : RunEdit V W) :
      RunEditList U W (n + 1)

theorem RunEditList.empty_target {U V : TNEPath} (ts : RunEditList U V 0) : V = U := by
  cases ts
  rfl

theorem RunEditList.source_isRun {U V : TNEPath} {n : ℕ}
    (ts : RunEditList U V n) : IsRun U := by
  induction ts with
  | nil h => exact h
  | snoc _ _ ih => exact ih

def RunEditList.append {U V W : TNEPath} {n k : ℕ}
    (ts : RunEditList U V n) (ss : RunEditList V W k) : RunEditList U W (n + k) := by
  induction ss with
  | nil => simpa using ts
  | snoc _ t ih => simpa [Nat.add_assoc] using RunEditList.snoc ih t

def EditProgram.length {m K A D : ℕ} {U V : TNEPath} :
    EditProgram m U V K A D → ℕ
  | .nil => 0
  | .complete p .. => p.length + 1
  | .north p .. => p.length + 1
  | .delete p .. => p.length + 1

/-- Proposition 4.10, hypothesis (a): the specified counts allow any ordering of the operations. -/
theorem EditProgram.length_eq {m K A D : ℕ} {U V : TNEPath}
    (p : EditProgram m U V K A D) : p.length = K + A + D := by
  induction p with
  | nil => rfl
  | complete p r i hr hi ih => simp only [length, ih]; omega
  | north p i hi ih => simp only [length, ih]; omega
  | delete p k hv ih => simp only [length, ih]; omega

end KroneckerPaperPaths
