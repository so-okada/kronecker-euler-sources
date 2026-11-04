import KroneckerUnitShift

/-! Definition 9.2 and Lemma 9.3. These updates also allow a horizontal edge on an empty list,
as prescribed by Definition 9.2. -/
set_option autoImplicit false
namespace KroneckerBoundaryListComparison
open KroneckerStack KroneckerDebtUnits

def step (s : UnitState) : Edge → Option UnitState
  | .H g => some ⟨s.balance + 1, List.replicate g (s.balance + 1) ++ s.stack⟩
  | .V h => match s.stack with
    | [] => none
    | a :: xs => if a ≤ s.balance - (h : ℤ) then
        some ⟨s.balance - (h : ℤ), xs⟩ else none

def execute : List Edge → UnitState → Option UnitState
  | [], s => some s
  | e :: es, s => (step s e).bind (execute es)

def Compared (δ : ℤ) (s t : UnitState) : Prop :=
  t.balance = s.balance + δ ∧
    List.Forall₂ (fun a a' => a' ≤ a + δ) s.stack t.stack

theorem step_comparison {δ : ℤ} {s t u : UnitState} {e : Edge}
    (h : Compared δ s t) (hs : step s e = some u) :
    ∃ v, step t e = some v ∧ Compared δ u v := by
  rcases s with ⟨b, xs⟩
  rcases t with ⟨b', ys⟩
  obtain ⟨hb, hl⟩ := h
  dsimp at hb hl
  subst b'
  cases e with
  | H g =>
    simp only [step, Option.some.injEq] at hs
    subst u
    refine ⟨_, rfl, by dsimp; omega, ?_⟩
    apply List.rel_append _ hl
    induction g with
    | zero => exact .nil
    | succ g ih => exact .cons (by dsimp; omega) ih
  | V h =>
    cases hl with
    | nil => simp [step] at hs
    | @cons a a' xs ys ha ht =>
      simp only [step] at hs
      split at hs
      next hv =>
        cases hs
        refine ⟨⟨b + δ - (h : ℤ), ys⟩, ?_, by dsimp; omega, ht⟩
        simp [step, show a' ≤ b + δ - (h : ℤ) by omega]
      next hv => contradiction

theorem execute_comparison {δ : ℤ} {s t u : UnitState} {es : List Edge}
    (h : Compared δ s t) (hs : execute es s = some u) :
    ∃ v, execute es t = some v ∧ Compared δ u v := by
  induction es generalizing s t with
  | nil =>
    simp only [execute, Option.some.injEq] at hs
    subst u
    exact ⟨t, rfl, h⟩
  | cons e es ih =>
    cases he : step s e with
    | none => simp [execute, he] at hs
    | some s' =>
      obtain ⟨t', ht, hc⟩ := step_comparison h he
      obtain ⟨v, hv, hc'⟩ := ih hc (by simpa [execute, he] using hs)
      exact ⟨v, by simpa [execute, ht] using hv, hc'⟩

theorem execute_append (xs ys : List Edge) (s : UnitState) :
    execute (xs ++ ys) s = (execute xs s).bind (execute ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih =>
    simp only [List.cons_append, execute]
    cases step s e <;> simp [ih]

theorem prefix_comparison {δ : ℤ} {s t u : UnitState} {xs ys : List Edge}
    (h : Compared δ s t) (hs : execute (xs ++ ys) s = some u) :
    ∃ s' t', execute xs s = some s' ∧ execute xs t = some t' ∧
      Compared δ s' t' ∧ s'.stack.length = t'.stack.length := by
  rw [execute_append] at hs
  cases he : execute xs s with
  | none => simp [he] at hs
  | some s' =>
    obtain ⟨t', ht, hc⟩ := execute_comparison h he
    exact ⟨s', t', rfl, ht, hc, hc.2.length_eq⟩

end KroneckerBoundaryListComparison
