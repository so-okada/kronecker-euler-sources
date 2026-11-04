import KroneckerUnitPreservingLoopShell

/- Original module: KroneckerUnitSingletonSimulation -/
section
/-! Suffix simulation with the exact protected root, not merely a related final stack. -/
set_option autoImplicit false
namespace KroneckerUnitSingletonSimulation
open KroneckerStack KroneckerDebtUnits KroneckerUnitShift KroneckerUnitStepWeakening
open KroneckerUnitExecutionWeakening KroneckerUnitBalanceRaise KroneckerUnitRaisedExecution
open KroneckerUnitExecutionBottom

theorem execute_weaker_singleton {es : List Edge} {s t : UnitState} {b a z : ℤ}
    (hw : Weaker s t) (h : unitExecute es t=some ⟨b,[z]⟩)
    (hb : s.stack.getLast?=some a) : unitExecute es s=some ⟨b,[a]⟩ := by
  obtain ⟨v,hv,hvw⟩ := unit_execute_weaker hw h
  have hne : v.stack≠[] := by
    intro he
    have hl := hvw.2.length_eq
    simp [he] at hl
  have hvb : v.stack.getLast?=some a := (unit_execute_bottom hv hne).trans hb
  rw [singleton_from_bottom v b a z hvw hvb] at hv
  exact hv

theorem execute_raised_singleton {es : List Edge} {s : UnitState} {c a : ℤ}
    (h : unitExecute es s=some ⟨c,[a]⟩) (d : ℤ) (hd : 0≤d) :
    unitExecute es (raiseBalance d s)=some ⟨c+d,[a]⟩ := by
  apply execute_weaker_singleton (raised_weaker_shift s d hd)
    (unit_execute_shift h d)
  change s.stack.getLast?=some a
  exact (unit_execute_bottom h (by simp)).symm

end KroneckerUnitSingletonSimulation
end

/- Original module: KroneckerMarkedDebtIndex -/
section
/-! The edge that consumes a marked debt unit depends only on horizontal grades. -/
set_option autoImplicit false
namespace KroneckerMarkedDebtIndex
open KroneckerStack

def markedIndex : ℕ → List Edge → Option ℕ
  | _, [] => none
  | d, .H g::es => (markedIndex (g+d) es).map Nat.succ
  | 0, .V _::_ => some 0
  | d+1, .V _::es => (markedIndex d es).map Nat.succ

inductive SameDebt : Edge → Edge → Prop
  | horizontal (g : ℕ) : SameDebt (.H g) (.H g)
  | vertical (g h : ℕ) : SameDebt (.V g) (.V h)

theorem sameDebt_refl (e : Edge) : SameDebt e e := by
  cases e with
  | H g => exact .horizontal g
  | V g => exact .vertical g g

theorem markedIndex_invariant {xs ys : List Edge}
    (h : List.Forall₂ SameDebt xs ys) (d : ℕ) : markedIndex d xs=markedIndex d ys := by
  induction h generalizing d with
  | nil => rfl
  | cons he ht ih =>
    cases he with
    | horizontal g => simp only [markedIndex,ih]
    | vertical g h => cases d <;> simp only [markedIndex,ih]

theorem markedIndex_vertical {es : List Edge} {d j : ℕ}
    (h : markedIndex d es=some j) : ∃ g, es[j]?=some (.V g) := by
  induction es generalizing d j with
  | nil => simp [markedIndex] at h
  | cons e es ih =>
    cases e with
    | H g =>
      simp only [markedIndex,Option.map_eq_some_iff] at h
      obtain ⟨k,hk,rfl⟩ := h
      simpa using ih hk
    | V g =>
      cases d with
      | zero => simp only [markedIndex,Option.some.injEq] at h; subst j; exact ⟨g,rfl⟩
      | succ d =>
        simp only [markedIndex,Option.map_eq_some_iff] at h
        obtain ⟨k,hk,rfl⟩ := h
        simpa using ih hk

end KroneckerMarkedDebtIndex
end

/- Original module: KroneckerVerticalRepair -/
section
/-! A single ordered vertical-grade decrease, with an explicit and recoverable index. -/
set_option autoImplicit false
namespace KroneckerVerticalRepair
open KroneckerStack KroneckerMarkedDebtIndex

inductive RepairAt : ℕ → List Edge → List Edge → ℕ → ℕ → Prop
  | here (es : List Edge) (h k : ℕ) (hk : k≤h) :
      RepairAt 0 (.V h::es) (.V k::es) h k
  | there {j h k : ℕ} {xs ys : List Edge} (e : Edge)
      (hr : RepairAt j xs ys h k) : RepairAt (j+1) (e::xs) (e::ys) h k

theorem repair_le {j h k : ℕ} {xs ys : List Edge}
    (hr : RepairAt j xs ys h k) : k≤h := by
  induction hr with
  | here _ _ _ hk => exact hk
  | there _ _ ih => exact ih

theorem repair_sameDebt {j h k : ℕ} {xs ys : List Edge}
    (hr : RepairAt j xs ys h k) : List.Forall₂ SameDebt xs ys := by
  induction hr with
  | here es h k _ =>
    refine .cons (.vertical h k) ?_
    induction es with
    | nil => exact .nil
    | cons e es ih => exact .cons (sameDebt_refl e) ih
  | there e _ ih => exact .cons (sameDebt_refl e) ih

theorem repair_recovery {j h k : ℕ} {xs ys : List Edge}
    (hr : RepairAt j xs ys h k) : ys.set j (.V h)=xs := by
  induction hr with
  | here => rfl
  | there e _ ih => exact congrArg (List.cons e) ih

theorem repair_original {j h k : ℕ} {xs ys : List Edge}
    (hr : RepairAt j xs ys h k) : xs[j]?=some (.V h) := by
  induction hr with
  | here => rfl
  | there _ _ ih => simpa using ih

end KroneckerVerticalRepair
end
