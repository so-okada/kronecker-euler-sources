import KroneckerDebtUnits

/- Original module: KroneckerPositiveUnitStack -/
section
/-! Positive debts make emptiness and the first debt unit faithful to the node stack. -/
set_option autoImplicit false
namespace KroneckerPositiveUnitStack
open KroneckerStack KroneckerComponentRoots KroneckerDebtUnits

theorem units_eq_nil_iff (xs : List Node) (hp : ∀ x ∈ xs, 0 < x.debt) :
    units xs=[] ↔ xs=[] := by
  cases xs with
  | nil => simp [units]
  | cons x xs =>
    have hx := hp x (by simp)
    simp [units_cons,hx.ne']

theorem units_positive_cons (x : Node) (xs : List Node) (hx : 0 < x.debt) :
    units (x::xs)=x.baseline::(List.replicate (x.debt-1) x.baseline++units xs) := by
  have hd : x.debt=(x.debt-1)+1 := by omega
  rw [units_cons,hd,List.replicate_succ,List.cons_append]
  simp only [Nat.add_sub_cancel]

theorem units_after_decrement (x : Node) (xs : List Node) :
    units (if x.debt=1 then xs else ⟨x.debt-1,x.baseline⟩::xs)=
      List.replicate (x.debt-1) x.baseline++units xs := by
  by_cases h : x.debt=1
  · simp [h]
  · simp [h,units_cons]

end KroneckerPositiveUnitStack
end

/- Original module: KroneckerUnitStepSimulation -/
section
/-! One step of the actual positive-debt interpreter is exactly represented by debt units. -/
set_option autoImplicit false
namespace KroneckerUnitStepSimulation
open KroneckerStack KroneckerComponentRoots KroneckerDebtUnits KroneckerPositiveUnitStack

theorem flatten_step (s : State) (e : Edge) (hp : PositiveDebts s) :
    Option.map flatten (step s e)=unitStep (flatten s) e := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simp [step,flatten,units,unitStep]
  | cons x xs =>
    have hx : 0 < x.debt := hp x (by simp)
    have hu := units_positive_cons x xs hx
    cases e with
    | H g =>
      by_cases hg : g=0
      · simp [step,flatten,unitStep,hu,hg]
      · simp [step,flatten,unitStep,hu,hg,units_cons]
    | V g =>
      by_cases hv : x.baseline ≤ b-(g : ℤ)
      · simp [step,flatten,unitStep,hu,hx,hv,units_after_decrement x xs]
      · simp [step,flatten,unitStep,hu,hx,hv]

theorem unit_step_of_step {s t : State} {e : Edge} (hp : PositiveDebts s)
    (h : step s e=some t) : unitStep (flatten s) e=some (flatten t) := by
  rw [← flatten_step s e hp,h]
  rfl

end KroneckerUnitStepSimulation
end

/- Original module: KroneckerUnitExecutionSimulation -/
section
/-! Exact simulation of the original interpreter, including failure. -/
set_option autoImplicit false
namespace KroneckerUnitExecutionSimulation
open KroneckerStack KroneckerComponentRoots KroneckerDebtUnits KroneckerUnitStepSimulation

theorem flatten_execute (es : List Edge) (s : State) (hp : PositiveDebts s) :
    Option.map flatten (execute es s)=unitExecute es (flatten s) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    cases hs : step s e with
    | none =>
      have hu : unitStep (flatten s) e=none := by rw [← flatten_step s e hp,hs]; rfl
      simp [execute,unitExecute,hs,hu]
    | some t =>
      have hu := unit_step_of_step hp hs
      simpa only [execute,unitExecute,hs,hu,Option.bind_some] using
        ih t (step_positive_debts hp hs)

theorem unit_execution_of_execution {es : List Edge} {s t : State}
    (hp : PositiveDebts s) (h : execute es s=some t) :
    unitExecute es (flatten s)=some (flatten t) := by
  rw [← flatten_execute es s hp,h]
  rfl

end KroneckerUnitExecutionSimulation
end

/- Original module: KroneckerUnitExecutionRecovery -/
section
/-! A successful debt-unit execution lifts to an actual positive-debt execution. -/
set_option autoImplicit false
namespace KroneckerUnitExecutionRecovery
open KroneckerStack KroneckerComponentRoots KroneckerDebtUnits
open KroneckerUnitExecutionSimulation KroneckerPositiveUnitStack

theorem recover_execution {es : List Edge} {s : State} {u : UnitState}
    (hp : PositiveDebts s) (h : unitExecute es (flatten s)=some u) :
    ∃ t, execute es s=some t ∧ flatten t=u ∧ PositiveDebts t := by
  rw [← flatten_execute es s hp] at h
  cases he : execute es s with
  | none => simp [he] at h
  | some t =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    exact ⟨t,rfl,h,execute_positive_debts hp he⟩

theorem recover_closed_execution {es : List Edge} {s : State} {b : ℤ}
    (hp : PositiveDebts s) (h : unitExecute es (flatten s)=some ⟨b,[]⟩) :
    execute es s=some ⟨b,[]⟩ := by
  obtain ⟨t,ht,hflat,htp⟩ := recover_execution hp h
  have hb := congrArg UnitState.balance hflat
  have hs := congrArg UnitState.stack hflat
  have hnil : t.stack=[] := (units_eq_nil_iff t.stack htp).mp hs
  have heq : t=⟨b,[]⟩ := by cases t; simp_all [flatten]
  simpa only [heq] using ht

end KroneckerUnitExecutionRecovery
end

/- Original module: KroneckerUnitNodeDictionary -/
section
/-! The new representation characterizes the actual NodeRun predicate. -/
set_option autoImplicit false
namespace KroneckerUnitNodeDictionary
open KroneckerStack KroneckerComponentRoots KroneckerDebtUnits
open KroneckerUnitExecutionSimulation KroneckerUnitExecutionRecovery

def UnitNodeRun (es : List Edge) (c : ℕ) : Prop :=
  ∃ g rest, es=.H (g+1)::rest ∧
    unitExecute rest ⟨1,List.replicate (g+1) 1⟩=some ⟨(c : ℤ)+1,[]⟩

theorem node_to_units {es : List Edge} {c : ℕ} (h : NodeRun es c) : UnitNodeRun es c := by
  obtain ⟨g,rest,rfl,he⟩ := h
  refine ⟨g,rest,rfl,?_⟩
  have hp : PositiveDebts ⟨1,[⟨g+1,1⟩]⟩ := by simp [PositiveDebts]
  simpa [flatten,units] using unit_execution_of_execution hp he

theorem units_to_node {es : List Edge} {c : ℕ} (h : UnitNodeRun es c) : NodeRun es c := by
  obtain ⟨g,rest,rfl,he⟩ := h
  refine ⟨g,rest,rfl,?_⟩
  apply recover_closed_execution (by simp [PositiveDebts])
  simpa [flatten,units] using he

theorem node_iff_units (es : List Edge) (c : ℕ) : NodeRun es c ↔ UnitNodeRun es c :=
  ⟨node_to_units,units_to_node⟩

end KroneckerUnitNodeDictionary
end
