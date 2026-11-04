import KroneckerUnitNodeDictionary

section

/-! Split executions at an arbitrary specified edit position. -/
set_option autoImplicit false
namespace KroneckerUnitConcatenation
open KroneckerStack KroneckerDebtUnits

theorem unit_execute_append (xs ys : List Edge) (s : UnitState) :
    unitExecute (xs++ys) s=(unitExecute xs s).bind (unitExecute ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih =>
    simp only [List.cons_append,unitExecute]
    cases unitStep s e <;> simp [ih]

theorem unit_execute_split {xs ys : List Edge} {s t : UnitState}
    (h : unitExecute (xs++ys) s=some t) :
    ∃ u, unitExecute xs s=some u ∧ unitExecute ys u=some t := by
  rw [unit_execute_append] at h
  cases hu : unitExecute xs s with
  | none => simp [hu] at h
  | some u => exact ⟨u,rfl,by simpa [hu] using h⟩

end KroneckerUnitConcatenation
end

section

/-! A valid unit execution preserves any appended outer debt stack. -/
set_option autoImplicit false
namespace KroneckerUnitOuterStack
open KroneckerStack KroneckerDebtUnits

def outer (s : UnitState) (ys : List ℤ) : UnitState := ⟨s.balance,s.stack++ys⟩

theorem unit_step_outer {s t : UnitState} {e : Edge}
    (h : unitStep s e=some t) (ys : List ℤ) :
    unitStep (outer s ys) e=some (outer t ys) := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simp [unitStep] at h
  | cons x xs =>
    cases e with
    | H g =>
      simp only [unitStep,Option.some.injEq] at h
      subst t
      simp [unitStep,outer,List.append_assoc]
    | V g =>
      simp only [unitStep] at h
      split at h
      next hv => cases h; simp [unitStep,outer,hv]
      next hv => contradiction

theorem unit_execute_outer {es : List Edge} {s t : UnitState}
    (h : unitExecute es s=some t) (ys : List ℤ) :
    unitExecute es (outer s ys)=some (outer t ys) := by
  induction es generalizing s with
  | nil => simp only [unitExecute,Option.some.injEq] at h; subst t; rfl
  | cons e es ih =>
    cases hs : unitStep s e with
    | none => simp [unitExecute,hs] at h
    | some u =>
      have hu : unitExecute es u=some t := by simpa [unitExecute,hs] using h
      simp only [unitExecute,unit_step_outer hs ys,Option.bind_some]
      exact ih hu

end KroneckerUnitOuterStack
end

section

/- Original module: KroneckerUnitStepWeakening -/
section
/-! Lowering corresponding debt baselines can only weaken a vertical guard. -/
set_option autoImplicit false
namespace KroneckerUnitStepWeakening
open KroneckerStack KroneckerDebtUnits

def Weaker (s t : UnitState) : Prop := s.balance=t.balance ∧ List.Forall₂ (· ≤ ·) s.stack t.stack


theorem unit_step_weaker {s t u : UnitState} {e : Edge}
    (hw : Weaker s t) (h : unitStep t e=some u) :
    ∃ v, unitStep s e=some v ∧ Weaker v u := by
  rcases s with ⟨b,xs⟩
  rcases t with ⟨c,ys⟩
  obtain ⟨hbc,hl⟩ := hw
  dsimp only at hbc
  subst c
  cases hl with
  | nil => simp [unitStep] at h
  | @cons x y xs ys hxy hrest =>
    cases e with
    | H g =>
      simp only [unitStep,Option.some.injEq] at h
      subst u
      refine ⟨_,rfl,rfl,?_⟩
      exact List.rel_append (List.forall₂_refl _) (List.Forall₂.cons hxy hrest)
    | V g =>
      simp only [unitStep] at h
      split at h
      next hv =>
        cases h
        refine ⟨⟨b-(g : ℤ),xs⟩,?_,rfl,hrest⟩
        simp [unitStep,le_trans hxy hv]
      next hv => contradiction

end KroneckerUnitStepWeakening
end

/- Original module: KroneckerUnitExecutionWeakening -/
section
/-! Baseline weakening simulates an entire execution with no change to balances. -/
set_option autoImplicit false
namespace KroneckerUnitExecutionWeakening
open KroneckerStack KroneckerDebtUnits KroneckerUnitStepWeakening

theorem unit_execute_weaker {es : List Edge} {s t u : UnitState}
    (hw : Weaker s t) (h : unitExecute es t=some u) :
    ∃ v, unitExecute es s=some v ∧ Weaker v u := by
  induction es generalizing s t with
  | nil =>
    simp only [unitExecute,Option.some.injEq] at h
    subst u
    exact ⟨s,rfl,hw⟩
  | cons e es ih =>
    cases ht : unitStep t e with
    | none => simp [unitExecute,ht] at h
    | some t' =>
      have hu : unitExecute es t'=some u := by simpa [unitExecute,ht] using h
      obtain ⟨s',hs,hw'⟩ := unit_step_weaker hw ht
      obtain ⟨v,hv,hvw⟩ := ih hw' hu
      exact ⟨v,by simpa [unitExecute,hs] using hv,hvw⟩

end KroneckerUnitExecutionWeakening
end

/- Original module: KroneckerUnitFloorBounds -/
section
/-! A common lower bound for balances and baselines survives every successful execution. -/
set_option autoImplicit false
namespace KroneckerUnitFloorBounds
open KroneckerStack KroneckerDebtUnits

def FloorBound (a : ℤ) (s : UnitState) : Prop := a ≤ s.balance ∧ ∀ x ∈ s.stack, a ≤ x

theorem unit_step_floor {a : ℤ} {s t : UnitState} {e : Edge}
    (hf : FloorBound a s) (h : unitStep s e=some t) : FloorBound a t := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simp [unitStep] at h
  | cons x xs =>
    obtain ⟨hb,hxs⟩ := hf
    change a ≤ b at hb
    cases e with
    | H g =>
      simp only [unitStep,Option.some.injEq] at h
      subst t
      refine ⟨by dsimp; omega,?_⟩
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · have he : y=b+1 := (List.mem_replicate.mp hy).2
        omega
      · exact hxs y hy
    | V g =>
      simp only [unitStep] at h
      split at h
      next hv =>
        cases h
        exact ⟨le_trans (hxs x (by simp)) hv,fun y hy => hxs y (by simp [hy])⟩
      next hv => contradiction

theorem unit_execute_floor {a : ℤ} {es : List Edge} {s t : UnitState}
    (hf : FloorBound a s) (h : unitExecute es s=some t) : FloorBound a t := by
  induction es generalizing s with
  | nil => simp only [unitExecute,Option.some.injEq] at h; simpa [← h] using hf
  | cons e es ih =>
    cases hs : unitStep s e with
    | none => simp [unitExecute,hs] at h
    | some u => exact ih (unit_step_floor hf hs) (by simpa [unitExecute,hs] using h)

end KroneckerUnitFloorBounds
end

/- Original module: KroneckerUnitOrderBounds -/
section
/-! The ordered baseline invariant needed to transfer one unit of debt to an ancestor. -/
set_option autoImplicit false
namespace KroneckerUnitOrderBounds
open KroneckerStack KroneckerDebtUnits

def OrderedBounded (s : UnitState) : Prop :=
  s.stack.Pairwise (fun x y => y ≤ x) ∧ ∀ x ∈ s.stack, x ≤ s.balance

theorem unit_step_ordered {s t : UnitState} {e : Edge}
    (ho : OrderedBounded s) (h : unitStep s e=some t) : OrderedBounded t := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simp [unitStep] at h
  | cons x xs =>
    obtain ⟨hs,hb⟩ := ho
    change ∀ y ∈ x::xs, y ≤ b at hb
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    cases e with
    | H g =>
      simp only [unitStep,Option.some.injEq] at h
      subst t
      constructor
      · rw [List.pairwise_append]
        refine ⟨by simp,hs,?_⟩
        intro y hy z hz
        have he : y=b+1 := (List.mem_replicate.mp hy).2
        have hh := hb z hz
        omega
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact ((List.mem_replicate.mp hy).2).le
        · have hh := hb y hy; dsimp; omega
    | V g =>
      simp only [unitStep] at h
      split at h
      next hv =>
        cases h
        exact ⟨htail,fun y hy => le_trans (hhead y hy) hv⟩
      next hv => contradiction

end KroneckerUnitOrderBounds
end

/- Original module: KroneckerUnitInvariantExecution -/
section
/-! Ordered/bounded stacks and their canonical initial states. -/
set_option autoImplicit false
namespace KroneckerUnitInvariantExecution
open KroneckerStack KroneckerDebtUnits KroneckerUnitOrderBounds KroneckerUnitFloorBounds

theorem unit_execute_ordered {es : List Edge} {s t : UnitState}
    (ho : OrderedBounded s) (h : unitExecute es s=some t) : OrderedBounded t := by
  induction es generalizing s with
  | nil => simp only [unitExecute,Option.some.injEq] at h; simpa [← h] using ho
  | cons e es ih =>
    cases hs : unitStep s e with
    | none => simp [unitExecute,hs] at h
    | some u => exact ih (unit_step_ordered ho hs) (by simpa [unitExecute,hs] using h)

theorem replicate_ordered (b : ℤ) (g : ℕ) : OrderedBounded ⟨b,List.replicate g b⟩ := by
  constructor
  · simp
  · intro x hx
    exact ((List.mem_replicate.mp hx).2).le

theorem replicate_floor (a b : ℤ) (g : ℕ) (h : a ≤ b) :
    FloorBound a ⟨b,List.replicate g b⟩ := by
  refine ⟨h,?_⟩
  intro x hx
  simpa only [(List.mem_replicate.mp hx).2] using h

end KroneckerUnitInvariantExecution
end

/- Original module: KroneckerUnitShift -/
section
/-! Balance and baseline translation for debt-unit executions. -/
set_option autoImplicit false
namespace KroneckerUnitShift
open KroneckerStack KroneckerDebtUnits

def shift (d : ℤ) (s : UnitState) : UnitState := ⟨s.balance+d,s.stack.map (fun x => x+d)⟩

theorem unit_step_shift {s t : UnitState} {e : Edge} (h : unitStep s e=some t) (d : ℤ) :
    unitStep (shift d s) e=some (shift d t) := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simp [unitStep] at h
  | cons x xs =>
    cases e with
    | H g =>
      simp only [unitStep,Option.some.injEq] at h
      subst t
      simp [unitStep,shift,List.map_append,add_assoc,add_comm]
    | V g =>
      simp only [unitStep] at h
      split at h
      next hv =>
        cases h
        have hv' : x+d ≤ b+d-(g : ℤ) := by omega
        simp [unitStep,shift,hv',sub_add_eq_add_sub]
      next hv => contradiction

theorem unit_execute_shift {es : List Edge} {s t : UnitState}
    (h : unitExecute es s=some t) (d : ℤ) :
    unitExecute es (shift d s)=some (shift d t) := by
  induction es generalizing s with
  | nil => simp only [unitExecute,Option.some.injEq] at h; subst t; rfl
  | cons e es ih =>
    cases hs : unitStep s e with
    | none => simp [unitExecute,hs] at h
    | some u =>
      simp only [unitExecute,unit_step_shift hs d,Option.bind_some]
      exact ih (by simpa [unitExecute,hs] using h)

end KroneckerUnitShift
end
end

