import KroneckerUnitShellReserve

section

/- Original module: KroneckerUnitErase -/
section
/-! Erase one marked debt unit while retaining at least one unit below it. -/
set_option autoImplicit false
namespace KroneckerUnitErase

inductive EraseUnit (a : ℤ) : List ℤ → List ℤ → Prop where
  | here {xs : List ℤ} (hne : xs≠[]) : EraseUnit a (a::xs) xs
  | there (x : ℤ) {xs ys : List ℤ} (h : EraseUnit a xs ys) : EraseUnit a (x::xs) (x::ys)

theorem erased_nonempty {a : ℤ} {xs ys : List ℤ} (h : EraseUnit a xs ys) : ys≠[] := by
  cases h with
  | here hne => exact hne
  | there => simp

theorem erase_length {a : ℤ} {xs ys : List ℤ} (h : EraseUnit a xs ys) : xs.length=ys.length+1 := by
  induction h with
  | here => simp
  | there x h ih => simpa using congrArg Nat.succ ih


end KroneckerUnitErase
end

/- Original module: KroneckerUnitEraseContext -/
section
/-! Contexts for a marked debt unit and exclusion of the protected bottom unit. -/
set_option autoImplicit false
namespace KroneckerUnitEraseContext
open KroneckerUnitErase



theorem erase_singleton_impossible (a b : ℤ) (ys : List ℤ) : ¬EraseUnit a [b] ys := by
  intro h
  have hl := erase_length h
  have hy : ys=[] := List.length_eq_zero_iff.mp (by simpa using hl.symm)
  exact erased_nonempty h hy

end KroneckerUnitEraseContext
end

/- Original module: KroneckerUnitEraseReplicate -/
section
/-! A marked unit after a horizontal push is either newly created or inherited. -/
set_option autoImplicit false
namespace KroneckerUnitEraseReplicate
open KroneckerUnitErase

theorem erase_replicate (a b : ℤ) (g : ℕ) (xs ys : List ℤ)
    (h : EraseUnit a (List.replicate g b++xs) ys) :
    (∃ k,g=k+1 ∧ a=b ∧ ys=List.replicate k b++xs) ∨
    (∃ zs,EraseUnit a xs zs ∧ ys=List.replicate g b++zs) := by
  induction g generalizing ys with
  | zero => exact Or.inr ⟨ys,h,rfl⟩
  | succ g ih =>
    simp only [List.replicate_succ,List.cons_append] at h
    cases h with
    | here hne => exact Or.inl ⟨g,rfl,rfl,rfl⟩
    | there x h =>
      rcases ih _ h with ⟨k,hg,hab,hy⟩ | ⟨zs,hz,hy⟩
      · subst g
        refine Or.inl ⟨k+1,rfl,hab,?_⟩
        simpa [List.replicate_succ] using congrArg (b::·) hy
      · refine Or.inr ⟨zs,hz,?_⟩
        simpa [List.replicate_succ] using congrArg (b::·) hy

end KroneckerUnitEraseReplicate
end

/- Original module: KroneckerHorizontalBacktrace -/
section
/-! Trace a missing unit backward through a horizontal step. -/
set_option autoImplicit false
namespace KroneckerHorizontalBacktrace
open KroneckerStack KroneckerDebtUnits KroneckerUnitErase KroneckerUnitEraseReplicate

def EraseState (a : ℤ) (s t : UnitState) : Prop :=
  s.balance=t.balance ∧ EraseUnit a s.stack t.stack

theorem horizontal_backtrace {a : ℤ} {s t v : UnitState} {g : ℕ}
    (hs : unitStep s (.H g)=some t) (he : EraseState a t v) :
    (∃ r,EraseState a s r ∧ unitStep r (.H g)=some v) ∨
    (∃ k,g=k+1 ∧ unitStep s (.H k)=some v) := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simp [unitStep] at hs
  | cons x xs =>
    simp only [unitStep,Option.some.injEq] at hs
    subst t
    rcases v with ⟨c,ys⟩
    obtain ⟨hb,he⟩ := he
    change b+1=c at hb
    subst c
    rcases erase_replicate a (b+1) g (x::xs) ys he with ⟨k,hg,ha,hy⟩ | ⟨zs,hz,hy⟩
    · subst g
      subst ys
      exact Or.inr ⟨k,rfl,rfl⟩
    · subst ys
      refine Or.inl ⟨⟨b,zs⟩,⟨rfl,hz⟩,?_⟩
      have hn := erased_nonempty hz
      cases zs with
      | nil => contradiction
      | cons z zs => rfl

end KroneckerHorizontalBacktrace
end

/- Original module: KroneckerVerticalBacktrace -/
section
/-! A surviving marked unit traces below the head consumed by a vertical step. -/
set_option autoImplicit false
namespace KroneckerVerticalBacktrace
open KroneckerStack KroneckerDebtUnits KroneckerUnitErase KroneckerHorizontalBacktrace

theorem vertical_backtrace {a : ℤ} {s t v : UnitState} {g : ℕ}
    (hs : unitStep s (.V g)=some t) (he : EraseState a t v) :
    ∃ r,EraseState a s r ∧ unitStep r (.V g)=some v := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simp [unitStep] at hs
  | cons x xs =>
    simp only [unitStep] at hs
    split at hs
    next hg =>
      cases hs
      rcases v with ⟨c,ys⟩
      obtain ⟨hb,he⟩ := he
      change b-(g : ℤ)=c at hb
      subst c
      refine ⟨⟨b,x::ys⟩,⟨rfl,EraseUnit.there x he⟩,?_⟩
      simp [unitStep,hg]
    next hg => contradiction

end KroneckerVerticalBacktrace
end

/- Original module: KroneckerUnitStepBacktrace -/
section
/-! The one-step provenance dichotomy for a marked debt unit. -/
set_option autoImplicit false
namespace KroneckerUnitStepBacktrace
open KroneckerStack KroneckerDebtUnits KroneckerHorizontalBacktrace KroneckerVerticalBacktrace

theorem step_backtrace {a : ℤ} {s t v : UnitState} {e : Edge}
    (hs : unitStep s e=some t) (he : EraseState a t v) :
    (∃ r,EraseState a s r ∧ unitStep r e=some v) ∨
    (∃ k,e=.H (k+1) ∧ unitStep s (.H k)=some v) := by
  cases e with
  | H g =>
    rcases horizontal_backtrace hs he with h | ⟨k,hg,hk⟩
    · exact Or.inl h
    · exact Or.inr ⟨k,congrArg Edge.H hg,hk⟩
  | V g => exact Or.inl (vertical_backtrace hs he)

end KroneckerUnitStepBacktrace
end

/- Original module: KroneckerLowerOneHorizontal -/
section
/-! Lower exactly one positive horizontal grade and retain every other edge. -/
set_option autoImplicit false
namespace KroneckerLowerOneHorizontal
open KroneckerStack

def LowerOne (xs ys : List Edge) : Prop :=
  ∃ pre post g,xs=pre++(.H (g+1)::post) ∧ ys=pre++(.H g::post)



theorem lower_grades {xs ys : List Edge} (h : LowerOne xs ys) (m : ℕ)
    (hx : ∀ e ∈ xs,e.grade ≤ m) : ∀ e ∈ ys,e.grade ≤ m := by
  obtain ⟨pre,post,g,rfl,rfl⟩ := h
  intro e he
  rcases List.mem_append.mp he with hp | hp
  · exact hx e (List.mem_append_left _ hp)
  · rcases List.mem_cons.mp hp with rfl | hp
    · have hg := hx (.H (g+1)) (by simp)
      change g+1 ≤ m at hg
      change g ≤ m
      omega
    · exact hx e (by simp [hp])

end KroneckerLowerOneHorizontal
end

/- Original module: KroneckerLowerOneContexts -/
section
/-! Preserve the identity of the one changed horizontal edge under word contexts. -/
set_option autoImplicit false
namespace KroneckerLowerOneContexts
open KroneckerStack KroneckerLowerOneHorizontal

theorem lower_cons (e : Edge) {xs ys : List Edge} (h : LowerOne xs ys) :
    LowerOne (e::xs) (e::ys) := by
  obtain ⟨pre,post,g,rfl,rfl⟩ := h
  exact ⟨e::pre,post,g,rfl,rfl⟩



end KroneckerLowerOneContexts
end

/- Original module: KroneckerUnitExecutionBacktrace -/
section
/-! Trace a marked surviving unit to the initial stack or its creating horizontal edge. -/
set_option autoImplicit false
namespace KroneckerUnitExecutionBacktrace
open KroneckerStack KroneckerDebtUnits KroneckerHorizontalBacktrace KroneckerUnitStepBacktrace
open KroneckerLowerOneHorizontal KroneckerLowerOneContexts

theorem execution_backtrace {a : ℤ} {es : List Edge} {s t v : UnitState}
    (hrun : unitExecute es s=some t) (he : EraseState a t v) :
    (∃ r,EraseState a s r ∧ unitExecute es r=some v) ∨
    (∃ es',LowerOne es es' ∧ unitExecute es' s=some v) := by
  induction es generalizing s with
  | nil =>
    simp only [unitExecute,Option.some.injEq] at hrun
    subst t
    exact Or.inl ⟨v,he,rfl⟩
  | cons e es ih =>
    cases hs : unitStep s e with
    | none => simp [unitExecute,hs] at hrun
    | some u =>
      have htail : unitExecute es u=some t := by simpa [unitExecute,hs] using hrun
      rcases ih htail with ⟨r,her,hrest⟩ | ⟨es',hel,hrest⟩
      · rcases step_backtrace hs her with ⟨r',her',hstep⟩ | ⟨k,hk,hstep⟩
        · exact Or.inl ⟨r',her',by simpa [unitExecute,hstep] using hrest⟩
        · subst e
          exact Or.inr ⟨.H k::es,⟨[],es,k,rfl,rfl⟩,by simpa [unitExecute,hstep] using hrest⟩
      · exact Or.inr ⟨e::es',lower_cons e hel,by simpa [unitExecute,hs] using hrest⟩

end KroneckerUnitExecutionBacktrace
end

/- Original module: KroneckerProtectedRootBacktrace -/
section
/-! Above a protected singleton root, the missing unit must originate inside the word. -/
set_option autoImplicit false
namespace KroneckerProtectedRootBacktrace
open KroneckerStack KroneckerDebtUnits KroneckerUnitErase KroneckerUnitEraseContext
open KroneckerLowerOneHorizontal KroneckerUnitExecutionBacktrace

theorem protected_root_backtrace (b floor a c : ℤ) (es : List Edge) (tail : List ℤ)
    (hne : tail≠[]) (hrun : unitExecute es ⟨b,[floor]⟩=some ⟨c,a::tail⟩) :
    ∃ es',LowerOne es es' ∧ unitExecute es' ⟨b,[floor]⟩=some ⟨c,tail⟩ := by
  rcases execution_backtrace (a:=a) (v:=⟨c,tail⟩) hrun ⟨rfl,EraseUnit.here hne⟩ with ⟨r,he,_⟩ | h
  · exact False.elim (erase_singleton_impossible a floor r.stack he.2)
  · exact h

end KroneckerProtectedRootBacktrace
end

/- Original module: KroneckerUnitNonemptyExecution -/
section
/-! A successful execution with nonempty final stack never passes through the empty stack. -/
set_option autoImplicit false
namespace KroneckerUnitNonemptyExecution
open KroneckerStack KroneckerDebtUnits

theorem execute_from_empty (es : List Edge) (b : ℤ) (t : UnitState)
    (h : unitExecute es ⟨b,[]⟩=some t) : es=[] ∧ t=⟨b,[]⟩ := by
  cases es with
  | nil => simp only [unitExecute,Option.some.injEq] at h; exact ⟨rfl,h.symm⟩
  | cons e es => simp [unitExecute,unitStep] at h

theorem execute_nonempty_source {es : List Edge} {s t : UnitState}
    (h : unitExecute es s=some t) (ht : t.stack≠[]) : s.stack≠[] := by
  rcases s with ⟨b,xs⟩
  intro hx
  change xs=[] at hx
  subst xs
  obtain ⟨_,rfl⟩ := execute_from_empty es b t h
  exact ht rfl

end KroneckerUnitNonemptyExecution
end

/- Original module: KroneckerUnitStepBottom -/
section
/-! Every step with a nonempty result preserves the bottom debt unit. -/
set_option autoImplicit false
namespace KroneckerUnitStepBottom
open KroneckerStack KroneckerDebtUnits

theorem unit_step_bottom {s t : UnitState} {e : Edge}
    (h : unitStep s e=some t) (ht : t.stack≠[]) : t.stack.getLast?=s.stack.getLast? := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simp [unitStep] at h
  | cons x xs =>
    cases e with
    | H g =>
      simp only [unitStep,Option.some.injEq] at h
      subst t
      simp [List.getLast?_cons]
    | V g =>
      simp only [unitStep] at h
      split at h
      next hg =>
        cases h
        cases xs with
        | nil => exact False.elim (ht rfl)
        | cons y ys => simp
      next hg => contradiction

end KroneckerUnitStepBottom
end

/- Original module: KroneckerUnitExecutionBottom -/
section
/-! The protected outer debt unit is unchanged throughout a successful nonempty execution. -/
set_option autoImplicit false
namespace KroneckerUnitExecutionBottom
open KroneckerStack KroneckerDebtUnits KroneckerUnitNonemptyExecution KroneckerUnitStepBottom

theorem unit_execute_bottom {es : List Edge} {s t : UnitState}
    (h : unitExecute es s=some t) (ht : t.stack≠[]) : t.stack.getLast?=s.stack.getLast? := by
  induction es generalizing s with
  | nil => simp only [unitExecute,Option.some.injEq] at h; cases h; rfl
  | cons e es ih =>
    cases hs : unitStep s e with
    | none => simp [unitExecute,hs] at h
    | some u =>
      have hu : unitExecute es u=some t := by simpa [unitExecute,hs] using h
      exact (ih hu).trans (unit_step_bottom hs (execute_nonempty_source hu ht))

end KroneckerUnitExecutionBottom
end

/- Original module: KroneckerUnitBalanceRaise -/
section
/-! Raising balance alone weakens a uniformly translated comparison state. -/
set_option autoImplicit false
namespace KroneckerUnitBalanceRaise
open KroneckerDebtUnits KroneckerUnitShift KroneckerUnitStepWeakening

def raiseBalance (d : ℤ) (s : UnitState) : UnitState := ⟨s.balance+d,s.stack⟩

theorem baselines_le_shift (xs : List ℤ) (d : ℤ) (hd : 0 ≤ d) :
    List.Forall₂ (· ≤ ·) xs (xs.map (fun x => x+d)) := by
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih => exact List.Forall₂.cons (by change x ≤ x+d; omega) ih

theorem raised_weaker_shift (s : UnitState) (d : ℤ) (hd : 0 ≤ d) :
    Weaker (raiseBalance d s) (shift d s) :=
  ⟨rfl,baselines_le_shift s.stack d hd⟩

end KroneckerUnitBalanceRaise
end

/- Original module: KroneckerUnitRaisedExecution -/
section
/-! Simulate the suffix after omitting a positive vertical balance decrement. -/
set_option autoImplicit false
namespace KroneckerUnitRaisedExecution
open KroneckerStack KroneckerDebtUnits KroneckerUnitShift KroneckerUnitStepWeakening
open KroneckerUnitExecutionWeakening KroneckerUnitBalanceRaise

theorem execute_raised {es : List Edge} {s t : UnitState}
    (h : unitExecute es s=some t) (d : ℤ) (hd : 0 ≤ d) :
    ∃ v,unitExecute es (raiseBalance d s)=some v ∧ Weaker v (shift d t) :=
  unit_execute_weaker (raised_weaker_shift s d hd) (unit_execute_shift h d)

theorem singleton_from_bottom (s : UnitState) (b a z : ℤ)
    (hw : Weaker s ⟨b,[z]⟩) (hb : s.stack.getLast?=some a) : s=⟨b,[a]⟩ := by
  rcases s with ⟨c,xs⟩
  obtain ⟨hc,hxs⟩ := hw
  cases hxs with
  | @cons x y xs ys hxy htail =>
    cases htail
    have he : x=a := by simpa using hb
    cases he
    cases hc
    rfl

end KroneckerUnitRaisedExecution
end
end

section

/- Original module: KroneckerUnitLoopDeletion -/
section
/-! Delete a specified vertical step by lowering its traced horizontal source by one. -/
set_option autoImplicit false
namespace KroneckerUnitLoopDeletion
open KroneckerStack KroneckerDebtUnits KroneckerLowerOneHorizontal KroneckerProtectedRootBacktrace
open KroneckerUnitConcatenation KroneckerUnitNonemptyExecution KroneckerUnitExecutionBottom
open KroneckerUnitRaisedExecution KroneckerUnitBalanceRaise KroneckerUnitShift KroneckerUnitStepWeakening

theorem loop_delete (b a c : ℤ) (h : ℕ) (xs ys : List Edge)
    (hrun : unitExecute (xs++(.V h::ys)) ⟨b,[a]⟩=some ⟨c,[a]⟩) :
    ∃ xs',LowerOne xs xs' ∧ unitExecute (xs'++ys) ⟨b,[a]⟩=some ⟨c+(h : ℤ),[a]⟩ := by
  obtain ⟨p,hp,hq⟩ := unit_execute_split hrun
  rcases p with ⟨d,ps⟩
  cases ps with
  | nil => simp [unitExecute,unitStep] at hq
  | cons z zs =>
    simp only [unitExecute,unitStep] at hq
    split at hq
    next hz =>
      simp only [Option.bind_some] at hq
      have hne : zs≠[] := execute_nonempty_source hq (by simp)
      obtain ⟨xs',hl,hpre⟩ := protected_root_backtrace b a z d xs zs hne hp
      obtain ⟨v,hv,hw⟩ := execute_raised hq (h : ℤ) (by omega)
      have hpost : unitExecute ys ⟨d,zs⟩=some v := by
        simpa [raiseBalance] using hv
      have hwhole : unitExecute (xs'++ys) ⟨b,[a]⟩=some v := by
        rw [unit_execute_append,hpre]
        exact hpost
      have hlen : v.stack.length=1 := by
        simpa [shift] using List.Forall₂.length_eq hw.2
      have hvne : v.stack≠[] := by intro he; simp [he] at hlen
      have hbottom : v.stack.getLast?=some a := by
        simpa using unit_execute_bottom hwhole hvne
      have heq := singleton_from_bottom v (c+(h : ℤ)) a (a+(h : ℤ))
        (by simpa [shift] using hw) hbottom
      exact ⟨xs',hl,by simpa [heq] using hwhole⟩
    next hz => simp_all

end KroneckerUnitLoopDeletion
end

/- Original module: KroneckerUnitParentExecution -/
section
/-! Execute an actual connected node inside a protected outer singleton. -/
set_option autoImplicit false
namespace KroneckerUnitParentExecution
open KroneckerStack KroneckerDebtUnits KroneckerUnitNodeDictionary KroneckerUnitShift KroneckerUnitOuterStack

theorem node_in_parent {es : List Edge} {c : ℕ} (hn : NodeRun es c) (b floor : ℤ) :
    unitExecute es ⟨b,[floor]⟩=some ⟨b+(c : ℤ)+1,[floor]⟩ := by
  obtain ⟨g,rest,rfl,hr⟩ := node_to_units hn
  have h := unit_execute_outer (unit_execute_shift hr b) [floor]
  simpa [unitExecute,unitStep,shift,outer,add_assoc,add_comm] using h

end KroneckerUnitParentExecution
end

/- Original module: KroneckerUnitPreservingLoopShell -/
section
/-! A one-unit preserving shell closes any valid loop with the prescribed balance increase. -/
set_option autoImplicit false
namespace KroneckerUnitPreservingLoopShell
open KroneckerStack KroneckerDebtUnits KroneckerUnitNodeDictionary KroneckerUnitConcatenation
open KroneckerUnitShellReserve

def loopShell (u v : ℕ) (es : List Edge) : List Edge :=
  .H (u+1)::(List.replicate u (.V 0)++es++((.H v::List.replicate v (.V 0))++[.V 2]))

theorem unit_single_prefix (u : ℕ) :
    unitExecute (List.replicate u (.V 0)) ⟨1,List.replicate (u+1) 1⟩=some ⟨1,[1]⟩ := by
  have h := unit_zeros_pop u 1 1 [1] le_rfl
  simpa only [← List.replicate_succ'] using h

theorem loop_shell_node (u v c : ℕ) (es : List Edge)
    (he : unitExecute es ⟨1,[1]⟩=some ⟨(c : ℤ)+2,[1]⟩) :
    NodeRun (loopShell u v es) c := by
  apply units_to_node
  refine ⟨u,_,rfl,?_⟩
  rw [List.append_assoc,unit_execute_append,unit_single_prefix]
  simp only [Option.bind_some]
  rw [unit_execute_append,he]
  exact unit_shell_suffix v c

end KroneckerUnitPreservingLoopShell
end
end

