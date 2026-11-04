import Mathlib.Tactic

/-!
The stack in Definition 2.6 of the manuscript. Colors do not affect execution;
`ColoredEdge` retains the choices when counting colored configurations.
No manuscript theorem is assumed in this file.
-/
set_option autoImplicit false
namespace KroneckerStack

inductive Edge where
  | H (grade : ℕ)
  | V (grade : ℕ)
  deriving DecidableEq, Repr

def Edge.grade : Edge → ℕ
  | .H g => g
  | .V g => g

def Edge.credit : Edge → ℤ
  | .H _ => 1
  | .V g => -(g : ℤ)

def Edge.debtChange : Edge → ℤ
  | .H g => g
  | .V _ => -1

structure ColoredEdge (m : ℕ) where
  edge : Edge
  legal : edge.grade ≤ m
  color : Fin (Nat.choose m edge.grade)

structure Node where
  debt : ℕ
  baseline : ℤ
  deriving DecidableEq, Repr

structure State where
  balance : ℤ
  stack : List Node
  deriving DecidableEq, Repr

def step (s : State) (e : Edge) : Option State :=
  match s.stack with
  | [] => none
  | t :: ts =>
    match e with
    | .H g =>
      some ⟨s.balance + 1,
        if g = 0 then t :: ts else ⟨g, s.balance + 1⟩ :: t :: ts⟩
    | .V g =>
      if 0 < t.debt ∧ t.baseline ≤ s.balance - (g : ℤ) then
        some ⟨s.balance - (g : ℤ),
          if t.debt = 1 then ts else ⟨t.debt - 1, t.baseline⟩ :: ts⟩
      else none

def execute : List Edge → State → Option State
  | [], s => some s
  | e :: es, s => (step s e).bind (execute es)

/-- Root positivity, no early closure, and closure at the last edge are all
checked. The final balance equals one plus the surplus. -/
def accept (m : ℕ) (es : List Edge) : Option ℕ := do
  if !(es.all fun e => e.grade ≤ m) then none
  else match es with
  | .H g :: rest =>
    if g = 0 then none else do
      let s ← execute rest ⟨1, [⟨g, 1⟩]⟩
      if s.stack = [] ∧ 1 ≤ s.balance then some (s.balance - 1).toNat else none
  | _ => none

def Connected (m : ℕ) (es : List Edge) (c : ℕ) : Prop := accept m es = some c

def credit (es : List Edge) : ℤ := (es.map Edge.credit).sum

def debtTotal (s : State) : ℤ := (s.stack.map fun n => (n.debt : ℤ)).sum

theorem step_debt {s t : State} {e : Edge} (h : step s e = some t) :
    debtTotal t = debtTotal s + e.debtChange := by
  cases s with
  | mk b st =>
    cases st with
    | nil => simp [step] at h
    | cons n ns =>
      cases e with
      | H g =>
        simp only [step] at h
        cases h
        by_cases hg : g=0 <;> simp [debtTotal,Edge.debtChange,hg,add_comm]
      | V g =>
        simp only [step] at h
        split at h
        next hv =>
          cases h
          by_cases hd : n.debt=1
          · simp [debtTotal,Edge.debtChange,hd]
          · have hn : 1≤n.debt := by omega
            simp only [debtTotal,ite_eq_right hd,List.map_cons,List.sum_cons,Edge.debtChange,
              Nat.cast_sub hn,Nat.cast_one]
            ring
        next hv => contradiction

theorem execute_debt {es : List Edge} {s t : State}
    (h : execute es s = some t) :
    debtTotal t = debtTotal s + (es.map Edge.debtChange).sum := by
  induction es generalizing s with
  | nil =>
    simp only [execute,Option.some.injEq] at h
    subst t
    simp
  | cons e es ih =>
    cases he : step s e with
    | none => simp [execute,he] at h
    | some u =>
      have hu : execute es u = some t := by simpa [execute,he] using h
      rw [ih hu,step_debt he]
      simp [add_assoc]

theorem step_balance {s t : State} {e : Edge} (h : step s e = some t) :
    t.balance = s.balance + e.credit := by
  cases s with
  | mk b st =>
    cases st with
    | nil => simp [step] at h
    | cons n ns =>
      cases e <;> simp only [step] at h
      · cases h; rfl
      · split at h
        · cases h; simp [Edge.credit, sub_eq_add_neg]
        · contradiction

theorem execute_balance {es : List Edge} {s t : State}
    (h : execute es s = some t) : t.balance = s.balance + credit es := by
  induction es generalizing s with
  | nil =>
    simp only [execute, Option.some.injEq] at h
    subst t
    simp [credit]
  | cons e es ih =>
    cases he : step s e with
    | none => simp [execute, he] at h
    | some u =>
      have hu : execute es u = some t := by simpa [execute, he] using h
      rw [ih hu, step_balance he]
      simp [credit, add_assoc]

theorem execute_append (xs ys : List Edge) (s : State) :
    execute (xs ++ ys) s = (execute xs s).bind (execute ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons e xs ih =>
    simp only [List.cons_append, execute]
    cases step s e <;> simp [ih]

theorem no_execution_after_root_closes (e : Edge) (es : List Edge) (b : ℤ) :
    execute (e :: es) ⟨b, []⟩ = none := by simp [execute, step]

theorem no_empty_connected (m c : ℕ) : ¬ Connected m [] c := by
  simp [Connected, accept]

theorem no_zero_root (m c : ℕ) (es : List Edge) :
    ¬ Connected m (.H 0 :: es) c := by
  simp [Connected, accept]

theorem no_vertical_root (m c g : ℕ) (es : List Edge) :
    ¬ Connected m (.V g :: es) c := by
  simp [Connected, accept]

def shiftNode (d : ℤ) (n : Node) : Node := ⟨n.debt, n.baseline + d⟩

def extend (d : ℤ) (outer : List Node) (s : State) : State :=
  ⟨s.balance + d, s.stack.map (shiftNode d) ++ outer⟩

/-- Executing a connected piece inside an enclosing stack preserves that
enclosing stack. All balances and baselines of the piece are translated. -/
theorem step_extend {s t : State} {e : Edge} (h : step s e = some t)
    (d : ℤ) (outer : List Node) :
    step (extend d outer s) e = some (extend d outer t) := by
  cases s with
  | mk b st =>
    cases st with
    | nil => simp [step] at h
    | cons n ns =>
      cases e with
      | H g =>
        simp only [step] at h
        cases h
        by_cases hg : g = 0 <;> simp [step, extend, shiftNode, hg, add_assoc, add_comm]
      | V g =>
        simp only [step] at h
        split at h
        next hn =>
          cases h
          have ht : 0 < n.debt ∧ n.baseline + d ≤ b + d - (g : ℤ) := by
            constructor
            · exact hn.1
            · omega
          by_cases hd : n.debt = 1 <;>
            simp [step, extend, shiftNode, hn, ht, hd, sub_add_eq_add_sub]
        next hn => contradiction

theorem execute_extend {es : List Edge} {s t : State}
    (h : execute es s = some t) (d : ℤ) (outer : List Node) :
    execute es (extend d outer s) = some (extend d outer t) := by
  induction es generalizing s with
  | nil => simp only [execute, Option.some.injEq] at h; subst t; rfl
  | cons e es ih =>
    cases he : step s e with
    | none => simp [execute, he] at h
    | some u =>
      have hu : execute es u = some t := by simpa [execute, he] using h
      simp only [execute, step_extend he d outer, Option.bind_some]
      exact ih hu

/-- Uncolored connected-node predicate with its final balance specified. -/
def NodeRun (es : List Edge) (c : ℕ) : Prop :=
  ∃ g rest, es = .H (g+1) :: rest ∧
    execute rest ⟨1, [⟨g+1, 1⟩]⟩ = some ⟨(c : ℤ)+1, []⟩

theorem node_credit {es : List Edge} {c : ℕ} (h : NodeRun es c) :
    credit es = (c : ℤ) + 1 := by
  obtain ⟨g, rest, rfl, hr⟩ := h
  have hb := execute_balance hr
  simp only at hb
  simp only [credit, List.map_cons, List.sum_cons, Edge.credit]
  unfold credit at hb
  omega

theorem node_debt_balance {es : List Edge} {c : ℕ} (h : NodeRun es c) :
    (es.map Edge.debtChange).sum=0 := by
  obtain ⟨g,rest,rfl,hr⟩ := h
  have hd := execute_debt hr
  simpa [debtTotal,Edge.debtChange] using hd.symm

theorem execute_node {es : List Edge} {c : ℕ} (h : NodeRun es c)
    (s : State) (hne : s.stack ≠ []) :
    execute es s = some ⟨s.balance + (c : ℤ) + 1, s.stack⟩ := by
  obtain ⟨g, rest, rfl, hr⟩ := h
  have he := execute_extend hr s.balance s.stack
  cases s with
  | mk b st =>
    cases st with
    | nil => contradiction
    | cons n ns =>
      simpa [execute, step, extend, shiftNode, add_assoc, add_comm, add_left_comm] using he

theorem zeros_leave_one (n : ℕ) (b base : ℤ) (outer : List Node)
    (hb : base ≤ b) :
    execute (List.replicate n (.V 0)) ⟨b, ⟨n+1, base⟩ :: outer⟩ =
      some ⟨b, ⟨1, base⟩ :: outer⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ, execute, step, hb, Nat.add_eq_zero_iff] using ih

theorem zeros_close (n : ℕ) (b base : ℤ) (outer : List Node)
    (hb : base ≤ b) :
    execute (List.replicate (n+1) (.V 0)) ⟨b, ⟨n+1, base⟩ :: outer⟩ =
      some ⟨b, outer⟩ := by
  rw [List.replicate_add, execute_append, zeros_leave_one n b base outer hb]
  simp [execute, step, hb]

theorem execute_single_run (g : ℕ) (s : State) (hne : s.stack ≠ []) :
    execute (.H g :: List.replicate g (.V 0)) s =
      some ⟨s.balance + 1, s.stack⟩ := by
  cases s with
  | mk b st =>
    cases st with
    | nil => contradiction
    | cons n ns =>
      cases g with
      | zero => simp [execute, step]
      | succ g =>
        simp only [execute, step, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
          ↓reduceIte, Option.bind_some]
        exact zeros_close g (b+1) (b+1) (n :: ns) le_rfl

theorem one_run_node (g : ℕ) : NodeRun (.H (g+1) :: List.replicate (g+1) (.V 0)) 0 := by
  refine ⟨g, _, rfl, ?_⟩
  exact zeros_close g 1 1 [] le_rfl

/-- A list of connected children contributes one unit plus its surplus for
each child, while leaving the enclosing node's debt unchanged. -/
theorem execute_children (xs : List (List Edge × ℕ))
    (hx : ∀ p ∈ xs, NodeRun p.1 p.2) (s : State) (hne : s.stack ≠ []) :
    execute (xs.flatMap Prod.fst) s =
      some ⟨s.balance + ((xs.map Prod.snd).sum : ℤ) + (xs.length : ℤ), s.stack⟩ := by
  induction xs generalizing s with
  | nil => simp [execute]
  | cons x xs ih =>
    rw [List.flatMap_cons, execute_append, execute_node (hx x (by simp)) s hne]
    simp only [Option.bind_some]
    rw [ih (by intro p hp; exact hx p (by simp [hp]))
      (⟨s.balance + (x.2 : ℤ) + 1, s.stack⟩ : State) hne]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    congr 1
    congr 1
    ring

/-- The shell in Lemma 3.3, before imposing the upper bound on grades.
`v` here is the final run type minus one. -/
def shell (u v e : ℕ) (xs : List (List Edge × ℕ)) : List Edge :=
  [.H (u+1)] ++ List.replicate u (.V 0) ++ xs.flatMap Prod.fst ++
    [.H v] ++ List.replicate v (.V 0) ++ [.V (xs.length+1+e)]

theorem shell_node (u v e : ℕ) (xs : List (List Edge × ℕ))
    (hx : ∀ p ∈ xs, NodeRun p.1 p.2)
    (he : e ≤ (xs.map Prod.snd).sum) :
    NodeRun (shell u v e xs) ((xs.map Prod.snd).sum-e) := by
  refine ⟨u, List.replicate u (.V 0) ++ xs.flatMap Prod.fst ++
    ((.H v :: List.replicate v (.V 0)) ++ [.V (xs.length+1+e)]), ?_, ?_⟩
  · simp [shell, List.append_assoc]
  have hzero := zeros_leave_one u 1 1 [] le_rfl
  have hchild := execute_children xs hx (⟨1, [⟨1,1⟩]⟩ : State) (by decide)
  rw [List.append_assoc, execute_append, hzero]
  simp only [Option.bind_some]
  rw [execute_append, hchild]
  simp only [Option.bind_some]
  rw [execute_append, execute_single_run v _ (by simp)]
  simp only [Option.bind_some]
  have he' : (e : ℤ) ≤ ((xs.map Prod.snd).sum : ℤ) := by exact_mod_cast he
  have hle : (1 : ℤ) ≤
      1 + ((xs.map Prod.snd).sum : ℤ) + (xs.length : ℤ) + 1 -
      ((xs.length+1+e : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_one]
    omega
  simp only [execute, step, Nat.zero_lt_one, true_and, ite_eq_left hle,
    Option.bind_some]
  congr 2
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub he]
  omega

theorem node_connected {m c : ℕ} {es : List Edge} (h : NodeRun es c)
    (hlegal : ∀ edge ∈ es, edge.grade ≤ m) : Connected m es c := by
  obtain ⟨g, rest, rfl, hr⟩ := h
  have hall : ([Edge.H (g+1)] ++ rest).all (fun e => decide (e.grade ≤ m)) = true := by
    simpa using hlegal
  unfold Connected accept
  simp only [List.singleton_append] at hall
  simp [hall, hr]

theorem connected_node {m c : ℕ} {es : List Edge} (h : Connected m es c) :
    NodeRun es c := by
  unfold Connected accept at h
  split at h
  · contradiction
  · cases es with
    | nil => simp at h
    | cons e rest =>
      cases e with
      | V g => simp at h
      | H g =>
        cases g with
        | zero => simp at h
        | succ g =>
          simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] at h
          cases hr : execute rest ⟨1, [⟨g+1,1⟩]⟩ with
          | none => simp [hr] at h
          | some s =>
            simp only [hr] at h
            change (if s.stack = [] ∧ 1 ≤ s.balance then
              some (s.balance-1).toNat else none) = some c at h
            split at h
            next hs =>
              simp only [Option.some.injEq] at h
              have hb : s.balance = (c : ℤ)+1 := by omega
              refine ⟨g,rest,rfl,?_⟩
              simpa [← hb, ← hs.1] using hr
            next hs => contradiction

theorem connected_grades {m c : ℕ} {es : List Edge} (h : Connected m es c) :
    ∀ e ∈ es, e.grade ≤ m := by
  unfold Connected accept at h
  split at h
  · contradiction
  · rename_i hg
    simpa using hg

theorem connected_iff {m c : ℕ} {es : List Edge} :
    Connected m es c ↔ NodeRun es c ∧ ∀ e ∈ es, e.grade ≤ m :=
  ⟨fun h => ⟨connected_node h, connected_grades h⟩,
    fun h => node_connected h.1 h.2⟩

theorem connected_surplus {m c : ℕ} {es : List Edge} (h : Connected m es c) :
    credit es = (c : ℤ)+1 := node_credit (connected_node h)

theorem colored_lift (m : ℕ) (es : List Edge) (h : ∀ e ∈ es, e.grade ≤ m) :
    ∃ cs : List (ColoredEdge m), cs.map ColoredEdge.edge = es := by
  induction es with
  | nil => exact ⟨[],rfl⟩
  | cons e es ih =>
    have he := h e (by simp)
    obtain ⟨cs,hcs⟩ := ih (by intro e he; exact h e (by simp [he]))
    refine ⟨⟨e,he,⟨0,Nat.choose_pos he⟩⟩ :: cs, ?_⟩
    simp [hcs]

theorem shell_grades (m u v e : ℕ) (xs : List (List Edge × ℕ))
    (hu : u+1 ≤ m) (hv : v ≤ m) (hlast : xs.length+1+e ≤ m)
    (hx : ∀ p ∈ xs, ∀ edge ∈ p.1, edge.grade ≤ m) :
    ∀ edge ∈ shell u v e xs, edge.grade ≤ m := by
  intro edge hedge
  have hmid : ∀ edge ∈ xs.flatMap Prod.fst, edge.grade ≤ m := by
    intro z hz
    obtain ⟨p,hp,hz⟩ := List.mem_flatMap.mp hz
    exact hx p hp z hz
  simp only [shell, List.mem_append, List.mem_singleton] at hedge
  rcases hedge with (((((h | h) | h) | h) | h) | h)
  · subst edge; exact hu
  · have hh : edge = .V 0 := (List.mem_replicate.mp h).2
    subst edge; exact Nat.zero_le m
  · exact hmid edge h
  · subst edge; exact hv
  · have hh : edge = .V 0 := (List.mem_replicate.mp h).2
    subst edge; exact Nat.zero_le m
  · subst edge; exact hlast

theorem shell_connected (m u v e : ℕ) (xs : List (List Edge × ℕ))
    (hu : u+1 ≤ m) (hv : v ≤ m) (hlast : xs.length+1+e ≤ m)
    (hx : ∀ p ∈ xs, Connected m p.1 p.2) (he : e ≤ (xs.map Prod.snd).sum) :
    Connected m (shell u v e xs) ((xs.map Prod.snd).sum-e) := by
  exact node_connected (shell_node u v e xs (fun p hp => connected_node (hx p hp)) he)
    (shell_grades m u v e xs hu hv hlast (fun p hp => connected_grades (hx p hp)))

/-- Lemma 3.3 with the manuscript's run types u and v and its permitted
preserving/draining cases. The implementation's suffix parameter is v-1. -/
theorem manuscript_shell (m u v e : ℕ) (xs : List (List Edge × ℕ))
    (hm : 3≤m) (hu : 1≤u ∧ u≤m-1) (hv : 1≤v ∧ v≤m-1)
    (hx : ∀ p ∈ xs, Connected m p.1 p.2)
    (hcase : (xs.length≤2 ∧ e=0) ∨
      (xs.length=1 ∧ e=1 ∧ 1≤(xs.map Prod.snd).sum)) :
    Connected m (shell u (v-1) e xs) ((xs.map Prod.snd).sum-e) := by
  apply shell_connected m u (v-1) e xs (by omega) (by omega) _ hx
  · rcases hcase with ⟨hj,he⟩ | ⟨hj,he,hc⟩ <;> omega
  · rcases hcase with ⟨hj,he⟩ | ⟨hj,he,hc⟩ <;> omega

theorem unary_shell_injective (u v e c : ℕ) :
    Function.Injective (fun es : List Edge => shell u v e [(es,c)]) := by
  intro xs ys h
  have h' : ([Edge.H (u+1)] ++ List.replicate u (.V 0)) ++
      (xs ++ ([Edge.H v] ++ List.replicate v (.V 0) ++ [.V (2+e)])) =
      ([Edge.H (u+1)] ++ List.replicate u (.V 0)) ++
      (ys ++ ([Edge.H v] ++ List.replicate v (.V 0) ++ [.V (2+e)])) := by
    simpa [shell,List.append_assoc] using h
  exact List.append_cancel_right (List.append_cancel_left h')

def Edge.isHorizontal : Edge → Bool
  | .H _ => true
  | .V _ => false

def shape (es : List Edge) : List Bool := es.map Edge.isHorizontal

def runShape (r : ℕ) : List Bool := true :: List.replicate r false

def Filling (m : ℕ) (rs : List ℕ) : Prop :=
  ∃ es : List Edge, Connected m es 0 ∧ shape es = rs.flatMap runShape

theorem one_run_filling {m r : ℕ} (hr : 1≤r) (hbound : r≤m) : Filling m [r] := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  refine ⟨.H (g+1) :: List.replicate (g+1) (.V 0), ?_, ?_⟩
  · exact node_connected (one_run_node g) (by
      intro edge h
      simp only [List.mem_cons, List.mem_replicate] at h
      rcases h with h | ⟨_,h⟩ <;> subst edge
      · exact hbound
      · exact Nat.zero_le m)
  · simp [shape,runShape,Edge.isHorizontal]

theorem two_run_filling {m u v : ℕ} (hm : 1≤m) (hu : u+1≤m) (hv : 1≤v)
    (hvbound : v≤m) : Filling m [u,v] := by
  refine ⟨shell u (v-1) 0 [], ?_, ?_⟩
  · exact shell_connected m u (v-1) 0 [] hu (by omega) (by simp; omega)
      (by simp) (by simp)
  · have hv' : List.replicate (v-1) false ++ [false] = List.replicate v false := by
      rw [← List.replicate_succ']
      congr 1
      omega
    simp [shell,shape,runShape,Edge.isHorizontal,List.append_assoc,hv']

theorem wrap_filling {m u v : ℕ} {rs : List ℕ} (hm : 2≤m) (hu : u+1≤m)
    (hv : 1≤v) (hvbound : v≤m) (h : Filling m rs) : Filling m (u :: rs ++ [v]) := by
  obtain ⟨es,hes,hshape⟩ := h
  refine ⟨shell u (v-1) 0 [(es,0)], ?_, ?_⟩
  · exact shell_connected m u (v-1) 0 [(es,0)] hu (by omega) (by simp; omega)
      (by simpa using hes) (by simp)
  · have hv' : List.replicate (v-1) false ++ [false] = List.replicate v false := by
      rw [← List.replicate_succ']
      congr 1
      omega
    simpa [shell,shape,runShape,Edge.isHorizontal,List.append_assoc,hv'] using
      congrArg (fun mid => runShape u ++ mid ++ runShape v) hshape

/-- The canonical filling in Definition 3.4, for every nonempty run
word of the stated alphabet. This is an existence proof, not a finite test. -/
theorem canonical_filling (m : ℕ) (hm : 3≤m) (rs : List ℕ) (hne : rs≠[])
    (hr : ∀ r ∈ rs, 1≤r ∧ r≤m-1) : Filling m rs := by
  have hfill : ∀ n : ℕ, ∀ rs : List ℕ, rs.length=n → rs≠[] →
      (∀ r ∈ rs, 1≤r ∧ r≤m-1) → Filling m rs := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro rs hn hne hr
      cases rs with
      | nil => contradiction
      | cons u tail =>
        have hu := hr u (by simp)
        by_cases ht : tail=[]
        · subst tail
          exact one_run_filling hu.1 (by omega)
        · obtain ⟨mid,v,htail⟩ : ∃ mid v, tail=mid++[v] :=
            ⟨tail.dropLast,tail.getLast ht,(List.dropLast_append_getLast ht).symm⟩
          subst tail
          have hv := hr v (by simp)
          by_cases hmid : mid=[]
          · subst mid
            exact two_run_filling (by omega) (by omega) hv.1 (by omega)
          · apply wrap_filling (by omega) (by omega) hv.1 (by omega)
            have hlt : mid.length<n := by simp at hn; omega
            apply ih mid.length hlt mid rfl hmid
            intro r hmemb
            exact hr r (by simp [hmemb])
  exact hfill rs.length rs rfl hne hr

theorem canonical_colored_filling (m : ℕ) (hm : 3≤m) (rs : List ℕ) (hne : rs≠[])
    (hr : ∀ r ∈ rs, 1≤r ∧ r≤m-1) :
    ∃ cs : List (ColoredEdge m), Connected m (cs.map ColoredEdge.edge) 0 ∧
      shape (cs.map ColoredEdge.edge) = rs.flatMap runShape := by
  obtain ⟨es,hc,hs⟩ := canonical_filling m hm rs hne hr
  obtain ⟨cs,hcs⟩ := colored_lift m es (connected_grades hc)
  exact ⟨cs,by simpa [hcs] using hc,by simpa [hcs] using hs⟩

#print axioms shell_node
#print axioms connected_iff
#print axioms connected_surplus
#print axioms shell_connected
#print axioms unary_shell_injective
#print axioms canonical_colored_filling

theorem example_210 : Connected 3 [.H 2, .V 0, .H 1, .V 0, .H 0, .V 2] 0 := by
  unfold Connected
  decide

theorem example_300a : Connected 3 [.H 3, .V 0, .H 0, .V 0, .H 0, .V 2] 0 := by
  unfold Connected
  decide

theorem example_300b : Connected 3 [.H 3, .V 0, .H 0, .V 1, .H 0, .V 1] 0 := by
  unfold Connected
  decide

end KroneckerStack
