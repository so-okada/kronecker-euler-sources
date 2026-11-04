import KroneckerUnitShift

/- Original module: KroneckerUnitTailWeakening -/
section
/-! Removing the first baseline and appending a smaller outer baseline weakens an ordered stack. -/
set_option autoImplicit false
namespace KroneckerUnitTailWeakening

theorem shifted_tail_le (xs : List ℤ) (a : ℤ)
    (ho : xs.Pairwise (fun x y => y ≤ x)) (ha : ∀ x ∈ xs, a ≤ x) :
    List.Forall₂ (· ≤ ·) ((xs++[a]).tail) xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simpa using (List.Forall₂.cons (ha x (by simp)) List.Forall₂.nil)
    | cons y ys =>
      have hxy : y ≤ x := (List.pairwise_cons.mp ho).1 y (by simp)
      have ht := ih (List.pairwise_cons.mp ho).2 (fun z hz => ha z (by simp [hz]))
      exact List.Forall₂.cons hxy ht

theorem append_floor_ordered (xs : List ℤ) (a : ℤ)
    (ho : xs.Pairwise (fun x y => y ≤ x)) (ha : ∀ x ∈ xs, a ≤ x) :
    (xs++[a]).Pairwise (fun x y => y ≤ x) := by
  rw [List.pairwise_append]
  refine ⟨ho,by simp,?_⟩
  intro x hx y hy
  simpa only [List.mem_singleton.mp hy] using ha x hx

end KroneckerUnitTailWeakening
end

/- Original module: KroneckerUnitInsertionSimulation -/
section
/-! The extra zero edge transfers one unit of debt toward the enclosing baseline. -/
set_option autoImplicit false
namespace KroneckerUnitInsertionSimulation
open KroneckerStack KroneckerDebtUnits KroneckerUnitOuterStack
open KroneckerUnitFloorBounds KroneckerUnitOrderBounds KroneckerUnitStepWeakening
open KroneckerUnitExecutionWeakening KroneckerUnitTailWeakening

def afterInsertion (a : ℤ) (s : UnitState) : UnitState :=
  ⟨s.balance,(s.stack++[a,a]).tail⟩

theorem zero_insertion_step (a : ℤ) (s : UnitState)
    (hf : FloorBound a s) (ho : OrderedBounded s) :
    unitStep (outer s [a,a]) (.V 0)=some (afterInsertion a s) := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => simpa [unitStep,outer,afterInsertion] using hf.1
  | cons x xs =>
    have hx : x ≤ b := ho.2 x (by simp)
    simp [unitStep,outer,afterInsertion,hx]

theorem insertion_weaker (a : ℤ) (s : UnitState)
    (hf : FloorBound a s) (ho : OrderedBounded s) :
    Weaker (afterInsertion a s) (outer s [a]) := by
  refine ⟨rfl,?_⟩
  have hs := shifted_tail_le (s.stack++[a]) a
    (append_floor_ordered s.stack a ho.1 hf.2)
    (by intro x hx; rcases List.mem_append.mp hx with hx | hx
        · exact hf.2 x hx
        · exact (List.mem_singleton.mp hx).ge)
  simpa [afterInsertion,outer,List.append_assoc] using hs

theorem singleton_from_bounds (a b : ℤ) (s : UnitState)
    (hf : FloorBound a s) (hw : Weaker s ⟨b,[a]⟩) : s=⟨b,[a]⟩ := by
  obtain ⟨hb,hs⟩ := hw
  cases s with
  | mk c xs =>
    cases hs with
    | @cons x y xs ys hhead htail =>
      cases htail
      have hx := hf.2 x (by simp)
      have he := le_antisymm hhead hx
      simp_all

end KroneckerUnitInsertionSimulation
end

/- Original module: KroneckerUnitInteriorInsertion -/
section
/-! Inserting one zero vertical edge at any split consumes exactly one of two outer debt units. -/
set_option autoImplicit false
namespace KroneckerUnitInteriorInsertion
open KroneckerStack KroneckerDebtUnits KroneckerUnitConcatenation KroneckerUnitOuterStack
open KroneckerUnitFloorBounds KroneckerUnitOrderBounds KroneckerUnitInvariantExecution
open KroneckerUnitInsertionSimulation KroneckerUnitExecutionWeakening

theorem insert_zero_inside (a b : ℤ) (xs ys : List Edge) (s : UnitState)
    (hf : FloorBound a s) (ho : OrderedBounded s)
    (h : unitExecute (xs++ys) s=some ⟨b,[]⟩) :
    unitExecute (xs++(.V 0::ys)) (outer s [a,a])=some ⟨b,[a]⟩ := by
  obtain ⟨p,hp,hq⟩ := unit_execute_split h
  have hpf := unit_execute_floor hf hp
  have hpo := unit_execute_ordered ho hp
  have hpre := unit_execute_outer hp [a,a]
  have hpost := unit_execute_outer hq [a]
  obtain ⟨v,hv,hvw⟩ := unit_execute_weaker (insertion_weaker a p hpf hpo) hpost
  have hpf' : FloorBound a (outer p [a,a]) := by
    refine ⟨hpf.1,?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hpf.2 x hx
    · have he : x=a := by simpa using hx
      exact he.ge
  have hstep := zero_insertion_step a p hpf hpo
  have hvf := unit_execute_floor (unit_step_floor hpf' hstep) hv
  have heq : v=⟨b,[a]⟩ := singleton_from_bounds a b v hvf (by simpa [outer] using hvw)
  rw [unit_execute_append,hpre]
  simpa only [Option.bind_some,unitExecute,hstep,heq] using hv

end KroneckerUnitInteriorInsertion
end

/- Original module: KroneckerUnitShellReserve -/
section
/-! Explicit debt-unit executions of the shell prefix and suffix. -/
set_option autoImplicit false
namespace KroneckerUnitShellReserve
open KroneckerStack KroneckerDebtUnits KroneckerUnitConcatenation

theorem unit_zeros_pop (n : ℕ) (b a : ℤ) (xs : List ℤ) (ha : a ≤ b) :
    unitExecute (List.replicate n (.V 0)) ⟨b,List.replicate n a++xs⟩=some ⟨b,xs⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,unitExecute,unitStep,ha] using ih

theorem unit_single_run (g : ℕ) (s : UnitState) (hne : s.stack≠[]) :
    unitExecute (.H g::List.replicate g (.V 0)) s=some ⟨s.balance+1,s.stack⟩ := by
  rcases s with ⟨b,xs⟩
  cases xs with
  | nil => contradiction
  | cons x xs =>
    simpa only [unitExecute,unitStep,Option.bind_some] using unit_zeros_pop g (b+1) (b+1) (x::xs) le_rfl

theorem unit_shell_prefix (u : ℕ) :
    unitExecute (List.replicate u (.V 0)) ⟨1,List.replicate (u+2) 1⟩=some ⟨1,[1,1]⟩ := by
  have h := unit_zeros_pop u 1 1 [1,1] le_rfl
  have hr : List.replicate (u+2) (1 : ℤ)=List.replicate u 1++[1,1] := by
    rw [List.replicate_add]
    rfl
  rw [hr]
  exact h

theorem unit_shell_suffix (v c : ℕ) :
    unitExecute ((.H v::List.replicate v (.V 0))++[.V 2]) ⟨(c : ℤ)+2,[1]⟩=
      some ⟨(c : ℤ)+1,[]⟩ := by
  rw [unit_execute_append,unit_single_run v _ (by simp)]
  have hc : (1 : ℤ) ≤ (c : ℤ)+2+1-2 := by omega
  simp [unitExecute,unitStep,hc]
  omega

end KroneckerUnitShellReserve
end
