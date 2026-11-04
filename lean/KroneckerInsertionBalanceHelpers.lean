import KroneckerListInsertion
import KroneckerNaturalNodes

/-! The balance and connectedness helper for insertion at an arbitrary
interior character boundary. The original root grade is increased by one. -/
set_option autoImplicit false
namespace KroneckerInsertionBalanceHelpers
open KroneckerStack KroneckerDebtUnits KroneckerUnitConcatenation
open KroneckerUnitOuterStack KroneckerUnitFloorBounds KroneckerUnitOrderBounds
open KroneckerUnitInvariantExecution KroneckerUnitTailWeakening
open KroneckerUnitStepWeakening KroneckerUnitExecutionWeakening
open KroneckerUnitNodeDictionary

theorem execute_nonempty_stack (xs : List Edge) (s t : UnitState)
    (hx : xs ≠ []) (he : unitExecute xs s = some t) : s.stack ≠ [] := by
  cases xs with
  | nil => contradiction
  | cons e xs =>
    intro hs
    simp [unitExecute, unitStep, hs] at he

theorem insert_one_zero (a b : ℤ) (xs ys : List Edge) (s : UnitState)
    (hy : ys ≠ []) (hf : FloorBound a s) (ho : OrderedBounded s)
    (he : unitExecute (xs ++ ys) s = some ⟨b, []⟩) :
    unitExecute (xs ++ (.V 0 :: ys)) (outer s [a]) = some ⟨b, []⟩ := by
  obtain ⟨p, hp, hq⟩ := unit_execute_split he
  have hpf := unit_execute_floor hf hp
  have hpo := unit_execute_ordered ho hp
  have hne := execute_nonempty_stack ys p ⟨b, []⟩ hy hq
  let p' : UnitState := ⟨p.balance, (p.stack ++ [a]).tail⟩
  have hstep : unitStep (outer p [a]) (.V 0) = some p' := by
    cases hs : p.stack with
    | nil => exact (hne hs).elim
    | cons x zs =>
      have hx : x ≤ p.balance := hpo.2 x (by simp [hs])
      simp [unitStep, outer, p', hs, hx]
  have hw : Weaker p' p :=
    ⟨rfl, shifted_tail_le p.stack a hpo.1 hpf.2⟩
  obtain ⟨v, hv, hweak⟩ := unit_execute_weaker hw hq
  have hvb : v.balance = b := hweak.1
  have hvs : v.stack = [] := by
    have hlen := List.Forall₂.length_eq hweak.2
    exact List.length_eq_zero_iff.mp (by simpa using hlen)
  have hve : v = ⟨b, []⟩ := by cases v; simp_all
  rw [unit_execute_append, unit_execute_outer hp [a]]
  simpa only [Option.bind_some, unitExecute, hstep, hve] using hv

/-- Exact arbitrary-root version of the insertion construction. Here `xs`
contains the old edges after the first horizontal edge and before the cut. -/
theorem root_insertion_node (g c : ℕ) (xs ys : List Edge) (hy : ys ≠ [])
    (he : unitExecute (xs ++ ys) ⟨1, List.replicate (g+1) 1⟩ =
      some ⟨(c : ℤ)+1, []⟩) :
    NodeRun (.H (g+2) :: (xs ++ (.V 0 :: ys))) c := by
  apply units_to_node
  refine ⟨g+1, xs ++ (.V 0 :: ys), rfl, ?_⟩
  have h := insert_one_zero 1 ((c : ℤ)+1) xs ys
    ⟨1, List.replicate (g+1) 1⟩ hy
    (replicate_floor 1 1 (g+1) le_rfl) (replicate_ordered 1 (g+1)) he
  have hr : List.replicate (g+2) (1 : ℤ) = List.replicate (g+1) 1 ++ [1] := by
    simpa using List.replicate_add (g+1) 1 (1 : ℤ)
  simpa only [outer, hr] using h

theorem node_insertion (g c : ℕ) (xs ys : List Edge) (hy : ys ≠ [])
    (hn : NodeRun (.H (g+1) :: (xs ++ ys)) c) :
    NodeRun (.H (g+2) :: (xs ++ (.V 0 :: ys))) c := by
  obtain ⟨h, rest, hword, he⟩ := node_to_units hn
  have hg : h = g := by
    have hh := (List.cons.inj hword).1
    cases hh
    rfl
  have hr : rest = xs ++ ys := (List.cons.inj hword).2.symm
  subst h
  subst rest
  exact root_insertion_node g c xs ys hy he

theorem insertion_grade_bound (m g : ℕ) (xs ys : List Edge)
    (hg : g+2 ≤ m) (hb : ∀ e ∈ xs ++ ys, e.grade ≤ m) :
    ∀ e ∈ (.H (g+2) :: (xs ++ (.V 0 :: ys))), e.grade ≤ m := by
  intro e he
  simp only [List.mem_cons, List.mem_append] at he
  rcases he with rfl | hx | rfl | hy
  · exact hg
  · exact hb e (List.mem_append_left _ hx)
  · exact Nat.zero_le m
  · exact hb e (List.mem_append_right _ hy)

theorem connected_insertion (m g c : ℕ) (xs ys : List Edge) (hy : ys ≠ [])
    (hg : g+2 ≤ m) (hc : Connected m (.H (g+1) :: (xs ++ ys)) c) :
    Connected m (.H (g+2) :: (xs ++ (.V 0 :: ys))) c := by
  apply node_connected (node_insertion g c xs ys hy (connected_node hc))
  apply insertion_grade_bound m g xs ys hg
  intro e he
  exact connected_grades hc e (List.mem_cons_of_mem _ he)

def prefixBalance (w : List Edge) (k : ℕ) : ℤ :=
  ((w.take k).map Edge.credit).sum

theorem sum_take_zero (xs ys : List ℤ) (k : ℕ) :
    ((xs ++ (0 :: ys)).take k).sum =
      if k ≤ xs.length then ((xs ++ ys).take k).sum
      else ((xs ++ ys).take (k-1)).sum := by
  by_cases hk : k ≤ xs.length
  · rw [ite_eq_left hk, List.take_append_of_le_length hk, List.take_append_of_le_length hk]
  · rw [ite_eq_right hk]
    have hk' : xs.length ≤ k := by omega
    have hk'' : xs.length ≤ k-1 := by omega
    rw [List.take_append, List.take_of_length_le hk', List.sum_append,
      List.take_append, List.take_of_length_le hk'', List.sum_append]
    obtain ⟨j, hj⟩ : ∃ j, k-xs.length = j+1 := ⟨k-xs.length-1, by omega⟩
    have he : k-1-xs.length = j := by omega
    simp [hj, he]

theorem insertion_prefix_balances (g : ℕ) (xs ys : List Edge) (k : ℕ) :
    prefixBalance (.H (g+2) :: (xs ++ (.V 0 :: ys))) k =
      if k ≤ xs.length+1 then prefixBalance (.H (g+1) :: (xs ++ ys)) k
      else prefixBalance (.H (g+1) :: (xs ++ ys)) (k-1) := by
  have h := sum_take_zero (1 :: xs.map Edge.credit) (ys.map Edge.credit) k
  simpa [prefixBalance, List.map_take, List.map_append, Edge.credit] using h

theorem insertion_surplus (g : ℕ) (xs ys : List Edge) :
    prefixBalance (.H (g+2) :: (xs ++ (.V 0 :: ys))) (xs.length+ys.length+2)-1 =
    prefixBalance (.H (g+1) :: (xs ++ ys)) (xs.length+ys.length+1)-1 := by
  rw [insertion_prefix_balances, ite_eq_right (by omega)]
  congr 2

end KroneckerInsertionBalanceHelpers
