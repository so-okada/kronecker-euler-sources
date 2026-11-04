import KroneckerUnitShellReserve

/- Original module: KroneckerUnitInsertionNode -/
section
/-! The actual uncolored insertion map: one extra zero vertical edge, with an extra outer debt unit. -/
set_option autoImplicit false
namespace KroneckerUnitInsertionNode
open KroneckerStack KroneckerDebtUnits KroneckerUnitNodeDictionary KroneckerUnitConcatenation
open KroneckerUnitShift KroneckerUnitOuterStack KroneckerUnitInteriorInsertion
open KroneckerUnitInvariantExecution KroneckerUnitShellReserve

def insertionShell (u v : ℕ) (xs ys : List Edge) : List Edge :=
  .H (u+2)::(List.replicate u (.V 0)++(xs++(.V 0::ys))++
    ((.H v::List.replicate v (.V 0))++[.V 2]))

theorem insertion_shell_node (u v c : ℕ) (xs ys : List Edge) (hne : xs≠[])
    (hn : NodeRun (xs++ys) c) : NodeRun (insertionShell u v xs ys) c := by
  obtain ⟨g,rest,hword,hex⟩ := node_to_units hn
  cases xs with
  | nil => contradiction
  | cons e xs =>
    have he : e=.H (g+1) := (List.cons.inj hword).1
    have hr : xs++ys=rest := (List.cons.inj hword).2
    subst e
    subst rest
    have hshift := unit_execute_shift hex 1
    have hbody : unitExecute (xs++ys) ⟨2,List.replicate (g+1) 2⟩=some ⟨(c : ℤ)+2,[]⟩ := by
      simpa [shift,add_assoc] using hshift
    have hinsert := insert_zero_inside 1 ((c : ℤ)+2) xs ys ⟨2,List.replicate (g+1) 2⟩
      (replicate_floor 1 2 (g+1) (by norm_num)) (replicate_ordered 2 (g+1)) hbody
    apply units_to_node
    refine ⟨u+1,_,rfl,?_⟩
    change unitExecute (List.replicate u (.V 0)++
      ((.H (g+1)::xs)++(.V 0::ys))++((.H v::List.replicate v (.V 0))++[.V 2]))
      ⟨1,List.replicate (u+2) 1⟩=some ⟨(c : ℤ)+1,[]⟩
    rw [List.append_assoc,unit_execute_append,unit_shell_prefix]
    simp only [Option.bind_some]
    rw [unit_execute_append]
    have hmid : unitExecute ((.H (g+1)::xs)++(.V 0::ys)) ⟨1,[1,1]⟩=
        some ⟨(c : ℤ)+2,[1]⟩ := by
      simpa [unitExecute,unitStep,outer] using hinsert
    rw [hmid]
    exact unit_shell_suffix v c

end KroneckerUnitInsertionNode
end

/- Original module: KroneckerVerticalInsertionConnected -/
section
/-! Connectedness and surplus preservation for vertical insertion in the actual interpreter. -/
set_option autoImplicit false
namespace KroneckerVerticalInsertionConnected
open KroneckerStack KroneckerUnitInsertionNode

theorem insertion_shell_grades (m u v : ℕ) (xs ys : List Edge)
    (hu : u+2 ≤ m) (hv : v ≤ m) (hm : 2 ≤ m)
    (hx : ∀ e ∈ xs++ys,e.grade ≤ m) :
    ∀ e ∈ insertionShell u v xs ys,e.grade ≤ m := by
  intro e he
  simp only [insertionShell,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at he
  rcases he with rfl | ((h | h | rfl | h) | (rfl | h) | rfl)
  · exact hu
  · have heq := (List.mem_replicate.mp h).2; subst e; exact Nat.zero_le m
  · exact hx e (List.mem_append_left _ h)
  · exact Nat.zero_le m
  · exact hx e (List.mem_append_right _ h)
  · exact hv
  · have heq := (List.mem_replicate.mp h).2; subst e; exact Nat.zero_le m
  · exact hm

theorem insertion_shell_connected (m u v c : ℕ) (xs ys : List Edge) (hne : xs≠[])
    (hu : u+2 ≤ m) (hv : v ≤ m) (hm : 2 ≤ m)
    (hc : Connected m (xs++ys) c) :
    Connected m (insertionShell u v xs ys) c :=
  node_connected (insertion_shell_node u v c xs ys hne (connected_node hc))
    (insertion_shell_grades m u v xs ys hu hv hm (connected_grades hc))

end KroneckerVerticalInsertionConnected
end

/- Original module: KroneckerListInsertion -/
section
/-! A fixed insertion position is independent of the grading and has an exact deletion inverse. -/
set_option autoImplicit false
namespace KroneckerListInsertion

def insertAt {α : Type*} (i : ℕ) (a : α) (xs : List α) : List α :=
  xs.take i++a::xs.drop i

theorem insertAt_length {α : Type*} (i : ℕ) (a : α) (xs : List α) :
    (insertAt i a xs).length=xs.length+1 := by
  simp [insertAt]
  omega

theorem erase_insertAt {α : Type*} (i : ℕ) (a : α) (xs : List α) (hi : i ≤ xs.length) :
    (insertAt i a xs).take i++(insertAt i a xs).drop (i+1)=xs := by
  have hlen : (xs.take i).length=i := List.length_take_of_le hi
  have hd : (xs.take i).drop (i+1)=[] := List.drop_eq_nil_of_le (by omega)
  simp [insertAt,List.drop_append,hlen,hd]

theorem insertAt_injective {α : Type*} (i : ℕ) (a : α) (N : ℕ) (hi : i ≤ N) :
    Function.Injective (fun xs : {xs : List α // xs.length=N} => insertAt i a xs.val) := by
  intro xs ys h
  change insertAt i a xs.val=insertAt i a ys.val at h
  have hx := erase_insertAt i a xs.val (by simpa [xs.property] using hi)
  have hy := erase_insertAt i a ys.val (by simpa [ys.property] using hi)
  apply Subtype.ext
  rw [← hx,← hy,h]

end KroneckerListInsertion
end
