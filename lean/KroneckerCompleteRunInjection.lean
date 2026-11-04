import KroneckerPrescribedLayerSplit

/- Original module: KroneckerPrescribedMiddleCount -/
section
/-! Every sufficiently long prescribed collar supports the actual middle-edit comparison. -/
set_option autoImplicit false
namespace KroneckerPrescribedMiddleCount
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerCollarColoring
open KroneckerMiddlePrograms KroneckerMiddleContext KroneckerMiddleProgramCount KroneckerPrescribedLayerSplit



end KroneckerPrescribedMiddleCount
end

/- Original module: KroneckerPrescribedRunPrograms -/
section
/-! Literal arbitrary left and right run collars, in the prescribed order. -/
set_option autoImplicit false
namespace KroneckerPrescribedRunPrograms
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerPrescribedCollars
open KroneckerMiddlePrograms KroneckerMiddleContext KroneckerPrescribedMiddleCount KroneckerOrientationPositions

theorem pairCollars_edit_legal {m : ℕ} (left right : List ℕ)
    (hl : ∀ r ∈ left,1 ≤ r ∧ r ≤ m-2) (hr : ∀ r ∈ right,1 ≤ r ∧ r ≤ m-2) :
    EditPairs m (pairCollars left right) := by
  intro pair h
  have hp := List.of_mem_zip h
  exact ⟨hl pair.1 hp.1,hr pair.2 (by simpa using hp.2)⟩


end KroneckerPrescribedRunPrograms
end

/- Original module: KroneckerVerticalComposition -/
section
/-! The K=0 prescribed-target composition theorem for arbitrary mixed vertical edits.
Complete-run insertion K>0 and separately labeled wrapped-parse owner identity are not asserted. -/
set_option autoImplicit false
namespace KroneckerVerticalComposition
open KroneckerWordCounts KroneckerFiberBudget KroneckerMiddlePrograms KroneckerPrescribedRunPrograms


end KroneckerVerticalComposition
end

/- Original module: KroneckerUnitCompleteChild -/
section
/-! A complete fixed-grade child preserves the open unit stack and raises balance by one. -/
set_option autoImplicit false
namespace KroneckerUnitCompleteChild
open KroneckerStack KroneckerDebtUnits KroneckerUnitBalanceRaise KroneckerUnitNonemptyExecution

def child (r : ℕ) : List Edge := .H r::List.replicate r (.V 0)

theorem zero_units_close (r : ℕ) (b a : ℤ) (tail : List ℤ) (ha : a ≤ b) :
    unitExecute (List.replicate r (.V 0)) ⟨b,List.replicate r a++tail⟩=some ⟨b,tail⟩ := by
  induction r with
  | zero => rfl
  | succ r ih => simpa [List.replicate_succ,unitExecute,unitStep,ha] using ih

theorem execute_child (r : ℕ) (s : UnitState) (hs : s.stack≠[]) :
    unitExecute (child r) s=some (raiseBalance 1 s) := by
  rcases s with ⟨b,st⟩
  cases st with
  | nil => contradiction
  | cons x xs =>
    simpa only [child,unitExecute,unitStep,Option.bind_some,raiseBalance] using
      zero_units_close r (b+1) (b+1) (x::xs) le_rfl

theorem nonempty_word_source {es : List Edge} {s t : UnitState}
    (h : unitExecute es s=some t) (hne : es≠[]) : s.stack≠[] := by
  rcases s with ⟨b,st⟩
  intro hs
  change st=[] at hs
  subst st
  exact hne (execute_from_empty es b t h).1

end KroneckerUnitCompleteChild
end

/- Original module: KroneckerRaisedClosure -/
section
/-! Raising balance preserves closure and raises the exact final balance. -/
set_option autoImplicit false
namespace KroneckerRaisedClosure
open KroneckerStack KroneckerDebtUnits KroneckerUnitShift KroneckerUnitStepWeakening
open KroneckerUnitBalanceRaise KroneckerUnitRaisedExecution

theorem weaker_empty (s : UnitState) (b : ℤ) (h : Weaker s ⟨b,[]⟩) : s=⟨b,[]⟩ := by
  rcases s with ⟨c,st⟩
  obtain ⟨hc,hs⟩ := h
  cases hs
  cases hc
  rfl

theorem execute_raised_closed {es : List Edge} {s : UnitState} {b : ℤ}
    (h : unitExecute es s=some ⟨b,[]⟩) (d : ℤ) (hd : 0 ≤ d) :
    unitExecute es (raiseBalance d s)=some ⟨b+d,[]⟩ := by
  obtain ⟨v,hv,hw⟩ := execute_raised h d hd
  have he : v=⟨b+d,[]⟩ := weaker_empty v (b+d) (by simpa [shift] using hw)
  simpa only [he] using hv

end KroneckerRaisedClosure
end

/- Original module: KroneckerChildExecutionInsertion -/
section
/-! Insert a complete child at a fixed gap before a nonempty suffix. -/
set_option autoImplicit false
namespace KroneckerChildExecutionInsertion
open KroneckerStack KroneckerDebtUnits KroneckerUnitConcatenation
open KroneckerUnitCompleteChild KroneckerRaisedClosure

theorem execute_insert_child (xs ys : List Edge) (r : ℕ) (s : UnitState) (b : ℤ)
    (h : unitExecute (xs++ys) s=some ⟨b,[]⟩) (hy : ys≠[]) :
    unitExecute (xs++child r++ys) s=some ⟨b+1,[]⟩ := by
  obtain ⟨p,hp,hq⟩ := unit_execute_split h
  have hn := nonempty_word_source hq hy
  have hr := execute_raised_closed hq 1 (by norm_num)
  rw [List.append_assoc,unit_execute_append,hp]
  simp only [Option.bind_some]
  rw [unit_execute_append,execute_child r p hn]
  exact hr

end KroneckerChildExecutionInsertion
end

/- Original module: KroneckerCompleteChildNode -/
section
/-! Insert a complete child inside a connected node, raising surplus by one. -/
set_option autoImplicit false
namespace KroneckerCompleteChildNode
open KroneckerStack KroneckerDebtUnits KroneckerUnitNodeDictionary KroneckerUnitCompleteChild
open KroneckerChildExecutionInsertion

theorem insert_child_node (xs ys : List Edge) (r c : ℕ) (hx : xs≠[]) (hy : ys≠[])
    (h : NodeRun (xs++ys) c) : NodeRun (xs++child r++ys) (c+1) := by
  obtain ⟨g,rest,hword,hex⟩ := node_to_units h
  cases xs with
  | nil => contradiction
  | cons e xs =>
    have he : e=.H (g+1) := (List.cons.inj hword).1
    have hr : xs++ys=rest := (List.cons.inj hword).2
    subst e
    subst rest
    have hi := execute_insert_child xs ys r ⟨1,List.replicate (g+1) 1⟩ ((c : ℤ)+1) hex hy
    apply units_to_node
    refine ⟨g,_,rfl,?_⟩
    rw [Nat.cast_add, Nat.cast_one]
    exact hi

end KroneckerCompleteChildNode
end

/- Original module: KroneckerCompleteChildConnected -/
section
/-! Legal grades and connectedness of the complete-run insertion. -/
set_option autoImplicit false
namespace KroneckerCompleteChildConnected
open KroneckerStack KroneckerUnitCompleteChild KroneckerCompleteChildNode

theorem child_grades (m r : ℕ) (hr : r ≤ m) : ∀ e ∈ child r,e.grade ≤ m := by
  intro e he
  simp only [child,List.mem_cons,List.mem_replicate] at he
  rcases he with rfl | ⟨_,rfl⟩
  · exact hr
  · exact Nat.zero_le m

theorem insert_child_connected (m r c : ℕ) (xs ys : List Edge)
    (hx : xs≠[]) (hy : ys≠[]) (hr : r ≤ m) (h : Connected m (xs++ys) c) :
    Connected m (xs++child r++ys) (c+1) := by
  apply node_connected (insert_child_node xs ys r c hx hy (connected_node h))
  intro e he
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · exact connected_grades h e (List.mem_append_left _ he)
    · exact child_grades m r hr e he
  · exact connected_grades h e (List.mem_append_right _ he)

end KroneckerCompleteChildConnected
end

/- Original module: KroneckerListSplice -/
section
/-! A fixed block insertion and the retained prefix/suffix lengths. -/
set_option autoImplicit false
namespace KroneckerListSplice

def splice {α : Type*} (i : ℕ) (block xs : List α) : List α := xs.take i++block++xs.drop i

theorem splice_length {α : Type*} (i : ℕ) (block xs : List α) :
    (splice i block xs).length=xs.length+block.length := by
  simp [splice]
  omega

theorem take_splice {α : Type*} (i : ℕ) (block xs : List α) (hi : i ≤ xs.length) :
    (splice i block xs).take i=xs.take i := by
  simp [splice,List.append_assoc,List.length_take_of_le hi]

theorem drop_splice {α : Type*} (i : ℕ) (block xs : List α) (hi : i ≤ xs.length) :
    (splice i block xs).drop (i+block.length)=xs.drop i := by
  have hlen : (xs.take i++block).length=i+block.length := by simp [List.length_take_of_le hi]
  rw [splice,← hlen,List.drop_left]

end KroneckerListSplice
end

/- Original module: KroneckerSplicePainting -/
section
/-! Paint a block insertion by splicing the shape and palette lists together. -/
set_option autoImplicit false
namespace KroneckerSplicePainting
open KroneckerListSplice

theorem zip_splice {α β γ : Type*} (f : α → β → γ) (i : ℕ)
    (a : List α) (b : List β) (xs : List α) (ys : List β)
    (hab : a.length=b.length) (hxy : xs.length=ys.length) :
    List.zipWith f (splice i a xs) (splice i b ys)=
      splice i (List.zipWith f a b) (List.zipWith f xs ys) := by
  unfold splice
  rw [List.zipWith_append (by simp [hab,hxy]),List.zipWith_append (by simp [hxy])]
  simp only [← List.take_zipWith,← List.drop_zipWith]

end KroneckerSplicePainting
end

/- Original module: KroneckerCompleteRunPalette -/
section
/-! The complete-run palette map copies every old palette and fixes all new colors. -/
set_option autoImplicit false
namespace KroneckerCompleteRunPalette
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerListSplice KroneckerUnitCompleteChild

def childColors (m r : ℕ) (hr : r ≤ m) : List (Palette m) :=
  fixedColor m r hr::List.replicate r (zeroColor m)

def completePath (r i : ℕ) (U : List Bool) : List Bool := splice i (runShape r) U

def completeColors {m : ℕ} (r i : ℕ) (hr : r ≤ m) (cs : List (Palette m)) : List (Palette m) :=
  splice i (childColors m r hr) cs

theorem childColors_length (m r : ℕ) (hr : r ≤ m) : (childColors m r hr).length=(runShape r).length := by
  simp [childColors,runShape]

theorem childColors_word (m r : ℕ) (hr : r ≤ m) :
    List.zipWith paint (runShape r) (childColors m r hr)=child r := by
  simp [runShape,childColors,child,paint]

theorem completeColors_length {m : ℕ} (r i : ℕ) (hr : r ≤ m) (U : List Bool)
    (cs : List (Palette m)) (hcs : cs.length=U.length) :
    (completeColors r i hr cs).length=(completePath r i U).length := by
  simp [completeColors,completePath,splice_length,childColors_length,hcs]

def completeColoring {m : ℕ} (r i : ℕ) (hr : r ≤ m) (U : List Bool) (g : Coloring m U.length) :
    Coloring m (completePath r i U).length :=
  fromList (completeColors r i hr (List.ofFn g)) (completeColors_length r i hr U _ (by simp))

end KroneckerCompleteRunPalette
end

/- Original module: KroneckerCompleteRunWord -/
section
/-! The actual colored map has exactly the inserted-child interpreter word. -/
set_option autoImplicit false
namespace KroneckerCompleteRunWord
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerListSplice KroneckerSplicePainting KroneckerUnitCompleteChild KroneckerCompleteRunPalette

theorem completeColoring_word {m : ℕ} (r i : ℕ) (hr : r ≤ m) (U : List Bool) (g : Coloring m U.length) :
    pathWord (completePath r i U) (completeColoring r i hr U g)=
      (pathWord U g).take i++child r++(pathWord U g).drop i := by
  rw [completeColoring,fromList_word]
  unfold completePath completeColors
  rw [zip_splice paint i _ _ _ _ (childColors_length m r hr).symm (by simp),
    childColors_word,← word_zip]
  rfl

end KroneckerCompleteRunWord
end

/- Original module: KroneckerCompleteRunMap -/
section
/-! The actual complete-run map raises surplus by one at every internal gap. -/
set_option autoImplicit false
namespace KroneckerCompleteRunMap
open KroneckerStack KroneckerColoring KroneckerWordCounts
open KroneckerCompleteRunPalette KroneckerCompleteRunWord KroneckerCompleteChildConnected

theorem completeColoring_connected {m : ℕ} (r i c : ℕ) (hr : r ≤ m) (U : List Bool)
    (hi : 1 ≤ i ∧ i < U.length) (g : Coloring m U.length) (hg : Connected m (pathWord U g) c) :
    Connected m (pathWord (completePath r i U) (completeColoring r i hr U g)) (c+1) := by
  rw [completeColoring_word]
  have hx : (pathWord U g).take i≠[] := by
    apply List.ne_nil_of_length_pos
    simp only [List.length_take,pathWord_length]
    omega
  have hy : (pathWord U g).drop i≠[] := by
    apply List.ne_nil_of_length_pos
    simp only [List.length_drop,pathWord_length]
    omega
  exact insert_child_connected m r c _ _ hx hy hr (by simpa using hg)

def completeRun {m : ℕ} (r i c : ℕ) (hr : r ≤ m) (U : List Bool) (hi : 1 ≤ i ∧ i < U.length) :
    ConnectedColorings m U c → ConnectedColorings m (completePath r i U) (c+1) :=
  fun g => ⟨completeColoring r i hr U g.val,completeColoring_connected r i c hr U hi g.val g.property⟩

end KroneckerCompleteRunMap
end

/- Original module: KroneckerCompleteRunRecovery -/
section
/-! Delete the fixed inserted block to recover every original palette exactly. -/
set_option autoImplicit false
namespace KroneckerCompleteRunRecovery
open KroneckerColoring KroneckerColoredShell KroneckerListSplice KroneckerCompleteRunPalette

def recoverBlock {α : Type*} (i k : ℕ) (xs : List α) : List α := xs.take i++xs.drop (i+k)

theorem recover_splice {α : Type*} (i : ℕ) (block xs : List α) (hi : i ≤ xs.length) :
    recoverBlock i block.length (splice i block xs)=xs := by
  rw [recoverBlock,take_splice i block xs hi,drop_splice i block xs hi,List.take_append_drop]

theorem recover_complete_colors {m : ℕ} (r i : ℕ) (hr : r ≤ m) (U : List Bool)
    (hi : i ≤ U.length) (g : Coloring m U.length) :
    recoverBlock i (r+1) (List.ofFn (completeColoring r i hr U g))=List.ofFn g := by
  rw [completeColoring,fromList_colors]
  simpa only [completeColors,childColors,List.length_cons,List.length_replicate] using
    recover_splice i (childColors m r hr) (List.ofFn g) (by simpa using hi)

end KroneckerCompleteRunRecovery
end

/- Original module: KroneckerCompleteRunInjection -/
section
/-! The actual complete-run map is an injection, with exact surplus increase one. -/
set_option autoImplicit false
namespace KroneckerCompleteRunInjection
open KroneckerColoring KroneckerWordCounts KroneckerCompleteRunPalette KroneckerCompleteRunMap
open KroneckerCompleteRunRecovery

theorem completeColoring_injective {m : ℕ} (r i : ℕ) (hr : r ≤ m) (U : List Bool) (hi : i ≤ U.length) :
    Function.Injective (completeColoring r i hr U) := by
  intro x y h
  have he := congrArg (fun g => recoverBlock i (r+1) (List.ofFn g)) h
  apply List.ofFn_injective
  simpa only [recover_complete_colors r i hr U hi] using he

theorem completeRun_injective {m : ℕ} (r i c : ℕ) (hr : r ≤ m) (U : List Bool)
    (hi : 1 ≤ i ∧ i < U.length) : Function.Injective (completeRun r i c hr U hi) := by
  intro x y h
  apply Subtype.ext
  exact completeColoring_injective r i hr U (by omega) (congrArg Subtype.val h)

theorem completeRun_count {m : ℕ} (r i c : ℕ) (hr : r ≤ m) (U : List Bool)
    (hi : 1 ≤ i ∧ i < U.length) : pathCount m U c ≤ pathCount m (completePath r i U) (c+1) := by
  classical
  simp only [pathCount,Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective _ (completeRun_injective r i c hr U hi)

end KroneckerCompleteRunInjection
end
