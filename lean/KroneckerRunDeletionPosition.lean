import KroneckerUnitPreservingLoopShell
import KroneckerColoredShell
import KroneckerOrientationPositions
import KroneckerFiberBudget

section

/- Original module: KroneckerVerticalDeletionNode -/
section
/-! Interpreter-level vertical deletion and its exact surplus increment. -/
set_option autoImplicit false
namespace KroneckerVerticalDeletionNode
open KroneckerStack KroneckerDebtUnits KroneckerLowerOneHorizontal KroneckerUnitLoopDeletion
open KroneckerUnitParentExecution KroneckerUnitPreservingLoopShell

theorem deletion_shell_node (u v c h : ℕ) (xs ys : List Edge)
    (hn : NodeRun (xs++(.V h::ys)) c) :
    ∃ xs',LowerOne xs xs' ∧ NodeRun (loopShell u v (xs'++ys)) (c+h) := by
  have he : unitExecute (xs++(.V h::ys)) ⟨1,[1]⟩=some ⟨(c : ℤ)+2,[1]⟩ := by
    simpa [add_comm,add_left_comm] using node_in_parent hn 1 1
  obtain ⟨xs',hl,hx⟩ := loop_delete 1 1 ((c : ℤ)+2) h xs ys he
  refine ⟨xs',hl,loop_shell_node u v (c+h) (xs'++ys) ?_⟩
  simpa [Nat.cast_add,add_assoc,add_comm,add_left_comm] using hx

end KroneckerVerticalDeletionNode
end

/- Original module: KroneckerVerticalDeletionConnected -/
section
/-! Legal grades and actual Connected preservation for one specified vertical deletion. -/
set_option autoImplicit false
namespace KroneckerVerticalDeletionConnected
open KroneckerStack KroneckerLowerOneHorizontal KroneckerUnitPreservingLoopShell KroneckerVerticalDeletionNode

theorem loop_shell_grades (m u v : ℕ) (es : List Edge) (hu : u+1 ≤ m) (hv : v ≤ m) (hm : 2 ≤ m)
    (he : ∀ e ∈ es,e.grade ≤ m) : ∀ e ∈ loopShell u v es,e.grade ≤ m := by
  intro e h
  simp only [loopShell,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
  rcases h with rfl | ((hp | hi) | (rfl | hp) | rfl)
  · exact hu
  · have hh := (List.mem_replicate.mp hp).2; subst e; exact Nat.zero_le m
  · exact he e hi
  · exact hv
  · have hh := (List.mem_replicate.mp hp).2; subst e; exact Nat.zero_le m
  · exact hm

theorem deletion_shell_connected (m u v c h : ℕ) (xs ys : List Edge)
    (hu : u+1 ≤ m) (hv : v ≤ m) (hm : 2 ≤ m)
    (hc : Connected m (xs++(.V h::ys)) c) :
    ∃ xs',LowerOne xs xs' ∧ Connected m (loopShell u v (xs'++ys)) (c+h) := by
  obtain ⟨xs',hl,hn⟩ := deletion_shell_node u v c h xs ys (connected_node hc)
  refine ⟨xs',hl,node_connected hn (loop_shell_grades m u v _ hu hv hm ?_)⟩
  have hxs : ∀ e ∈ xs,e.grade ≤ m := by
    intro e he; exact connected_grades hc e (by simp [he])
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact lower_grades hl m hxs e he
  · exact connected_grades hc e (by simp [he])

end KroneckerVerticalDeletionConnected
end

/- Original module: KroneckerListDeletion -/
section
/-! The fixed position of a deleted edge is independent of its grading. -/
set_option autoImplicit false
namespace KroneckerListDeletion

def removeAt {α : Type*} (i : ℕ) (xs : List α) : List α := xs.take i++xs.drop (i+1)

theorem split_at {α : Type*} (xs : List α) (i : ℕ) (hi : i < xs.length) :
    xs=xs.take i++xs[i]::xs.drop (i+1) := by
  rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]

theorem removeAt_length {α : Type*} (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (removeAt i xs).length=xs.length-1 := by
  simp [removeAt]
  omega


end KroneckerListDeletion
end

/- Original module: KroneckerLowerOneIndex -/
section
/-! Extract the actual changed position from a one-horizontal lowering witness. -/
set_option autoImplicit false
namespace KroneckerLowerOneIndex
open KroneckerStack KroneckerLowerOneHorizontal

theorem lower_index {xs ys : List Edge} (h : LowerOne xs ys) :
    ∃ (j : Fin xs.length) (k : ℕ),xs[j.val]=.H (k+1) ∧ ys=xs.set j.val (.H k) := by
  obtain ⟨pre,post,g,rfl,rfl⟩ := h
  refine ⟨⟨pre.length,by simp⟩,g,?_,?_⟩
  · simp
  · simp

end KroneckerLowerOneIndex
end

/- Original module: KroneckerZipSet -/
section
/-! Updating one palette entry updates exactly its painted edge. -/
set_option autoImplicit false
namespace KroneckerZipSet

theorem zip_set_at {α β γ : Type*} (f : α → β → γ) (xs : List α) (ys : List β)
    (hlen : xs.length=ys.length) (i : ℕ) (hi : i < xs.length) (b : β) :
    List.zipWith f xs (ys.set i b)=(List.zipWith f xs ys).set i (f xs[i] b) := by
  induction xs generalizing ys i with
  | nil => simp at hi
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i =>
        simpa using congrArg (f x y::·) (ih ys (by simpa using hlen) i (by simpa using hi))

end KroneckerZipSet
end
end

section

/- Original module: KroneckerPathWordIndex -/
section
/-! Read and split the literal colored word at the chosen deletion position. -/
set_option autoImplicit false
namespace KroneckerPathWordIndex
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerListDeletion

theorem pathWord_getElem {m : ℕ} (U : List Bool) (g : Coloring m U.length)
    (i : ℕ) (hi : i < U.length) :
    (pathWord U g)[i]'(by simpa [pathWord_length] using hi)=paint U[i] (g ⟨i,hi⟩) := by
  simp [pathWord,word,pathShape,List.getD]

theorem pathWord_split_vertical {m : ℕ} (U : List Bool) (g : Coloring m U.length)
    (i : ℕ) (hi : i < U.length) (hv : U[i]=false) :
    pathWord U g=(pathWord U g).take i++
      .V (grade (g ⟨i,hi⟩))::(pathWord U g).drop (i+1) := by
  have h := split_at (pathWord U g) i (by simpa [pathWord_length] using hi)
  rw [pathWord_getElem U g i hi,hv] at h
  exact h

end KroneckerPathWordIndex
end

/- Original module: KroneckerLowerPalette -/
section
/-! The changed horizontal edge uses color zero at its grade lowered by one. -/
set_option autoImplicit false
namespace KroneckerLowerPalette
open KroneckerStack KroneckerColoring KroneckerColoredShell

def lowerPalette {m : ℕ} (x : Palette m) : Palette m :=
  fixedColor m (grade x-1) ((Nat.sub_le _ _).trans (grade_le x))


theorem paint_lower_of_H {m : ℕ} (b : Bool) (x : Palette m) (k : ℕ)
    (h : paint b x=.H (k+1)) : paint b (lowerPalette x)=.H k := by
  cases b with
  | false => simp [paint] at h
  | true =>
    have hg : grade x=k+1 := by simpa [paint] using h
    simp [paint,lowerPalette,hg]

theorem horizontal_of_paint_H {m : ℕ} (b : Bool) (x : Palette m) (k : ℕ)
    (h : paint b x=.H (k+1)) : b=true ∧ 0 < grade x := by
  cases b with
  | false => simp [paint] at h
  | true =>
    have hg : grade x=k+1 := by simpa [paint] using h
    exact ⟨rfl,by omega⟩

end KroneckerLowerPalette
end

/- Original module: KroneckerDeletionInteriorColors -/
section
/-! A literal palette map lowers one earlier horizontal entry and deletes the specified vertical entry. -/
set_option autoImplicit false
namespace KroneckerDeletionInteriorColors
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerListDeletion KroneckerLowerPalette KroneckerZipSet

def editedColors {m : ℕ} (U : List Bool) (i : ℕ) (hi : i < U.length) (j : Fin i)
    (g : Coloring m U.length) : List (Palette m) :=
  ((List.ofFn g).take i).set j.val (lowerPalette (g ⟨j.val,lt_trans j.isLt hi⟩))++
    (List.ofFn g).drop (i+1)

theorem editedColors_length {m : ℕ} (U : List Bool) (i : ℕ) (hi : i < U.length)
    (j : Fin i) (g : Coloring m U.length) :
    (editedColors U i hi j g).length=(removeAt i U).length := by
  simp [editedColors,removeAt]

def editedColoring {m : ℕ} (U : List Bool) (i : ℕ) (hi : i < U.length) (j : Fin i)
    (g : Coloring m U.length) : Coloring m (removeAt i U).length :=
  fromList (editedColors U i hi j g) (editedColors_length U i hi j g)

theorem editedColoring_word {m : ℕ} (U : List Bool) (i : ℕ) (hi : i < U.length)
    (j : Fin i) (g : Coloring m U.length) :
    pathWord (removeAt i U) (editedColoring U i hi j g)=
      ((pathWord U g).take i).set j.val
        (paint U[j.val] (lowerPalette (g ⟨j.val,lt_trans j.isLt hi⟩)))++
      (pathWord U g).drop (i+1) := by
  rw [editedColoring,fromList_word]
  unfold editedColors removeAt
  rw [List.zipWith_append (by simp)]
  rw [zip_set_at paint (U.take i) ((List.ofFn g).take i) (by simp) j.val (by simp; omega)]
  rw [← List.take_zipWith,← List.drop_zipWith,← word_zip]
  simp only [List.getElem_take]

end KroneckerDeletionInteriorColors
end

/- Original module: KroneckerDeletionColoring -/
section
/-! Wrap the literal palette edit in fixed-color preserving shell runs. -/
set_option autoImplicit false
namespace KroneckerDeletionColoring
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerListDeletion KroneckerDeletionInteriorColors KroneckerUnitPreservingLoopShell

def deletionPath (u v : ℕ) (U : List Bool) (i : ℕ) : List Bool :=
  shellPath u v (removeAt i U)

def deletionColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (j : Fin i) (g : Coloring m U.length) : Coloring m (deletionPath u v U i).length :=
  shellColoring u v hu hv hm hpos (removeAt i U) (editedColoring U i hi j g)

theorem deletionColoring_word {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (j : Fin i) (g : Coloring m U.length) :
    pathWord (deletionPath u v U i) (deletionColoring u v hu hv hm hpos U i hi j g)=
      loopShell u (v-1) (pathWord (removeAt i U) (editedColoring U i hi j g)) := by
  change pathWord (shellPath u v _) (shellColoring u v hu hv hm hpos _ _) = _
  rw [shellColoring_word u v 0]
  simp [shell,loopShell,List.append_assoc]

theorem deletionColoring_recover {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (j : Fin i) (g : Coloring m U.length) :
    recover u v (removeAt i U) (deletionColoring u v hu hv hm hpos U i hi j g)=
      editedColoring U i hi j g := recover_shellColoring u v hu hv hm hpos _ _

end KroneckerDeletionColoring
end

/- Original module: KroneckerDeletionColorExists -/
section
/-! An actual finite colored deletion exists. No labeled owner identity is asserted. -/
set_option autoImplicit false
namespace KroneckerDeletionColorExists
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerPathWordIndex KroneckerLowerOneIndex KroneckerLowerPalette
open KroneckerDeletionInteriorColors KroneckerDeletionColoring KroneckerVerticalDeletionConnected

theorem deletion_color_exists {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) (g : Coloring m U.length) (hg : Connected m (pathWord U g) c) :
    ∃ j : Fin i,U[j.val]=true ∧ 0 < grade (g ⟨j.val,lt_trans j.isLt hi⟩) ∧
      Connected m (pathWord (deletionPath u v U i)
        (deletionColoring u v hu hv hm hpos U i hi j g)) (c+grade (g ⟨i,hi⟩)) := by
  have hs := pathWord_split_vertical U g i hi hvertical
  obtain ⟨xs',hl,hc⟩ := deletion_shell_connected m u (v-1) c (grade (g ⟨i,hi⟩))
    ((pathWord U g).take i) ((pathWord U g).drop (i+1)) hu hv hm (by rw [← hs]; exact hg)
  obtain ⟨j,k,hj,he⟩ := lower_index hl
  have hlen : ((pathWord U g).take i).length=i := by simp [pathWord_length]; omega
  have hji : j.val < i := by simpa [hlen] using j.isLt
  have hp : paint U[j.val] (g ⟨j.val,lt_trans hji hi⟩)=.H (k+1) := by
    have hj' : (pathWord U g)[j.val]'(by simp [pathWord_length]; omega)=.H (k+1) := by
      simpa only [List.getElem_take] using hj
    rw [pathWord_getElem U g j.val (lt_trans hji hi)] at hj'
    exact hj'
  refine ⟨⟨j.val,hji⟩,(horizontal_of_paint_H _ _ _ hp).1,
    (horizontal_of_paint_H _ _ _ hp).2,?_⟩
  rw [deletionColoring_word,editedColoring_word,paint_lower_of_H _ _ _ hp,← he]
  exact hc

end KroneckerDeletionColorExists
end

/- Original module: KroneckerDeletionChoice -/
section
/-! Choose a certified earlier horizontal position for each connected input. -/
set_option autoImplicit false
namespace KroneckerDeletionChoice
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerDeletionColoring
open KroneckerDeletionColorExists

noncomputable def chosenIndex {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) (g : ConnectedColorings m U c) : Fin i :=
  Classical.choose (deletion_color_exists u v c hu hv hm hpos U i hi hvertical g.val g.property)

theorem chosenIndex_spec {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) (g : ConnectedColorings m U c) :
    let j := chosenIndex u v c hu hv hm hpos U i hi hvertical g
    U[j.val]=true ∧ 0 < grade (g.val ⟨j.val,lt_trans j.isLt hi⟩) ∧
      Connected m (pathWord (deletionPath u v U i)
        (deletionColoring u v hu hv hm hpos U i hi j g.val)) (c+grade (g.val ⟨i,hi⟩)) :=
  Classical.choose_spec (deletion_color_exists u v c hu hv hm hpos U i hi hvertical g.val g.property)

end KroneckerDeletionChoice
end

/- Original module: KroneckerVerticalDeletionMap -/
section
/-! The concrete connected-coloring map, indexed by the deleted vertical grade. -/
set_option autoImplicit false
namespace KroneckerVerticalDeletionMap
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerDeletionColoring
open KroneckerDeletionChoice

abbrev DeletionTarget (m : ℕ) (V : List Bool) (c : ℕ) :=
  (h : Fin (m+1)) × ConnectedColorings m V (c+h.val)

noncomputable def verticalDeletion {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) (g : ConnectedColorings m U c) :
    DeletionTarget m (deletionPath u v U i) c :=
  ⟨⟨grade (g.val ⟨i,hi⟩),by have := grade_le (g.val ⟨i,hi⟩); omega⟩,
    ⟨deletionColoring u v hu hv hm hpos U i hi
      (chosenIndex u v c hu hv hm hpos U i hi hvertical g) g.val,
      (chosenIndex_spec u v c hu hv hm hpos U i hi hvertical g).2.2⟩⟩



end KroneckerVerticalDeletionMap
end

/- Original module: KroneckerListEditRestore -/
section
/-! Recover a list from one earlier update and one later deletion. -/
set_option autoImplicit false
namespace KroneckerListEditRestore

def restoreEdit {α : Type*} (i j : ℕ) (oldH oldV : α) (zs : List α) : List α :=
  (zs.take i).set j oldH++oldV::zs.drop i

theorem restore_edit {α : Type*} (xs : List α) (i j : ℕ) (hi : i < xs.length)
    (hj : j < i) (newH : α) :
    restoreEdit i j xs[j] xs[i] (((xs.take i).set j newH)++xs.drop (i+1))=xs := by
  have hlen : ((xs.take i).set j newH).length=i := by simp; omega
  have htake : ((((xs.take i).set j newH)++xs.drop (i+1)).take i)=
      (xs.take i).set j newH := by
    simpa only [hlen] using (List.take_left (l₁ := (xs.take i).set j newH) (l₂ := xs.drop (i+1)))
  have hdrop : ((((xs.take i).set j newH)++xs.drop (i+1)).drop i)=
      xs.drop (i+1) := by
    simpa only [hlen] using (List.drop_left (l₁ := (xs.take i).set j newH) (l₂ := xs.drop (i+1)))
  unfold restoreEdit
  rw [htake,hdrop,List.set_set]
  have hset : (xs.take i).set j xs[j]=xs.take i := by
    have hji : j < (xs.take i).length := by simp; omega
    simpa using List.set_getElem_self hji
  rw [hset]
  exact (KroneckerListDeletion.split_at xs i hi).symm

end KroneckerListEditRestore
end

/- Original module: KroneckerDeletionPaletteRecovery -/
section
/-! Exact recovery of every old palette entry, including both discarded colors. -/
set_option autoImplicit false
namespace KroneckerDeletionPaletteRecovery
open KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerListDeletion KroneckerDeletionInteriorColors KroneckerDeletionColoring
open KroneckerListEditRestore

theorem restore_editedColors {m : ℕ} (U : List Bool) (i : ℕ) (hi : i < U.length)
    (j : Fin i) (g : Coloring m U.length) :
    restoreEdit i j.val (g ⟨j.val,lt_trans j.isLt hi⟩) (g ⟨i,hi⟩)
      (editedColors U i hi j g)=List.ofFn g := by
  have h := restore_edit (List.ofFn g) i j.val (by simpa using hi)
    j.isLt (KroneckerLowerPalette.lowerPalette (g ⟨j.val,lt_trans j.isLt hi⟩))
  simpa only [List.getElem_ofFn,editedColors] using h

theorem restore_deletionColoring {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (j : Fin i) (g : Coloring m U.length) :
    restoreEdit i j.val (g ⟨j.val,lt_trans j.isLt hi⟩) (g ⟨i,hi⟩)
      (List.ofFn (recover u v (removeAt i U)
        (deletionColoring u v hu hv hm hpos U i hi j g)))=List.ofFn g := by
  rw [deletionColoring_recover,editedColoring,fromList_colors]
  exact restore_editedColors U i hi j g

end KroneckerDeletionPaletteRecovery
end

/- Original module: KroneckerDeletionCode -/
section
/-! Store only the changed horizontal position and the two old palette entries. -/
set_option autoImplicit false
namespace KroneckerDeletionCode
open KroneckerColoring KroneckerWordCounts KroneckerOrientationPositions
open KroneckerDeletionChoice

abbrev DeletionCode (m : ℕ) (U : List Bool) := Positions U true × Palette m × Palette m

noncomputable def deletionCode {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) (g : ConnectedColorings m U c) : DeletionCode m U :=
  let j := chosenIndex u v c hu hv hm hpos U i hi hvertical g
  ⟨⟨⟨j.val,lt_trans j.isLt hi⟩,(chosenIndex_spec u v c hu hv hm hpos U i hi hvertical g).1⟩,
    g.val ⟨j.val,lt_trans j.isLt hi⟩,g.val ⟨i,hi⟩⟩



end KroneckerDeletionCode
end

/- Original module: KroneckerDeletionDecoder -/
section
/-! A total list decoder exactly recovers inputs on the image of the actual deletion map. -/
set_option autoImplicit false
namespace KroneckerDeletionDecoder
open KroneckerColoring KroneckerWordCounts KroneckerColoredShell KroneckerListDeletion
open KroneckerDeletionChoice KroneckerDeletionColoring KroneckerVerticalDeletionMap
open KroneckerDeletionCode KroneckerListEditRestore KroneckerDeletionPaletteRecovery

def decodeDeletion {m : ℕ} (u v : ℕ) (U : List Bool) (i : ℕ)
    (out : Coloring m (deletionPath u v U i).length) (code : DeletionCode m U) : List (Palette m) :=
  restoreEdit i code.1.val.val code.2.1 code.2.2 (List.ofFn (recover u v (removeAt i U) out))

theorem decode_code {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) (g : ConnectedColorings m U c) :
    decodeDeletion u v U i
      (deletionColoring u v hu hv hm hpos U i hi (chosenIndex u v c hu hv hm hpos U i hi hvertical g) g.val)
      (deletionCode u v c hu hv hm hpos U i hi hvertical g)=List.ofFn g.val :=
  restore_deletionColoring u v hu hv hm hpos U i hi _ g.val

theorem decode_verticalDeletion {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) (g : ConnectedColorings m U c) :
    decodeDeletion u v U i (verticalDeletion u v c hu hv hm hpos U i hi hvertical g).2.val
      (deletionCode u v c hu hv hm hpos U i hi hvertical g)=List.ofFn g.val :=
  decode_code u v c hu hv hm hpos U i hi hvertical g

end KroneckerDeletionDecoder
end

/- Original module: KroneckerDeletionInjectivity -/
section
/-! Equal output palettes and equal recorded data force equal source colorings. -/
set_option autoImplicit false
namespace KroneckerDeletionInjectivity
open KroneckerColoring KroneckerWordCounts KroneckerDeletionColoring KroneckerVerticalDeletionMap
open KroneckerDeletionCode KroneckerDeletionDecoder

theorem deletion_data_injective {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) (x y : ConnectedColorings m U c)
    (ho : (verticalDeletion u v c hu hv hm hpos U i hi hvertical x).2.val=
      (verticalDeletion u v c hu hv hm hpos U i hi hvertical y).2.val)
    (hc : deletionCode u v c hu hv hm hpos U i hi hvertical x=
      deletionCode u v c hu hv hm hpos U i hi hvertical y) : x=y := by
  apply Subtype.ext
  apply List.ofFn_injective
  rw [← decode_verticalDeletion u v c hu hv hm hpos U i hi hvertical x,
    ← decode_verticalDeletion u v c hu hv hm hpos U i hi hvertical y,ho,hc]

theorem deletion_pair_injective {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) :
    Function.Injective (fun g : ConnectedColorings m U c =>
      (verticalDeletion u v c hu hv hm hpos U i hi hvertical g,
        deletionCode u v c hu hv hm hpos U i hi hvertical g)) := by
  intro x y h
  apply deletion_data_injective u v c hu hv hm hpos U i hi hvertical x y
  · exact congrArg (fun z : DeletionTarget m (deletionPath u v U i) c => z.2.val)
      (congrArg Prod.fst h)
  · exact congrArg Prod.snd h

end KroneckerDeletionInjectivity
end

/- Original module: KroneckerDeletionCodeCard -/
section
/-! Count the concrete one-deletion code and compare it with the manuscript budget. -/
set_option autoImplicit false
namespace KroneckerDeletionCodeCard
open KroneckerDeletionCode KroneckerOrientationPositions KroneckerWeights KroneckerFiberBudget

theorem deletionCode_card (m : ℕ) (U : List Bool) :
    Fintype.card (DeletionCode m U)=U.count true*2^(2*m) := by
  simp only [DeletionCode,Fintype.card_prod,positions_card,palette_card]
  rw [← pow_add]
  congr 2
  omega

theorem deletionCode_card_le (m : ℕ) (U : List Bool) :
    Fintype.card (DeletionCode m U) ≤ fiberBudget m (U.count true) 1 := by
  rw [deletionCode_card]
  simp only [fiberBudget,Nat.choose_one_right,Nat.mul_one]
  exact Nat.mul_le_mul_right _ (Nat.le_succ _)

end KroneckerDeletionCodeCard
end

/- Original module: KroneckerDeletionFiber -/
section
/-! A proved fiber bound for the concrete deletion map, with no recovery hypothesis. -/
set_option autoImplicit false
namespace KroneckerDeletionFiber
open KroneckerWordCounts KroneckerDeletionColoring KroneckerVerticalDeletionMap
open KroneckerDeletionCode KroneckerDeletionInjectivity KroneckerDeletionCodeCard KroneckerFiberBudget


end KroneckerDeletionFiber
end

/- Original module: KroneckerDeletionCount -/
section
/-! Count the actual deletion outputs in their surplus-indexed disjoint union. -/
set_option autoImplicit false
namespace KroneckerDeletionCount
open KroneckerWordCounts KroneckerDeletionColoring KroneckerVerticalDeletionMap
open KroneckerDeletionCode KroneckerDeletionInjectivity KroneckerDeletionCodeCard KroneckerFiberBudget
open scoped BigOperators


theorem deletion_count_bound {m : ℕ} (u v c : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (i : ℕ) (hi : i < U.length)
    (hvertical : U[i]=false) :
    pathCount m U c ≤ fiberBudget m (U.count true) 1*
      ∑ h : Fin (m+1),pathCount m (deletionPath u v U i) (c+h.val) := by
  classical
  have h := Fintype.card_le_of_injective (fun g : ConnectedColorings m U c =>
    (verticalDeletion u v c hu hv hm hpos U i hi hvertical g,
      deletionCode u v c hu hv hm hpos U i hi hvertical g))
    (deletion_pair_injective u v c hu hv hm hpos U i hi hvertical)
  rw [Fintype.card_prod] at h
  have h' := h.trans (Nat.mul_le_mul_left _ (deletionCode_card_le m U))
  simpa only [pathCount,Nat.card_eq_fintype_card,DeletionTarget,Fintype.card_sigma,Nat.mul_comm] using h'

end KroneckerDeletionCount
end

/- Original module: KroneckerRunDeletionPosition -/
section
/-! Locate a prescribed vertical deletion in a literal run word. -/
set_option autoImplicit false
namespace KroneckerRunDeletionPosition
open KroneckerStack KroneckerWordCounts KroneckerListDeletion

theorem removeAt_middle {α : Type*} (xs ys : List α) (a : α) :
    removeAt xs.length (xs++a::ys)=xs++ys := by
  simp [removeAt,List.drop_append]

def runDeletionIndex (A : List ℕ) (r : ℕ) : ℕ := (runWord A).length+1+r

theorem runWord_delete_split (A B : List ℕ) (r : ℕ) :
    runWord (A++(r+1)::B)=runWord (A++[r])++false::runWord B := by
  simp [runWord,runShape,List.replicate_succ',List.append_assoc]

theorem runDeletion_data (A B : List ℕ) (r : ℕ) :
    let U := runWord (A++(r+1)::B)
    let i := runDeletionIndex A r
    ∃ hi : i < U.length,U[i]=false ∧ removeAt i U=runWord (A++r::B) := by
  have hp : (runWord (A++[r])).length=runDeletionIndex A r := by
    simp [runWord,runShape,runDeletionIndex,Nat.add_assoc]
    omega
  have hs := runWord_delete_split A B r
  have hi : runDeletionIndex A r < (runWord (A++(r+1)::B)).length := by
    rw [hs,← hp]
    simp
  refine ⟨hi,?_,?_⟩
  · simp [hs,← hp]
  · rw [hs,← hp,removeAt_middle]
    simp [runWord]

end KroneckerRunDeletionPosition
end
end

