import KroneckerListInsertion
import KroneckerColoredShell

section

/- Original module: KroneckerInsertionShape -/
section
/-! Insertion changes only the specified shape position; old edge identities are retained. -/
set_option autoImplicit false
namespace KroneckerInsertionShape
open KroneckerStack KroneckerListInsertion KroneckerUnitInsertionNode

theorem map_insertAt {α β : Type*} (f : α → β) (i : ℕ) (a : α) (xs : List α) :
    (insertAt i a xs).map f=insertAt i (f a) (xs.map f) := by
  simp [insertAt,List.map_take,List.map_drop]

theorem shape_insert_zero (i : ℕ) (xs : List Edge) :
    shape (insertAt i (.V 0) xs)=insertAt i false (shape xs) := by
  exact map_insertAt Edge.isHorizontal i (.V 0) xs


end KroneckerInsertionShape
end

/- Original module: KroneckerInsertionZip -/
section
/-! Painting commutes with a simultaneous insertion into the shape and palette lists. -/
set_option autoImplicit false
namespace KroneckerInsertionZip
open KroneckerStack KroneckerColoring KroneckerListInsertion

theorem zip_insertAt {α β γ : Type*} (f : α → β → γ) (i : ℕ)
    (a : α) (b : β) (xs : List α) (ys : List β) (hlen : xs.length=ys.length) :
    List.zipWith f (insertAt i a xs) (insertAt i b ys)=
      insertAt i (f a b) (List.zipWith f xs ys) := by
  unfold insertAt
  rw [List.zipWith_append (by simp [hlen])]
  simp only [List.zipWith_cons_cons,← List.take_zipWith,← List.drop_zipWith]

theorem paint_insert_zero {m : ℕ} (i : ℕ) (U : List Bool) (cs : List (Palette m))
    (hlen : U.length=cs.length) :
    List.zipWith paint (insertAt i false U) (insertAt i (zeroColor m) cs)=
      insertAt i (.V 0) (List.zipWith paint U cs) := by
  exact zip_insertAt paint i false (zeroColor m) U cs hlen

end KroneckerInsertionZip
end

/- Original module: KroneckerInsertionPalette -/
section
/-! An explicit insertion palette: all old entries are copied, and new colors are fixed. -/
set_option autoImplicit false
namespace KroneckerInsertionPalette
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerListInsertion

def extraPrefix (m u : ℕ) (hu : u+2 ≤ m) : List (Palette m) :=
  fixedColor m (u+2) hu::List.replicate u (zeroColor m)

def insertedPath (u v i : ℕ) (U : List Bool) : List Bool :=
  runShape u++(insertAt i false U++runShape v)

def insertedColors {m : ℕ} (u v i : ℕ) (hu : u+2 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (cs : List (Palette m)) : List (Palette m) :=
  extraPrefix m u hu++(insertAt i (zeroColor m) cs++suffixColors m v hv hm)

theorem extraPrefix_length (m u : ℕ) (hu : u+2 ≤ m) :
    (extraPrefix m u hu).length=(runShape u).length := by
  simp [extraPrefix,runShape]

theorem extraPrefix_word (m u : ℕ) (hu : u+2 ≤ m) :
    List.zipWith paint (runShape u) (extraPrefix m u hu)=
      .H (u+2)::List.replicate u (.V 0) := by
  simp [runShape,extraPrefix,paint]

theorem insertedColors_length {m : ℕ} (u v i : ℕ) (hu : u+2 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (cs : List (Palette m))
    (hcs : cs.length=U.length) :
    (insertedColors u v i hu hv hm cs).length=(insertedPath u v i U).length := by
  simp [insertedColors,insertedPath,extraPrefix_length,insertAt_length,
    suffix_length _ _ _ _ hpos,hcs]

def insertionColoring {m : ℕ} (u v i : ℕ) (hu : u+2 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (g : Coloring m U.length) :
    Coloring m (insertedPath u v i U).length :=
  fromList (insertedColors u v i hu hv hm (List.ofFn g))
    (insertedColors_length u v i hu hv hm hpos U _ (by simp))

end KroneckerInsertionPalette
end

/- Original module: KroneckerInsertionWord -/
section
/-! The explicit palette map realizes exactly the interpreter-level insertion shell. -/
set_option autoImplicit false
namespace KroneckerInsertionWord
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerListInsertion KroneckerInsertionZip KroneckerInsertionPalette KroneckerUnitInsertionNode

theorem insertionColoring_word {m : ℕ} (u v i : ℕ) (hu : u+2 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (g : Coloring m U.length) :
    pathWord (insertedPath u v i U) (insertionColoring u v i hu hv hm hpos U g)=
      insertionShell u (v-1) ((pathWord U g).take i) ((pathWord U g).drop i) := by
  rw [insertionColoring,fromList_word]
  unfold insertedPath insertedColors
  rw [List.zipWith_append (extraPrefix_length m u hu).symm]
  rw [List.zipWith_append (by simp [insertAt_length])]
  rw [extraPrefix_word,suffix_word _ _ _ _ hpos,paint_insert_zero i U _ (by simp),← word_zip]
  simp [insertAt,insertionShell,List.append_assoc]

end KroneckerInsertionWord
end

/- Original module: KroneckerInsertionListRecovery -/
section
/-! Recovery removes the fixed shell and the fixed inserted position. -/
set_option autoImplicit false
namespace KroneckerInsertionListRecovery
open KroneckerListInsertion

def recoverList {α : Type*} (p N i : ℕ) (xs : List α) : List α :=
  let mid := (xs.drop p).take (N+1)
  mid.take i++mid.drop (i+1)

theorem recover_wrapped_insert {α : Type*} (pre post cs : List α) (i : ℕ) (a : α)
    (hi : i ≤ cs.length) :
    recoverList pre.length cs.length i (pre++(insertAt i a cs++post))=cs := by
  have hm : (insertAt i a cs++post).take (cs.length+1)=insertAt i a cs := by
    rw [← insertAt_length i a cs,List.take_left]
  unfold recoverList
  rw [List.drop_left,hm]
  exact erase_insertAt i a cs hi


end KroneckerInsertionListRecovery
end

/- Original module: KroneckerInsertionColorRecovery -/
section
/-! The recovery theorem retains full palette entries, including the binomial colors. -/
set_option autoImplicit false
namespace KroneckerInsertionColorRecovery
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerColoredShell
open KroneckerInsertionPalette KroneckerInsertionListRecovery

theorem recover_insertion_colors {m : ℕ} (u v i : ℕ) (hu : u+2 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (hi : i ≤ U.length)
    (g : Coloring m U.length) :
    recoverList (u+1) U.length i
      (List.ofFn (insertionColoring u v i hu hv hm hpos U g))=List.ofFn g := by
  rw [insertionColoring,fromList_colors]
  have h := recover_wrapped_insert (extraPrefix m u hu) (suffixColors m v hv hm)
    (List.ofFn g) i (zeroColor m) (by simpa using hi)
  simpa [insertedColors,extraPrefix] using h

theorem insertionColoring_injective {m : ℕ} (u v i : ℕ) (hu : u+2 ≤ m) (hv : v-1 ≤ m)
    (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool) (hi : i ≤ U.length) :
    Function.Injective (insertionColoring u v i hu hv hm hpos U) := by
  intro x y hxy
  have h := congrArg (fun g => recoverList (u+1) U.length i (List.ofFn g)) hxy
  apply List.ofFn_injective
  simpa only [recover_insertion_colors u v i hu hv hm hpos U hi] using h

end KroneckerInsertionColorRecovery
end

/- Original module: KroneckerInsertionColorConnected -/
section
/-! Connectedness of the literal colored map at every legal position after the first edge. -/
set_option autoImplicit false
namespace KroneckerInsertionColorConnected
open KroneckerStack KroneckerColoring KroneckerWordCounts
open KroneckerInsertionPalette KroneckerInsertionWord KroneckerVerticalInsertionConnected

theorem insertionColoring_connected {m : ℕ} (u v i c : ℕ) (hu : u+2 ≤ m)
    (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) (U : List Bool)
    (hi : 1 ≤ i ∧ i ≤ U.length) (g : Coloring m U.length)
    (hg : Connected m (pathWord U g) c) :
    Connected m (pathWord (insertedPath u v i U)
      (insertionColoring u v i hu hv hm hpos U g)) c := by
  rw [insertionColoring_word]
  have hne : (pathWord U g).take i≠[] := by
    apply List.ne_nil_of_length_pos
    rw [List.length_take,pathWord_length]
    omega
  exact insertion_shell_connected m u (v-1) c _ _ hne hu hv hm (by simpa using hg)

end KroneckerInsertionColorConnected
end

/- Original module: KroneckerVerticalInsertionMap -/
section
/-! The finite injective map asserted by the manuscript's vertical insertion lemma. -/
set_option autoImplicit false
namespace KroneckerVerticalInsertionMap
open KroneckerStack KroneckerWordCounts KroneckerInsertionPalette
open KroneckerInsertionColorConnected KroneckerInsertionColorRecovery

def verticalInsertion {m : ℕ} (u v i c : ℕ) (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2)
    (U : List Bool) (hi : 1 ≤ i ∧ i ≤ U.length) :
    ConnectedColorings m U c → ConnectedColorings m (insertedPath u v i U) c :=
  fun g => ⟨insertionColoring u v i (by omega) (by omega) (by omega) hv.1 U g.val,
    insertionColoring_connected u v i c (by omega) (by omega) (by omega) hv.1 U hi g.val g.property⟩



end KroneckerVerticalInsertionMap
end
end

section

/-! A vertical insertion in one specified run, expressed using the manuscript run counts. -/
set_option autoImplicit false
namespace KroneckerVerticalInsertionRuns
open KroneckerStack KroneckerWordCounts KroneckerListInsertion
open KroneckerInsertionPalette KroneckerVerticalInsertionMap

theorem insertAt_boundary {α : Type*} (pre post : List α) (a : α) :
    insertAt pre.length a (pre++post)=pre++a::post := by
  simp [insertAt]

theorem insert_run (pre post : List Bool) (r : ℕ) :
    insertAt (pre.length+1) false (pre++(runShape r++post))=
      pre++(runShape (r+1)++post) := by
  have h := insertAt_boundary (pre++[true]) (List.replicate r false++post) false
  simpa [runShape,List.append_assoc,List.replicate_succ] using h

theorem insert_runWord (pre post : List ℕ) (r : ℕ) :
    insertAt ((runWord pre).length+1) false (runWord (pre++r::post))=
      runWord (pre++(r+1)::post) := by
  simpa [runWord] using insert_run (runWord pre) (runWord post) r


end KroneckerVerticalInsertionRuns
end

