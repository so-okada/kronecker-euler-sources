import KroneckerTaggedListEdits
import KroneckerVerticalInsertionRuns

section

/- Original module: KroneckerTagCoverage -/
section
/-! Every original horizontal survives; an original vertical can disappear only into the fixed deletion record. -/
set_option autoImplicit false
namespace KroneckerTagCoverage
open KroneckerOriginalTags KroneckerTaggedListEdits KroneckerListDeletion KroneckerListInsertion

structure Covers {n q : ℕ} (tags : List (Tag n q)) (deleted : List (Fin q)) : Prop where
  horizontal : ∀ i,some (.inl i) ∈ tags
  vertical : ∀ j,j ∉ deleted → some (.inr j) ∈ tags

theorem covers_insert {n q : ℕ} {tags : List (Tag n q)} {deleted : List (Fin q)}
    (h : Covers tags deleted) (i : ℕ) : Covers (insertAt i none tags) deleted := by
  constructor
  · intro j; exact mem_insertAt tags i _ none (h.horizontal j)
  · intro j hj; exact mem_insertAt tags i _ none (h.vertical j hj)

theorem covers_remove {n q : ℕ} {tags : List (Tag n q)} {deleted : List (Fin q)}
    (h : Covers tags deleted) (i : ℕ) (hi : i < tags.length) (ht : Compatible false tags[i]) :
    Covers (removeAt i tags) (verticalRecord tags[i]++deleted) := by
  constructor
  · intro j
    exact mem_removeAt_of_ne tags i hi (h.horizontal j) (Ne.symm (vertical_tag_ne_horizontal ht j))
  · intro j hj
    have hjold : j ∉ deleted := fun hm => hj (List.mem_append_right _ hm)
    apply mem_removeAt_of_ne tags i hi (h.vertical j hjold)
    intro he
    apply hj
    rw [← he]
    simp [verticalRecord]

theorem covers_append {n q : ℕ} {tags : List (Tag n q)} {deleted : List (Fin q)}
    (h : Covers tags deleted) (pre post : List (Tag n q)) : Covers (pre++tags++post) deleted := by
  constructor
  · intro i; exact List.mem_append_left _ (List.mem_append_right _ (h.horizontal i))
  · intro i hi; exact List.mem_append_left _ (List.mem_append_right _ (h.vertical i hi))

end KroneckerTagCoverage
end

/- Original module: KroneckerTagUpdateRetention -/
section
/-! One earlier horizontal update and one later deletion preserve all unlogged original palettes. -/
set_option autoImplicit false
namespace KroneckerTagUpdateRetention
open KroneckerColoring KroneckerInputRecovery KroneckerOriginalTags KroneckerAlignedLists
open KroneckerTagChanges KroneckerListDeletion

theorem update_delete_keeps {m n q : ℕ} (source : Input m n q) (changed : List (Fin n))
    (tags : List (Tag n q)) (cs : List (Palette m))
    (hkeep : List.Forall₂ (Keeps source changed) tags cs)
    (i j : ℕ) (hi : i < tags.length) (hj : j < i)
    (ht : Compatible true tags[j]) (x : Palette m) :
    List.Forall₂ (Keeps source (horizontalRecord tags[j]++changed)) (removeAt i tags)
      (((cs.take i).set j x)++cs.drop (i+1)) := by
  have hw := aligned_keeps_mono (fun a ha => List.mem_append_right (horizontalRecord tags[j]) ha) hkeep
  apply List.rel_append
  · apply rel_set_right (List.forall₂_take i hw) j (by simp; omega) x
    simpa only [List.getElem_take] using keeps_changed source changed tags[j] ht x
  · exact List.forall₂_drop (i+1) hw

theorem horizontal_log_step_bound {n q : ℕ} (t : Tag n q) (xs : List (Fin n)) :
    (horizontalRecord t++xs).length ≤ xs.length+1 := by
  have := horizontalRecord_length t
  simp only [List.length_append]
  omega

theorem vertical_log_step_bound {n q : ℕ} (t : Tag n q) (xs : List (Fin q)) :
    (verticalRecord t++xs).length ≤ xs.length+1 := by
  have := verticalRecord_length t
  simp only [List.length_append]
  omega

end KroneckerTagUpdateRetention
end

/- Original module: KroneckerEmptyTags -/
section
/-! New edges contribute no original-label recovery information. -/
set_option autoImplicit false
namespace KroneckerEmptyTags
open KroneckerColoring KroneckerInputRecovery KroneckerOriginalTags

theorem compatible_none {n q : ℕ} (U : List Bool) :
    List.Forall₂ Compatible U (List.replicate U.length (none : Tag n q)) := by
  induction U with
  | nil => exact .nil
  | cons b U ih => exact .cons trivial ih

theorem keeps_none {m n q : ℕ} (source : Input m n q) (changed : List (Fin n))
    (cs : List (Palette m)) :
    List.Forall₂ (Keeps source changed) (List.replicate cs.length (none : Tag n q)) cs := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih => exact .cons trivial ih

end KroneckerEmptyTags
end

/- Original module: KroneckerInitialTags -/
section
/-! Label the original path by its horizontal and vertical position alphabets. -/
set_option autoImplicit false
namespace KroneckerInitialTags
open KroneckerOriginalTags KroneckerOrientationPositions

noncomputable def initialTag (U : List Bool) (i : Fin U.length) :
    Tag (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) :=
  if h : U[i.val]=true then some (.inl (Fintype.equivFin (Positions U true) ⟨i,h⟩))
  else some (.inr (Fintype.equivFin (Positions U false) ⟨i,by cases hb : U[i.val] <;> simp_all⟩))

noncomputable def initialTags (U : List Bool) := List.ofFn (initialTag U)

theorem initialTag_horizontal (U : List Bool) (i : Positions U true) :
    initialTag U i.val=some (.inl (Fintype.equivFin (Positions U true) i)) := by
  simp [initialTag,i.property]

theorem initialTag_vertical (U : List Bool) (i : Positions U false) :
    initialTag U i.val=some (.inr (Fintype.equivFin (Positions U false) i)) := by
  simp [initialTag,i.property]

theorem initialTag_compatible (U : List Bool) (i : Fin U.length) :
    Compatible U[i.val] (initialTag U i) := by
  cases hb : U[i.val] with
  | false => simp [initialTag,hb,Compatible]
  | true => simp [initialTag,hb,Compatible]

end KroneckerInitialTags
end

/- Original module: KroneckerInitialCoverage -/
section
/-! Every original edge has a corresponding tag in the initial path. -/
set_option autoImplicit false
namespace KroneckerInitialCoverage
open KroneckerOriginalTags KroneckerInitialTags KroneckerTagCoverage KroneckerOrientationPositions

theorem initialTags_cover (U : List Bool) : Covers (initialTags U) [] := by
  constructor
  · intro i
    let p := (Fintype.equivFin (Positions U true)).symm i
    apply List.mem_ofFn.mpr
    refine ⟨p.val,?_⟩
    rw [initialTag_horizontal U p]
    simp [p]
  · intro j _
    let p := (Fintype.equivFin (Positions U false)).symm j
    apply List.mem_ofFn.mpr
    refine ⟨p.val,?_⟩
    rw [initialTag_vertical U p]
    simp [p]

theorem initialTags_compatible (U : List Bool) :
    List.Forall₂ Compatible U (initialTags U) := by
  have h := KroneckerAlignedLists.rel_ofFn (fun i : Fin U.length => U[i.val]) (initialTag U)
    (initialTag_compatible U)
  simpa only [List.ofFn_getElem, initialTags] using h

end KroneckerInitialCoverage
end

/- Original module: KroneckerInitialPaletteRetention -/
section
/-! The initial tagged coloring retains the complete original horizontal and vertical arrays. -/
set_option autoImplicit false
namespace KroneckerInitialPaletteRetention
open KroneckerColoring KroneckerOriginalTags KroneckerInitialTags KroneckerWordPaletteSplit
open KroneckerOrientationPositions KroneckerAlignedLists

theorem initialTag_keeps {m : ℕ} (U : List Bool) (g : Coloring m U.length) (i : Fin U.length) :
    Keeps (splitColoring U g) [] (initialTag U i) (g i) := by
  cases hb : U[i.val] with
  | false =>
    rw [initialTag_vertical U ⟨i,hb⟩]
    exact (split_vertical U g ⟨i,hb⟩).symm
  | true =>
    rw [initialTag_horizontal U ⟨i,hb⟩]
    intro _
    exact (split_horizontal U g ⟨i,hb⟩).symm

theorem initialTags_keep {m : ℕ} (U : List Bool) (g : Coloring m U.length) :
    List.Forall₂ (Keeps (splitColoring U g) []) (initialTags U) (List.ofFn g) :=
  rel_ofFn (initialTag U) g (initialTag_keeps U g)

end KroneckerInitialPaletteRetention
end

/- Original module: KroneckerTaggedLayout -/
section
/-! A fixed tag layout and deletion record depend on positions, not on the input grading. -/
set_option autoImplicit false
namespace KroneckerTaggedLayout
open KroneckerOriginalTags KroneckerTagCoverage KroneckerColoring KroneckerInputRecovery
open KroneckerInitialTags KroneckerInitialCoverage KroneckerInitialPaletteRetention
open KroneckerOrientationPositions KroneckerWordPaletteSplit

structure Layout (n q : ℕ) (U : List Bool) where
  tags : List (Tag n q)
  typed : List.Forall₂ Compatible U tags
  deleted : List (Fin q)
  covers : Covers tags deleted

theorem layout_length {n q : ℕ} {U : List Bool} (L : Layout n q U) : L.tags.length=U.length :=
  L.typed.length_eq.symm

def Retains {m n q : ℕ} {U : List Bool} (source : Input m n q) (changed : List (Fin n))
    (L : Layout n q U) (g : Coloring m U.length) : Prop :=
  List.Forall₂ (Keeps source changed) L.tags (List.ofFn g)

noncomputable def initialLayout (U : List Bool) :
    Layout (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) U :=
  ⟨initialTags U,initialTags_compatible U,[],initialTags_cover U⟩

theorem initialLayout_retains {m : ℕ} (U : List Bool) (g : Coloring m U.length) :
    Retains (splitColoring U g) [] (initialLayout U) g := initialTags_keep U g

theorem compatible_at {n q : ℕ} {U : List Bool} (L : Layout n q U) (i : Fin U.length) :
    Compatible U[i.val] (L.tags[i.val]'(by rw [layout_length]; exact i.isLt)) :=
  L.typed.get i.isLt (by rw [layout_length]; exact i.isLt)

end KroneckerTaggedLayout
end

/- Original module: KroneckerWrappedTags -/
section
/-! Prescribed shell edges carry no original labels; the interior layout is unchanged. -/
set_option autoImplicit false
namespace KroneckerWrappedTags
open KroneckerStack KroneckerColoring KroneckerInputRecovery KroneckerOriginalTags
open KroneckerEmptyTags KroneckerTaggedLayout KroneckerColoredShell KroneckerTagCoverage

def shellTags {n q : ℕ} (u v : ℕ) (tags : List (Tag n q)) : List (Tag n q) :=
  List.replicate (u+1) none++tags++List.replicate (v+1) none

def wrapLayout {n q : ℕ} {U : List Bool} (u v : ℕ) (L : Layout n q U) :
    Layout n q (shellPath u v U) where
  tags := shellTags u v L.tags
  typed := by
    simpa [shellTags,shellPath,runShape,List.append_assoc] using
      List.rel_append (compatible_none (n:=n) (q:=q) (runShape u))
        (List.rel_append L.typed (compatible_none (runShape v)))
  deleted := L.deleted
  covers := covers_append L.covers _ _


theorem wrap_keeps {m n q : ℕ} (source : Input m n q) (changed : List (Fin n))
    (u v : ℕ) (tags : List (Tag n q)) (cs pre post : List (Palette m))
    (h : List.Forall₂ (Keeps source changed) tags cs) (hp : pre.length=u+1) (hq : post.length=v+1) :
    List.Forall₂ (Keeps source changed) (shellTags u v tags) (pre++cs++post) := by
  simpa only [hp,hq,shellTags] using
    List.rel_append (List.rel_append (keeps_none source changed pre) h) (keeps_none source changed post)

theorem shellColoring_retains {m n q : ℕ} {U : List Bool} (source : Input m n q)
    (changed : List (Fin n)) (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) :
    Retains source changed (wrapLayout u v L) (shellColoring u v hu hv hm hpos U g) := by
  unfold Retains
  rw [shellColoring,fromList_colors]
  simpa only [wrapLayout,shellColors,List.append_assoc] using
    wrap_keeps source changed u v L.tags (List.ofFn g) (prefixColors m u hu) (suffixColors m v hv hm) h
      (by simp [prefixColors]) (by simpa [runShape] using suffix_length m v hv hm hpos)

end KroneckerWrappedTags
end
end

section

/- Original module: KroneckerDecrementLog -/
section
/-! A deletion-owner log counts repeated decrements without recording colors repeatedly. -/
set_option autoImplicit false
namespace KroneckerDecrementLog
open KroneckerDecrementSlack
open scoped BigOperators

def decrementLog {n : ℕ} (owners : List (Fin n)) : Fin n → ℕ := fun i => owners.count i

theorem decrementLog_sum {n : ℕ} (owners : List (Fin n)) :
    (∑ i,decrementLog owners i)=owners.length := by
  induction owners with
  | nil => simp [decrementLog]
  | cons j owners ih =>
    simp only [decrementLog,List.count_cons,beq_iff_eq] at *
    simp [Finset.sum_add_distrib,ih]

theorem decrementLog_append {n : ℕ} (xs ys : List (Fin n)) :
    decrementLog (xs++ys)=fun i => decrementLog xs i+decrementLog ys i := by
  funext i
  simp [decrementLog]

def boundedLog {n D : ℕ} (owners : List (Fin n)) (h : owners.length ≤ D) : Decrements n D :=
  ⟨decrementLog owners,by simpa only [decrementLog_sum] using h⟩

theorem boundedLog_zero_iff {n D : ℕ} (owners : List (Fin n)) (h : owners.length ≤ D) (i : Fin n) :
    (boundedLog owners h).val i=0 ↔ i ∉ owners := by
  change owners.count i=0 ↔ i ∉ owners
  exact List.count_eq_zero

end KroneckerDecrementLog
end

/- Original module: KroneckerEditedLayouts -/
section
/-! Static layouts for one vertical insertion or deletion. -/
set_option autoImplicit false
namespace KroneckerEditedLayouts
open KroneckerOriginalTags KroneckerTaggedLayout KroneckerTaggedListEdits KroneckerTagCoverage
open KroneckerListInsertion KroneckerListDeletion KroneckerTagUpdateRetention

def insertLayout {n q : ℕ} {U : List Bool} (i : ℕ) (L : Layout n q U) :
    Layout n q (insertAt i false U) where
  tags := insertAt i none L.tags
  typed := rel_insertAt L.typed i false none trivial
  deleted := L.deleted
  covers := covers_insert L.covers i

def removeLayout {n q : ℕ} {U : List Bool} (i : ℕ) (hi : i < U.length) (hv : U[i]=false)
    (L : Layout n q U) : Layout n q (removeAt i U) where
  tags := removeAt i L.tags
  typed := rel_removeAt L.typed i
  deleted := verticalRecord (L.tags[i]'(by rw [layout_length]; exact hi))++L.deleted
  covers := covers_remove L.covers i (by rw [layout_length]; exact hi)
    (by simpa only [hv] using compatible_at L ⟨i,hi⟩)


theorem removeLayout_deleted_bound {n q : ℕ} {U : List Bool} (i : ℕ) (hi : i < U.length)
    (hv : U[i]=false) (L : Layout n q U) :
    (removeLayout i hi hv L).deleted.length ≤ L.deleted.length+1 :=
  vertical_log_step_bound _ _

end KroneckerEditedLayouts
end

/- Original module: KroneckerRecoverySpecification -/
section
/-! Explicit recovery hypotheses for an arbitrary proposed map.
No existence of the manuscript's deletion/composition map is asserted here. -/
set_option autoImplicit false
namespace KroneckerRecoverySpecification
open KroneckerDecrementSlack KroneckerRecoveryCode KroneckerInputRecovery

structure RecoverySpec {α β : Type*} (m n q D : ℕ) (source : α → Input m n q) (f : α → β) where
  deleted : Finset (Fin q)
  deleted_card : deleted.card ≤ D
  delta : α → Decrements n D
  retained : β → Input m n q
  horizontal_unchanged : ∀ a i,(delta a).val i=0 → (retained (f a)).1 i=(source a).1 i
  vertical_retained : ∀ a i,i ∉ deleted → (retained (f a)).2 i=(source a).2 i

noncomputable def code {α β : Type*} {m n q D : ℕ} {source : α → Input m n q} {f : α → β}
    (s : RecoverySpec m n q D source f) (a : α) : RecoveryCode m n D :=
  encodeInput (s.delta a) s.deleted s.deleted_card (source a)

theorem recover_source {α β : Type*} {m n q D : ℕ} {source : α → Input m n q} {f : α → β}
    (s : RecoverySpec m n q D source f) (a : α) :
    decodeInput s.deleted s.deleted_card (s.retained (f a)) (code s a)=source a :=
  decode_encodeInput (s.delta a) s.deleted s.deleted_card (source a) (s.retained (f a))
    (s.horizontal_unchanged a) (s.vertical_retained a)

theorem target_code_injective {α β : Type*} {m n q D : ℕ} {source : α → Input m n q} {f : α → β}
    (s : RecoverySpec m n q D source f) (hs : Function.Injective source) :
    Function.Injective (fun a => (f a,code s a)) := by
  intro a b hab
  apply hs
  have hf : f a=f b := congrArg Prod.fst hab
  have hc : code s a=code s b := congrArg Prod.snd hab
  rw [← recover_source s a,← recover_source s b,hf,hc]

end KroneckerRecoverySpecification
end

/- Original module: KroneckerReconstructionFiber -/
section
/-! A sharp fiber budget, conditional on the stated recovery properties of the proposed map. -/
set_option autoImplicit false
namespace KroneckerReconstructionFiber
open KroneckerInputRecovery KroneckerRecoveryCode KroneckerRecoverySpecification KroneckerFiberBudget

theorem fiber_code_injective {α β : Type*} {m n q D : ℕ}
    {source : α → Input m n q} {f : α → β} (s : RecoverySpec m n q D source f)
    (hs : Function.Injective source) (b : β) :
    Function.Injective (fun a : {a // f a=b} => code s a.val) := by
  intro a a' h
  apply Subtype.ext
  apply target_code_injective s hs
  exact Prod.ext (a.property.trans a'.property.symm) h

theorem reconstruction_fiber_bound {α β : Type*} [Fintype α] {m n q D : ℕ}
    {source : α → Input m n q} {f : α → β} (s : RecoverySpec m n q D source f)
    (hs : Function.Injective source) (b : β) :
    Nat.card {a // f a=b} ≤ fiberBudget m n D := by
  classical
  rw [Nat.card_eq_fintype_card,← recoveryCode_card]
  exact Fintype.card_le_of_injective (fun a : {a // f a=b} => code s a.val)
    (fiber_code_injective s hs b)

end KroneckerReconstructionFiber
end

/- Original module: KroneckerReconstructionCount -/
section
/-! The finite counting consequence of the explicit reconstruction conditions. -/
set_option autoImplicit false
namespace KroneckerReconstructionCount
open KroneckerInputRecovery KroneckerRecoveryCode KroneckerRecoverySpecification KroneckerFiberBudget

theorem reconstruction_count_bound {α β : Type*} [Fintype α] [Fintype β] {m n q D : ℕ}
    {source : α → Input m n q} {f : α → β} (s : RecoverySpec m n q D source f)
    (hs : Function.Injective source) :
    Nat.card α ≤ fiberBudget m n D*Nat.card β := by
  have h := Fintype.card_le_of_injective (fun a => (f a,code s a)) (target_code_injective s hs)
  rw [Fintype.card_prod,recoveryCode_card] at h
  simpa only [Nat.card_eq_fintype_card,Nat.mul_comm] using h

theorem reconstruction_real_bound {α β : Type*} [Fintype α] [Fintype β] {m n q D : ℕ}
    {source : α → Input m n q} {f : α → β} (s : RecoverySpec m n q D source f)
    (hs : Function.Injective source) :
    (Nat.card α : ℝ)/(fiberBudget m n D : ℝ) ≤ (Nat.card β : ℝ) := by
  have hp : (0 : ℝ) < fiberBudget m n D := by exact_mod_cast fiberBudget_positive m n D
  apply (div_le_iff₀ hp).mpr
  have h := reconstruction_count_bound s hs
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

end KroneckerReconstructionCount
end

/- Original module: KroneckerRepeatedDecrementRecovery -/
section
/-! One original palette per changed owner suffices, including repeated decrements at that owner. -/
set_option autoImplicit false
namespace KroneckerRepeatedDecrementRecovery
open KroneckerColoring KroneckerDecrementLog KroneckerHorizontalRecovery
open KroneckerDecrementSupport



end KroneckerRepeatedDecrementRecovery
end

/- Original module: KroneckerTaggedInsertion -/
section
/-! The actual colored insertion preserves every original palette and its fixed layout. -/
set_option autoImplicit false
namespace KroneckerTaggedInsertion
open KroneckerStack KroneckerColoring KroneckerInputRecovery KroneckerOriginalTags KroneckerTaggedLayout
open KroneckerWrappedTags KroneckerEditedLayouts KroneckerColoredShell KroneckerInsertionPalette
open KroneckerTaggedListEdits

set_option backward.isDefEq.respectTransparency false in
theorem insertion_retains {m n q : ℕ} {U : List Bool} (source : Input m n q)
    (changed : List (Fin n)) (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (u v i : ℕ) (hu : u+2 ≤ m) (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v) :
    Retains source changed (wrapLayout u v (insertLayout i L))
      (insertionColoring u v i hu hv hm hpos U g) := by
  unfold Retains
  rw [insertionColoring,fromList_colors]
  have hi := rel_insertAt h i none (zeroColor m) trivial
  simpa only [wrapLayout,insertLayout,insertedColors,List.append_assoc] using
    wrap_keeps source changed u v _ _ (extraPrefix m u hu) (suffixColors m v hv hm) hi
      (by simp [extraPrefix]) (by simpa [runShape] using suffix_length m v hv hm hpos)

end KroneckerTaggedInsertion
end

/- Original module: KroneckerTaggedDeletion -/
section
/-! The actual colored deletion logs at most one original horizontal label and retains all others. -/
set_option autoImplicit false
namespace KroneckerTaggedDeletion
open KroneckerStack KroneckerColoring KroneckerInputRecovery KroneckerOriginalTags KroneckerTaggedLayout
open KroneckerWrappedTags KroneckerEditedLayouts KroneckerColoredShell KroneckerDeletionColoring
open KroneckerDeletionInteriorColors KroneckerTagUpdateRetention KroneckerLowerPalette

def changedAt {n q : ℕ} {U : List Bool} (L : Layout n q U) (j : Fin U.length)
    (changed : List (Fin n)) : List (Fin n) :=
  horizontalRecord (L.tags[j.val]'(by rw [layout_length]; exact j.isLt))++changed

theorem changedAt_bound {n q : ℕ} {U : List Bool} (L : Layout n q U) (j : Fin U.length)
    (changed : List (Fin n)) : (changedAt L j changed).length ≤ changed.length+1 :=
  horizontal_log_step_bound _ _

set_option backward.isDefEq.respectTransparency false in
theorem deletion_retains {m n q : ℕ} {U : List Bool} (source : Input m n q)
    (changed : List (Fin n)) (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (u v i : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m) (hm : 2 ≤ m) (hpos : 1 ≤ v)
    (hi : i < U.length) (hvertical : U[i]=false) (j : Fin i) (hj : U[j.val]=true) :
    Retains source (changedAt L ⟨j.val,lt_trans j.isLt hi⟩ changed)
      (wrapLayout u v (removeLayout i hi hvertical L))
      (deletionColoring u v hu hv hm hpos U i hi j g) := by
  have ht : Compatible true (L.tags[j.val]'(by rw [layout_length]; exact lt_trans j.isLt hi)) := by
    simpa only [hj] using compatible_at L ⟨j.val,lt_trans j.isLt hi⟩
  have hk := update_delete_keeps source changed L.tags (List.ofFn g) h i j.val
    (by rw [layout_length]; exact hi) j.isLt ht (lowerPalette (g ⟨j.val,lt_trans j.isLt hi⟩))
  unfold Retains
  simp only [deletionColoring,shellColoring,editedColoring,fromList_colors]
  simpa only [wrapLayout,removeLayout,changedAt,shellColors,editedColors,List.append_assoc] using
    wrap_keeps source _ u v _ _ (prefixColors m u hu) (suffixColors m v hv hm) hk
      (by simp [prefixColors]) (by simpa [runShape] using suffix_length m v hv hm hpos)

end KroneckerTaggedDeletion
end

/- Original module: KroneckerTaggedAutomaticShell -/
section
/-! Draining and preserving shells retain the same original tagged palettes. -/
set_option autoImplicit false
namespace KroneckerTaggedAutomaticShell
open KroneckerStack KroneckerColoring KroneckerInputRecovery KroneckerTaggedLayout KroneckerWrappedTags
open KroneckerColoredShell KroneckerDrainingShell KroneckerAutomaticShell

set_option backward.isDefEq.respectTransparency false in
theorem drainColoring_retains {m n q : ℕ} {U : List Bool} (source : Input m n q)
    (changed : List (Fin n)) (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m) (hm : 3 ≤ m) (hpos : 1 ≤ v) :
    Retains source changed (wrapLayout u v L) (drainColoring u v hu hv hm hpos U g) := by
  unfold Retains
  rw [drainColoring,KroneckerBinaryShell.binaryColoring,fromList_colors]
  simpa [wrapLayout,KroneckerBinaryShell.binaryColors,List.append_assoc] using
    wrap_keeps source changed u v L.tags (List.ofFn g) (prefixColors m u hu)
      (KroneckerBinaryShell.suffixColors m v hv hm) h (by simp [prefixColors])
      (by simpa [runShape] using KroneckerBinaryShell.suffix_length m v hv hm hpos)

theorem autoColoring_retains {m n q : ℕ} {U : List Bool} (source : Input m n q)
    (changed : List (Fin n)) (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (u v c : ℕ) (hm : 3 ≤ m) (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) :
    Retains source changed (wrapLayout u v L) (autoColoring u v c hm hu hv U g) := by
  unfold autoColoring
  split
  · exact shellColoring_retains source changed L g h u v _ _ _ hv.1
  · exact drainColoring_retains source changed L g h u v _ _ hm hv.1

end KroneckerTaggedAutomaticShell
end

/- Original module: KroneckerTagLookup -/
section
/-! Read a retained original palette from an output position selected only by its fixed tag layout. -/
set_option autoImplicit false
namespace KroneckerTagLookup
open KroneckerOriginalTags KroneckerTaggedLayout KroneckerColoring KroneckerInputRecovery

theorem tag_position_exists {n q : ℕ} {U : List Bool} (L : Layout n q U) (t : Tag n q)
    (ht : t ∈ L.tags) : ∃ i : Fin U.length,L.tags[i.val]'(by rw [layout_length]; exact i.isLt)=t := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ht
  exact ⟨⟨i,by rw [← layout_length L]; exact hi⟩,he⟩

noncomputable def tagPosition {n q : ℕ} {U : List Bool} (L : Layout n q U) (t : Tag n q)
    (ht : t ∈ L.tags) : Fin U.length := Classical.choose (tag_position_exists L t ht)

theorem tagPosition_spec {n q : ℕ} {U : List Bool} (L : Layout n q U) (t : Tag n q)
    (ht : t ∈ L.tags) :
    L.tags[(tagPosition L t ht).val]'(by rw [layout_length]; exact (tagPosition L t ht).isLt)=t :=
  Classical.choose_spec (tag_position_exists L t ht)

theorem tag_lookup_keeps {m n q : ℕ} {U : List Bool} (source : Input m n q) (changed : List (Fin n))
    (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (t : Tag n q) (ht : t ∈ L.tags) : Keeps source changed t (g (tagPosition L t ht)) := by
  have he := h.get (i:=(tagPosition L t ht).val)
    (by rw [layout_length]; exact (tagPosition L t ht).isLt)
    (by simpa only [List.length_ofFn] using (tagPosition L t ht).isLt)
  simpa only [List.get_eq_getElem,List.getElem_ofFn,tagPosition_spec] using he

end KroneckerTagLookup
end

/- Original module: KroneckerTaggedDecoder -/
section
/-! An output-only retained-array decoder; deleted original vertical entries receive a fixed placeholder. -/
set_option autoImplicit false
namespace KroneckerTaggedDecoder
open KroneckerColoring KroneckerInputRecovery KroneckerTaggedLayout KroneckerTagLookup

noncomputable def retained {m n q : ℕ} {U : List Bool} (L : Layout n q U)
    (g : Coloring m U.length) : Input m n q := by
  classical
  exact ⟨fun i => g (tagPosition L (some (.inl i)) (L.covers.horizontal i)),
    fun j => if hj : j ∈ L.deleted then zeroColor m
      else g (tagPosition L (some (.inr j)) (L.covers.vertical j hj))⟩

theorem retained_horizontal {m n q : ℕ} {U : List Bool} (source : Input m n q) (changed : List (Fin n))
    (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (i : Fin n) (hi : i ∉ changed) : (retained L g).1 i=source.1 i :=
  tag_lookup_keeps source changed L g h (some (.inl i)) (L.covers.horizontal i) hi

theorem retained_vertical {m n q : ℕ} {U : List Bool} (source : Input m n q) (changed : List (Fin n))
    (L : Layout n q U) (g : Coloring m U.length) (h : Retains source changed L g)
    (j : Fin q) (hj : j ∉ L.deleted) : (retained L g).2 j=source.2 j := by
  simpa only [retained, dite_eq_right hj, KroneckerOriginalTags.Keeps] using
    tag_lookup_keeps source changed L g h (some (.inr j)) (L.covers.vertical j hj)

end KroneckerTaggedDecoder
end

/- Original module: KroneckerTaggedRecoverySpec -/
section
/-! Derive the existing compressed recovery specification from proved tagged retention. -/
set_option autoImplicit false
namespace KroneckerTaggedRecoverySpec
open KroneckerColoring KroneckerInputRecovery KroneckerTaggedLayout KroneckerTaggedDecoder
open KroneckerDecrementLog KroneckerRecoverySpecification

noncomputable def taggedSpec {α β : Type*} {m n q D : ℕ} {U : List Bool}
    (source : α → Input m n q) (f : α → β) (out : β → Coloring m U.length)
    (L : Layout n q U) (changed : α → List (Fin n))
    (hc : ∀ a,(changed a).length ≤ D) (hd : L.deleted.length ≤ D)
    (hkeep : ∀ a,Retains (source a) (changed a) L (out (f a))) : RecoverySpec m n q D source f where
  deleted := L.deleted.toFinset
  deleted_card := (List.toFinset_card_le L.deleted).trans hd
  delta := fun a => boundedLog (changed a) (hc a)
  retained := fun b => retained L (out b)
  horizontal_unchanged := by
    intro a i hi
    exact retained_horizontal (source a) (changed a) L (out (f a)) (hkeep a) i
      ((boundedLog_zero_iff (changed a) (hc a) i).mp hi)
  vertical_retained := by
    intro a j hj
    exact retained_vertical (source a) (changed a) L (out (f a)) (hkeep a) j (by simpa using hj)


end KroneckerTaggedRecoverySpec
end

/- Original module: KroneckerWordRecoveryFiber -/
section
/-! The recovery criterion specialized to the actual finite sets of connected word colorings.
The criterion is explicit data to be supplied for a future surgery map. -/
set_option autoImplicit false
namespace KroneckerWordRecoveryFiber
open KroneckerWordCounts KroneckerWordPaletteSplit KroneckerOrientationPositions
open KroneckerInputRecovery KroneckerRecoverySpecification KroneckerReconstructionFiber
open KroneckerFiberBudget

noncomputable def connectedSource (m : ℕ) (U : List Bool) (c : ℕ)
    (g : ConnectedColorings m U c) :
    Input m (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) :=
  splitColoring U g.val

theorem connectedSource_injective (m : ℕ) (U : List Bool) (c : ℕ) :
    Function.Injective (connectedSource m U c) := by
  intro a b hab
  apply Subtype.ext
  exact splitColoring_injective U hab

abbrev WordRecoverySpec {m D : ℕ} (U V : List Bool) (c c' : ℕ)
    (f : ConnectedColorings m U c → ConnectedColorings m V c') :=
  RecoverySpec m (Fintype.card (Positions U true)) (Fintype.card (Positions U false)) D
    (connectedSource m U c) f

theorem word_recovery_fiber_bound {m D c c' : ℕ} {U V : List Bool}
    {f : ConnectedColorings m U c → ConnectedColorings m V c'}
    (s : WordRecoverySpec (D:=D) U V c c' f) (y : ConnectedColorings m V c') :
    Nat.card {g // f g=y} ≤ fiberBudget m (U.count true) D := by
  classical
  simpa only [positions_card] using
    reconstruction_fiber_bound s (connectedSource_injective m U c) y

end KroneckerWordRecoveryFiber
end

/- Original module: KroneckerWordRecoveryCount -/
section
/-! Conditional finite comparison for actual pathCount, with no assumed counting bound. -/
set_option autoImplicit false
namespace KroneckerWordRecoveryCount
open KroneckerWordCounts KroneckerOrientationPositions KroneckerWordRecoveryFiber
open KroneckerReconstructionCount KroneckerFiberBudget

theorem word_recovery_count_bound {m D c c' : ℕ} {U V : List Bool}
    {f : ConnectedColorings m U c → ConnectedColorings m V c'}
    (s : WordRecoverySpec (D:=D) U V c c' f) :
    pathCount m U c ≤ fiberBudget m (U.count true) D*pathCount m V c' := by
  classical
  simpa only [pathCount,positions_card] using
    reconstruction_count_bound s (connectedSource_injective m U c)

theorem word_recovery_real_bound {m D c c' : ℕ} {U V : List Bool}
    {f : ConnectedColorings m U c → ConnectedColorings m V c'}
    (s : WordRecoverySpec (D:=D) U V c c' f) :
    (pathCount m U c : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤ (pathCount m V c' : ℝ) := by
  classical
  simpa only [pathCount,positions_card] using
    reconstruction_real_bound s (connectedSource_injective m U c)

end KroneckerWordRecoveryCount
end

/- Original module: KroneckerTaggedWordCount -/
section
/-! Transfer the compressed tagged decoder to actual connected word counts. -/
set_option autoImplicit false
namespace KroneckerTaggedWordCount
open KroneckerWordCounts KroneckerWordPaletteSplit KroneckerOrientationPositions
open KroneckerTaggedLayout KroneckerTaggedRecoverySpec KroneckerWordRecoveryCount KroneckerFiberBudget



end KroneckerTaggedWordCount
end
end

