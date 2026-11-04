import KroneckerPrescribedCollars
import KroneckerWordPaletteSplit
import KroneckerListInsertion

/- Original module: KroneckerZeroSurplusDeletion -/
section
/-! Drain every surplus produced by one deletion with a fixed prescribed collar path. -/
set_option autoImplicit false
namespace KroneckerZeroSurplusDeletion
open KroneckerStack KroneckerColoring KroneckerWordCounts KroneckerDeletionColoring
open KroneckerVerticalDeletionMap KroneckerCollarColoring KroneckerCollarConnected

noncomputable def zeroDeletion {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (L : List (ℕ×ℕ)) (hL : LegalPairs m L) (hsize : m ≤ L.length)
    (U : List Bool) (i : ℕ) (hi : i < U.length) (hvertical : U[i]=false)
    (g : ConnectedColorings m U 0) :
    ConnectedColorings m (collarPath L (deletionPath u v U i)) 0 := by
  let d := verticalDeletion u v 0 hu hv (by omega) hpos U i hi hvertical g
  refine ⟨collarColoring hm L hL (0+d.1.val) (deletionPath u v U i) d.2.val,?_⟩
  have hz : (0+d.1.val)-L.length=0 := by have := d.1.isLt; omega
  simpa only [hz] using collarColoring_connected hm L hL (0+d.1.val) _ d.2.val d.2.property

theorem zeroDeletion_recover {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (L : List (ℕ×ℕ)) (hL : LegalPairs m L) (hsize : m ≤ L.length)
    (U : List Bool) (i : ℕ) (hi : i < U.length) (hvertical : U[i]=false)
    (g : ConnectedColorings m U 0) :
    KroneckerCollarRecovery.recoverCollar L (deletionPath u v U i)
      (zeroDeletion u v hu hv hm hpos L hL hsize U i hi hvertical g).val=
      (verticalDeletion u v 0 hu hv (by omega) hpos U i hi hvertical g).2.val :=
  KroneckerCollarRecovery.recover_collarColoring hm L hL _ _ _

end KroneckerZeroSurplusDeletion
end

/- Original module: KroneckerDrainedDeletionRecovery -/
section
/-! The actual zero-surplus deletion map retains the same finite recovery code. -/
set_option autoImplicit false
namespace KroneckerDrainedDeletionRecovery
open KroneckerWordCounts KroneckerDeletionColoring KroneckerVerticalDeletionMap
open KroneckerDeletionCode KroneckerDeletionDecoder KroneckerDeletionInjectivity
open KroneckerCollarColoring KroneckerCollarRecovery KroneckerZeroSurplusDeletion

theorem zeroDeletion_decode {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (L : List (ℕ×ℕ)) (hL : LegalPairs m L) (hsize : m ≤ L.length)
    (U : List Bool) (i : ℕ) (hi : i < U.length) (hvertical : U[i]=false)
    (g : ConnectedColorings m U 0) :
    decodeDeletion u v U i
      (recoverCollar L (deletionPath u v U i)
        (zeroDeletion u v hu hv hm hpos L hL hsize U i hi hvertical g).val)
      (deletionCode u v 0 hu hv (by omega) hpos U i hi hvertical g)=List.ofFn g.val := by
  rw [zeroDeletion_recover]
  exact decode_verticalDeletion u v 0 hu hv (by omega) hpos U i hi hvertical g

theorem zeroDeletion_pair_injective {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (L : List (ℕ×ℕ)) (hL : LegalPairs m L) (hsize : m ≤ L.length)
    (U : List Bool) (i : ℕ) (hi : i < U.length) (hvertical : U[i]=false) :
    Function.Injective (fun g : ConnectedColorings m U 0 =>
      (zeroDeletion u v hu hv hm hpos L hL hsize U i hi hvertical g,
        deletionCode u v 0 hu hv (by omega) hpos U i hi hvertical g)) := by
  intro x y h
  apply deletion_data_injective u v 0 hu hv (by omega) hpos U i hi hvertical x y
  · have he := congrArg (fun z : ConnectedColorings m (collarPath L (deletionPath u v U i)) 0 =>
        recoverCollar L (deletionPath u v U i) z.val) (congrArg Prod.fst h)
    simpa only [zeroDeletion_recover] using he
  · exact congrArg Prod.snd h

end KroneckerDrainedDeletionRecovery
end

/- Original module: KroneckerDrainedDeletionCount -/
section
/-! A concrete zero-surplus comparison for one deletion; no structural witness is assumed. -/
set_option autoImplicit false
namespace KroneckerDrainedDeletionCount
open KroneckerWordCounts KroneckerDeletionColoring KroneckerDeletionCode KroneckerDeletionCodeCard
open KroneckerCollarColoring KroneckerZeroSurplusDeletion KroneckerDrainedDeletionRecovery KroneckerFiberBudget

theorem zero_deletion_count_bound {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (L : List (ℕ×ℕ)) (hL : LegalPairs m L) (hsize : m ≤ L.length)
    (U : List Bool) (i : ℕ) (hi : i < U.length) (hvertical : U[i]=false) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) 1*
      pathCount m (collarPath L (deletionPath u v U i)) 0 := by
  classical
  have h := Fintype.card_le_of_injective (fun g : ConnectedColorings m U 0 =>
    (zeroDeletion u v hu hv hm hpos L hL hsize U i hi hvertical g,
      deletionCode u v 0 hu hv (by omega) hpos U i hi hvertical g))
    (zeroDeletion_pair_injective u v hu hv hm hpos L hL hsize U i hi hvertical)
  rw [Fintype.card_prod] at h
  have h' := h.trans (Nat.mul_le_mul_left _ (deletionCode_card_le m U))
  simpa only [pathCount,Nat.card_eq_fintype_card,Nat.mul_comm] using h'

theorem zero_deletion_real_bound {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (L : List (ℕ×ℕ)) (hL : LegalPairs m L) (hsize : m ≤ L.length)
    (U : List Bool) (i : ℕ) (hi : i < U.length) (hvertical : U[i]=false) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) 1 : ℝ) ≤
      (pathCount m (collarPath L (deletionPath u v U i)) 0 : ℝ) := by
  have hp : (0 : ℝ) < fiberBudget m (U.count true) 1 := by
    exact_mod_cast fiberBudget_positive m (U.count true) 1
  apply (div_le_iff₀ hp).mpr
  have h := zero_deletion_count_bound u v hu hv hm hpos L hL hsize U i hi hvertical
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

end KroneckerDrainedDeletionCount
end

/- Original module: KroneckerPrescribedDeletionCount -/
section
/-! Prescribed left and right run collars around an actual one-vertical run deletion. -/
set_option autoImplicit false
namespace KroneckerPrescribedDeletionCount
open KroneckerWordCounts KroneckerRunDeletionPosition KroneckerRunDeletionCount
open KroneckerPrescribedCollars KroneckerDrainedDeletionCount KroneckerOrientationPositions KroneckerFiberBudget

theorem prescribed_deletion_count {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (A B X Y : List ℕ) (r : ℕ)
    (hlen : A.length=B.length) (hsize : m ≤ A.length)
    (hA : ∀ a ∈ A,1 ≤ a ∧ a ≤ m-1) (hB : ∀ b ∈ B,1 ≤ b ∧ b ≤ m-1) :
    runCount m (X++(r+1)::Y) 0 ≤ fiberBudget m (X.length+1+Y.length) 1*
      runCount m (A++(u::(X++r::Y)++[v])++B) 0 := by
  obtain ⟨hi,hvert,_⟩ := runDeletion_data X Y r
  have hz := zero_deletion_count_bound u v hu hv hm hpos (pairCollars A B)
    (pairCollars_legal m A B hA hB) (by simpa [pairCollars_length A B hlen] using hsize)
    (runWord (X++(r+1)::Y)) (runDeletionIndex X r) hi hvert
  rw [deletionPath_runWord,pairCollars_path A B _ hlen] at hz
  simpa [runCount,runWord_horizontal_count,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hz

theorem prescribed_deletion_real {m : ℕ} (u v : ℕ) (hu : u+1 ≤ m) (hv : v-1 ≤ m)
    (hm : 3 ≤ m) (hpos : 1 ≤ v) (A B X Y : List ℕ) (r : ℕ)
    (hlen : A.length=B.length) (hsize : m ≤ A.length)
    (hA : ∀ a ∈ A,1 ≤ a ∧ a ≤ m-1) (hB : ∀ b ∈ B,1 ≤ b ∧ b ≤ m-1) :
    (runCount m (X++(r+1)::Y) 0 : ℝ)/(fiberBudget m (X.length+1+Y.length) 1 : ℝ) ≤
      (runCount m (A++(u::(X++r::Y)++[v])++B) 0 : ℝ) := by
  have hp : (0 : ℝ) < fiberBudget m (X.length+1+Y.length) 1 := by
    exact_mod_cast fiberBudget_positive m (X.length+1+Y.length) 1
  apply (div_le_iff₀ hp).mpr
  have h := prescribed_deletion_count u v hu hv hm hpos A B X Y r hlen hsize hA hB
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

end KroneckerPrescribedDeletionCount
end

/- Original module: KroneckerSingleDeletionComparison -/
section
/-! The prescribed-target comparison for exactly one run-preserving vertical deletion.
This does not assert the general composition proposition or labeled owner identity. -/
set_option autoImplicit false
namespace KroneckerSingleDeletionComparison
open KroneckerWordCounts KroneckerFiberBudget KroneckerPrescribedDeletionCount

theorem one_deletion_prescribed_target {m P u v r : ℕ} (hm : 4 ≤ m)
    (hP : m+1 ≤ P) (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2)
    (hr : 1 ≤ r ∧ r+1 ≤ m-2) (A B X Y : List ℕ)
    (hAlen : A.length=P) (hBlen : B.length=P)
    (hA : ∀ a ∈ A,1 ≤ a ∧ a ≤ m-2) (hB : ∀ b ∈ B,1 ≤ b ∧ b ≤ m-2)
    (hX : ∀ x ∈ X,1 ≤ x ∧ x ≤ m-2) (hY : ∀ y ∈ Y,1 ≤ y ∧ y ≤ m-2) :
    (∀ t ∈ A++(u::(X++r::Y)++[v])++B,1 ≤ t ∧ t ≤ m-2) ∧
    (runCount m (X++(r+1)::Y) 0 : ℝ)/(fiberBudget m (X.length+1+Y.length) 1 : ℝ) ≤
      (runCount m (A++(u::(X++r::Y)++[v])++B) 0 : ℝ) := by
  constructor
  · intro t ht
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with (ha | ((rfl | hx | rfl | hy) | rfl)) | hb
    · exact hA t ha
    · exact hu
    · exact hX t hx
    · exact ⟨hr.1,by omega⟩
    · exact hY t hy
    · exact hv
    · exact hB t hb
  · exact prescribed_deletion_real u v (by omega) (by omega) (by omega) hv.1 A B X Y r
      (by omega) (by omega) (fun a ha => ⟨(hA a ha).1,by have := (hA a ha).2; omega⟩)
      (fun b hb => ⟨(hB b hb).1,by have := (hB b hb).2; omega⟩)

end KroneckerSingleDeletionComparison
end

/- Original module: KroneckerOriginalTags -/
section
/-! Original horizontal and vertical labels are distinct; newly introduced edges carry no label. -/
set_option autoImplicit false
namespace KroneckerOriginalTags
open KroneckerColoring KroneckerInputRecovery

abbrev Tag (n q : ℕ) := Option (Fin n ⊕ Fin q)

def Compatible {n q : ℕ} (b : Bool) : Tag n q → Prop
  | none => True
  | some (.inl _) => b=true
  | some (.inr _) => b=false

def Keeps {m n q : ℕ} (source : Input m n q) (changed : List (Fin n)) :
    Tag n q → Palette m → Prop
  | none,_ => True
  | some (.inl i),x => i ∉ changed → x=source.1 i
  | some (.inr j),x => x=source.2 j

def horizontalRecord {n q : ℕ} : Tag n q → List (Fin n)
  | some (.inl i) => [i]
  | _ => []

def verticalRecord {n q : ℕ} : Tag n q → List (Fin q)
  | some (.inr j) => [j]
  | _ => []

theorem horizontalRecord_length {n q : ℕ} (t : Tag n q) : (horizontalRecord t).length ≤ 1 := by
  cases t with
  | none => simp [horizontalRecord]
  | some t => cases t <;> simp [horizontalRecord]

theorem verticalRecord_length {n q : ℕ} (t : Tag n q) : (verticalRecord t).length ≤ 1 := by
  cases t with
  | none => simp [verticalRecord]
  | some t => cases t <;> simp [verticalRecord]

theorem vertical_tag_ne_horizontal {n q : ℕ} {t : Tag n q} (ht : Compatible false t) (i : Fin n) :
    t≠some (.inl i) := by intro h; subst t; simp [Compatible] at ht

theorem horizontal_tag_ne_vertical {n q : ℕ} {t : Tag n q} (ht : Compatible true t) (j : Fin q) :
    t≠some (.inr j) := by intro h; subst t; simp [Compatible] at ht

end KroneckerOriginalTags
end

/- Original module: KroneckerAlignedLists -/
section
/-! Indexed and pointwise operations on aligned lists. -/
set_option autoImplicit false
namespace KroneckerAlignedLists

theorem rel_getElem {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (i : ℕ) (hx : i < xs.length) (hy : i < ys.length) :
    R xs[i] ys[i] := h.get hx hy

theorem rel_set_right {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (i : ℕ) (hi : i < xs.length) (b : β) (hb : R xs[i] b) :
    List.Forall₂ R xs (ys.set i b) := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons a b' xs ys hab h ih =>
    cases i with
    | zero => exact .cons hb h
    | succ i => exact .cons hab (ih i (by simpa using hi) hb)

theorem rel_ofFn {α β : Type*} {N : ℕ} {R : α → β → Prop} (f : Fin N → α) (g : Fin N → β)
    (h : ∀ i,R (f i) (g i)) : List.Forall₂ R (List.ofFn f) (List.ofFn g) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hi hj
  simpa only [List.get_eq_getElem,List.getElem_ofFn] using h ⟨i,by simpa using hi⟩

end KroneckerAlignedLists
end

/- Original module: KroneckerTagChanges -/
section
/-! Only original horizontal labels need to be logged when a horizontal palette is changed. -/
set_option autoImplicit false
namespace KroneckerTagChanges
open KroneckerOriginalTags KroneckerColoring KroneckerInputRecovery

theorem keeps_mono {m n q : ℕ} {source : Input m n q} {xs ys : List (Fin n)}
    (hsub : ∀ i,i ∈ xs → i ∈ ys) {t : Tag n q} {x : Palette m} (h : Keeps source xs t x) :
    Keeps source ys t x := by
  cases t with
  | none => trivial
  | some t =>
    cases t with
    | inl i => exact fun hi => h (fun hx => hi (hsub i hx))
    | inr j => exact h

theorem keeps_changed {m n q : ℕ} (source : Input m n q) (changed : List (Fin n))
    (t : Tag n q) (ht : Compatible true t) (x : Palette m) :
    Keeps source (horizontalRecord t++changed) t x := by
  cases t with
  | none => trivial
  | some t =>
    cases t with
    | inl i => simp [Keeps,horizontalRecord]
    | inr j => simp [Compatible] at ht

theorem aligned_keeps_mono {m n q : ℕ} {source : Input m n q} {xs ys : List (Fin n)}
    (hsub : ∀ i,i ∈ xs → i ∈ ys) {tags : List (Tag n q)} {cs : List (Palette m)}
    (h : List.Forall₂ (Keeps source xs) tags cs) : List.Forall₂ (Keeps source ys) tags cs := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (keeps_mono hsub ha) ih

end KroneckerTagChanges
end

/- Original module: KroneckerTaggedListEdits -/
section
/-! Exact tag retention and alignment under fixed list insertions and deletions. -/
set_option autoImplicit false
namespace KroneckerTaggedListEdits
open KroneckerListDeletion KroneckerListInsertion

theorem mem_removeAt_of_ne {α : Type*} {a : α} (xs : List α) (i : ℕ) (hi : i < xs.length)
    (ha : a ∈ xs) (hne : a≠xs[i]) : a ∈ removeAt i xs := by
  have hs := split_at xs i hi
  rw [hs,List.mem_append,List.mem_cons] at ha
  rcases ha with hp | he | ht
  · exact List.mem_append_left _ hp
  · exact False.elim (hne he)
  · exact List.mem_append_right _ ht

theorem mem_insertAt {α : Type*} (xs : List α) (i : ℕ) (a b : α) (ha : a ∈ xs) :
    a ∈ insertAt i b xs := by
  have h : a ∈ xs.take i++xs.drop i := by simpa using ha
  rcases List.mem_append.mp h with hp | ht
  · exact List.mem_append_left _ hp
  · exact List.mem_append_right _ (List.mem_cons_of_mem b ht)

theorem rel_removeAt {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (i : ℕ) : List.Forall₂ R (removeAt i xs) (removeAt i ys) :=
  List.rel_append (List.forall₂_take i h) (List.forall₂_drop (i+1) h)

theorem rel_insertAt {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (i : ℕ) (a : α) (b : β) (hab : R a b) :
    List.Forall₂ R (insertAt i a xs) (insertAt i b ys) :=
  List.rel_append (List.forall₂_take i h) (.cons hab (List.forall₂_drop i h))

end KroneckerTaggedListEdits
end
