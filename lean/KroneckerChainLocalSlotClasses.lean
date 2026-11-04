import KroneckerReflectedPairSlotCounts
import KroneckerChainBlockNeighbors
import KroneckerActualSlotGluing

/- Original module: KroneckerAssignedSlotObjects -/
section
set_option autoImplicit false
namespace KroneckerAssignedSlotObjects
open KroneckerFiniteColoredTables KroneckerSaturatedTableAction KroneckerReflectedSingleSlotCounts
open KroneckerRetainedBlockSupport KroneckerSlotIsoTransport KroneckerColoredIncidenceIso
open KroneckerRetainedReflectionKernels
attribute [local instance] Classical.propDecidable

variable (I J A : Type) [Fintype I] [Fintype J]

/-- Slots are indexed by the actual incident connectors; injectivity keeps
ordered marks distinct even when their prescribed colors agree. -/
abbrev AssignedObject (κ : A → Fin 3) :=
  Σ T : SaturatedTable I J,
    {s : A → ReflectedSlot T // Function.Injective s ∧ ∀ a,(s a).1.2=κ a}

def assignedSetoid (κ : A → Fin 3) : Setoid (AssignedObject I J A κ) where
  r M N := ∃ e : ColoredIso (retainedColoring (coloring M.1.1))
      (retainedColoring (coloring N.1.1)),∀ a,slotEquiv e (M.2.1 a)=N.2.1 a
  iseqv := by
    constructor
    · intro M; exact ⟨1,fun _ => rfl⟩
    · rintro M N ⟨e,he⟩
      refine ⟨e.symm,?_⟩
      intro a
      rw [←he a]
      apply Subtype.ext
      exact Prod.ext (e.sink.symm_apply_apply _) rfl
    · rintro M N P ⟨e,he⟩ ⟨f,hf⟩
      refine ⟨e.trans f,?_⟩
      intro a
      change slotEquiv f (slotEquiv e (M.2.1 a))=P.2.1 a
      rw [he a,hf a]

abbrev AssignedClass (κ : A → Fin 3) := Quotient (assignedSetoid I J A κ)

noncomputable instance [Fintype A] (κ : A → Fin 3) : Fintype (AssignedClass I J A κ) := Fintype.ofFinite _

variable {I J A}

theorem assigned_class_eq_iff (κ : A → Fin 3) (M N : AssignedObject I J A κ) :
    (Quotient.mk _ M : AssignedClass I J A κ)=Quotient.mk _ N ↔
      ∃ e : ColoredIso (retainedColoring (coloring M.1.1))
        (retainedColoring (coloring N.1.1)),∀ a,slotEquiv e (M.2.1 a)=N.2.1 a :=
  Quotient.eq

noncomputable def reindexObject {A' : Type} (e : A ≃ A')
    (κ : A' → Fin 3) : AssignedObject I J A (κ ∘ e) ≃ AssignedObject I J A' κ where
  toFun M := ⟨M.1,fun a => M.2.1 (e.symm a),M.2.2.1.comp e.symm.injective,
    fun a => by simpa using M.2.2.2 (e.symm a)⟩
  invFun M := ⟨M.1,M.2.1 ∘ e,M.2.2.1.comp e.injective,fun a => M.2.2.2 (e a)⟩
  left_inv M := by
    rcases M with ⟨T,s,hs,hc⟩
    apply congrArg (fun q => (⟨T,q⟩ : AssignedObject I J A (κ ∘ e)))
    apply Subtype.ext
    funext a
    exact congrArg s (e.symm_apply_apply a)
  right_inv M := by
    rcases M with ⟨T,s,hs,hc⟩
    apply congrArg (fun q => (⟨T,q⟩ : AssignedObject I J A' κ))
    apply Subtype.ext
    funext a
    exact congrArg s (e.apply_symm_apply a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem reindex_relation {A' : Type} (e : A ≃ A') (κ : A' → Fin 3)
    (M N : AssignedObject I J A (κ ∘ e)) :
    assignedSetoid I J A (κ ∘ e) M N ↔ assignedSetoid I J A' κ
      (reindexObject e κ M) (reindexObject e κ N) := by
  constructor
  · rintro ⟨f,hf⟩; exact ⟨f,fun a => hf (e.symm a)⟩
  · rintro ⟨f,hf⟩
    exact ⟨f,fun a => by simpa [reindexObject] using hf (e a)⟩

end KroneckerAssignedSlotObjects
end

/- Original module: KroneckerAssignedPairSlots -/
section
set_option autoImplicit false
namespace KroneckerAssignedPairSlots
open KroneckerAssignedSlotObjects KroneckerReflectedPairSlotCounts
attribute [local instance] Classical.propDecidable
variable {I J : Type} [Fintype I] [Fintype J]

def pairColors (d e : Fin 3) : Bool → Fin 3 := fun b => if b then e else d

noncomputable def boolSlotEquiv (d e : Fin 3) :
    AssignedObject I J Bool (pairColors d e) ≃ PairSlotObject I J d e where
  toFun M := ⟨M.1,(M.2.1 false,M.2.1 true),M.2.2.2 false,M.2.2.2 true,
    fun h => Bool.false_ne_true (M.2.2.1 h)⟩
  invFun M := ⟨M.1,fun b => if b then M.2.1.2 else M.2.1.1,by
      intro b c h
      cases b <;> cases c <;> simp_all
      · exact M.2.2.2.2 h
      · exact M.2.2.2.2 h.symm,
    by
      intro b
      cases b
      · exact M.2.2.1
      · exact M.2.2.2.1⟩
  left_inv M := by
    rcases M with ⟨T,s,hs,hc⟩
    apply congrArg (fun q => (⟨T,q⟩ : AssignedObject I J Bool (pairColors d e)))
    apply Subtype.ext
    funext b
    cases b <;> rfl
  right_inv M := rfl

theorem bool_slot_relation (d e : Fin 3) (M N : AssignedObject I J Bool (pairColors d e)) :
    assignedSetoid I J Bool (pairColors d e) M N ↔
      pairSlotSetoid I J d e (boolSlotEquiv d e M) (boolSlotEquiv d e N) := by
  constructor
  · rintro ⟨f,hf⟩; exact ⟨f,hf false,hf true⟩
  · rintro ⟨f,h0,h1⟩
    exact ⟨f,fun b => by cases b; exact h0; exact h1⟩

noncomputable def boolSlotClassEquiv (d e : Fin 3) :
    AssignedClass I J Bool (pairColors d e) ≃ PairSlotClass I J d e :=
  Quotient.congr (boolSlotEquiv d e) (bool_slot_relation d e)

theorem bool_slot_class_card (d e : Fin 3) :
    Fintype.card (AssignedClass I J Bool (pairColors d e))=Fintype.card (PairSlotClass I J d e) := by
  simp only [←Nat.card_eq_fintype_card]
  exact Nat.card_congr (boolSlotClassEquiv d e)

end KroneckerAssignedPairSlots
end

/- Original module: KroneckerAssignedSingleSlots -/
section
set_option autoImplicit false
namespace KroneckerAssignedSingleSlots
open KroneckerAssignedSlotObjects KroneckerReflectedSingleSlotCounts
attribute [local instance] Classical.propDecidable
variable {I J : Type} [Fintype I] [Fintype J]

noncomputable def unitSlotEquiv (d : Fin 3) :
    AssignedObject I J Unit (fun _ => d) ≃ SingleSlotObject I J d where
  toFun M := ⟨M.1,M.2.1 (),M.2.2.2 ()⟩
  invFun M := ⟨M.1,fun _ => M.2.1,fun _ _ _ => Subsingleton.elim _ _,fun _ => M.2.2⟩
  left_inv M := by
    rcases M with ⟨T,s,hs,hc⟩
    apply congrArg (fun q => (⟨T,q⟩ : AssignedObject I J Unit (fun _ => d)))
    apply Subtype.ext
    funext u
    cases u
    rfl
  right_inv M := rfl

theorem unit_slot_relation (d : Fin 3) (M N : AssignedObject I J Unit (fun _ => d)) :
    assignedSetoid I J Unit (fun _ => d) M N ↔
      singleSlotSetoid I J d (unitSlotEquiv d M) (unitSlotEquiv d N) := by
  constructor
  · rintro ⟨e,he⟩; exact ⟨e,he ()⟩
  · rintro ⟨e,he⟩; exact ⟨e,fun u => by cases u; exact he⟩

noncomputable def unitSlotClassEquiv (d : Fin 3) :
    AssignedClass I J Unit (fun _ => d) ≃ SingleSlotClass I J d :=
  Quotient.congr (unitSlotEquiv d) (unit_slot_relation d)

theorem unit_slot_class_card (d : Fin 3) :
    Fintype.card (AssignedClass I J Unit (fun _ => d))=Fintype.card (SingleSlotClass I J d) := by
  simp only [←Nat.card_eq_fintype_card]
  exact Nat.card_congr (unitSlotClassEquiv d)

end KroneckerAssignedSingleSlots
end

/- Original module: KroneckerAssignedClassReindexing -/
section
set_option autoImplicit false
namespace KroneckerAssignedClassReindexing
open KroneckerAssignedSlotObjects KroneckerAssignedSingleSlots KroneckerAssignedPairSlots
open KroneckerReflectedSingleSlotCounts KroneckerReflectedPairSlotCounts
variable {I J A A' : Type} [Fintype I] [Fintype J]

noncomputable def reindexClass (e : A ≃ A') (κ : A' → Fin 3) :
    AssignedClass I J A (κ ∘ e) ≃ AssignedClass I J A' κ :=
  Quotient.congr (reindexObject e κ) (reindex_relation e κ)

noncomputable def singletonClassEquiv (e : Unit ≃ A) (κ : A → Fin 3) :
    AssignedClass I J A κ ≃ SingleSlotClass I J (κ (e ())) := by
  have hc : κ ∘ e=(fun _ : Unit => κ (e ())) := by funext u; cases u; rfl
  refine (reindexClass e κ).symm.trans ?_
  rw [hc]
  exact unitSlotClassEquiv _

noncomputable def doubleClassEquiv (e : Bool ≃ A) (κ : A → Fin 3) :
    AssignedClass I J A κ ≃ PairSlotClass I J (κ (e false)) (κ (e true)) := by
  have hc : κ ∘ e=pairColors (κ (e false)) (κ (e true)) := by
    funext b; cases b <;> rfl
  refine (reindexClass e κ).symm.trans ?_
  rw [hc]
  exact boolSlotClassEquiv _ _

theorem singleton_class_card [Fintype A] (e : Unit ≃ A) (κ : A → Fin 3) :
    Fintype.card (AssignedClass I J A κ)=Fintype.card (SingleSlotClass I J (κ (e ()))) := by
  simp only [←Nat.card_eq_fintype_card]
  exact Nat.card_congr (singletonClassEquiv e κ)

theorem double_class_card [Fintype A] (e : Bool ≃ A) (κ : A → Fin 3) :
    Fintype.card (AssignedClass I J A κ)=
      Fintype.card (PairSlotClass I J (κ (e false)) (κ (e true))) := by
  simp only [←Nat.card_eq_fintype_card]
  exact Nat.card_congr (doubleClassEquiv e κ)

end KroneckerAssignedClassReindexing
end

/- Original module: KroneckerChainPortColors -/
section
set_option autoImplicit false
namespace KroneckerChainPortColors
open KroneckerChainIncidence
attribute [local instance] Classical.propDecidable

abbrev ColorChoices (n : ℕ) := Connector n → Equiv.Perm (Fin 3)

noncomputable def prescribed {n : ℕ} (σ : ColorChoices n) (i : Connector n)
    (j : Block n) (h : incidence i j) : Fin 3 :=
  σ i ((portEquiv i).symm ⟨j,h⟩)

theorem prescribed_injective {n : ℕ} (σ : ColorChoices n) (i : Connector n) :
    Function.Injective (fun j : {j // incidence i j} => prescribed σ i j.1 j.2) :=
  (σ i).injective.comp (portEquiv i).symm.injective

theorem prescribed_at_port {n : ℕ} (σ : ColorChoices n) (i : Connector n) (p : Fin 3) :
    prescribed σ i (portBlock i p) (port_incident i p)=σ i p := by
  change σ i ((portEquiv i).symm ((portEquiv i) p))=σ i p
  rw [Equiv.symm_apply_apply]

theorem port_colors_recover_permutations {n : ℕ} (σ τ : ColorChoices n)
    (h : ∀ i j (hij : incidence i j),prescribed σ i j hij=prescribed τ i j hij) : σ=τ := by
  funext i
  apply Equiv.ext
  intro p
  simpa only [prescribed_at_port] using h i (portBlock i p) (port_incident i p)

theorem independent_color_count (n : ℕ) : Fintype.card (ColorChoices n)=6^(n+1) := by
  simp [ColorChoices,Connector,Fintype.card_perm]
  norm_num

end KroneckerChainPortColors
end

/- Original module: KroneckerChainNeighborIndices -/
section
set_option autoImplicit false
namespace KroneckerChainNeighborIndices
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainPortColors
attribute [local instance] Classical.propDecidable

abbrev Neighbors {n : ℕ} (j : Block n) := {i // incidence i j}

def uniqueNeighborEquiv {n : ℕ} (j : Block n) (k : Connector n)
    (h : ∀ i,incidence i j ↔ i=k) : Unit ≃ Neighbors j where
  toFun _ := ⟨k,(h k).mpr rfl⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := Subtype.ext ((h i).mp i.2).symm

def leftNeighbors (n : ℕ) : Unit ≃ Neighbors (leftBlock n) :=
  uniqueNeighborEquiv _ 0 left_incidence

def rightNeighbors (n : ℕ) : Unit ≃ Neighbors (rightBlock n) :=
  uniqueNeighborEquiv _ (Fin.last n) right_incidence

def middleNeighbors {n : ℕ} (t : Connector n) : Unit ≃ Neighbors (middleBlock t) :=
  uniqueNeighborEquiv _ t (fun i => middle_incidence i t)

noncomputable def internalNeighbors {n : ℕ} (t : Fin n) : Bool ≃ Neighbors (internalBlock t) :=
  Equiv.ofBijective (fun b =>
    ⟨if b then t.succ else t.castSucc,by cases b <;> simp [internal_incidence]⟩) (by
    have hn : t.castSucc≠t.succ := by intro h; have hv := congrArg Fin.val h; simp at hv
    constructor
    · intro b c h
      have hv := congrArg Subtype.val h
      cases b <;> cases c <;> simp_all
    · intro i
      rcases (internal_incidence i t).mp i.2 with h|h
      · exact ⟨false,Subtype.ext h.symm⟩
      · exact ⟨true,Subtype.ext h.symm⟩)

noncomputable def neighborColors {n : ℕ} (σ : ColorChoices n) (j : Block n)
    (i : Neighbors j) : Fin 3 := prescribed σ i.1 j i.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem leaf_neighbor_colors {n : ℕ} (σ : ColorChoices n) (t : Connector n) :
    neighborColors σ (leftBlock n) (leftNeighbors n ())=σ 0 0 ∧
    neighborColors σ (rightBlock n) (rightNeighbors n ())=σ (Fin.last n) 2 ∧
    neighborColors σ (middleBlock t) (middleNeighbors t ())=σ t 1 := by
  constructor
  · simpa [neighborColors,leftNeighbors,uniqueNeighborEquiv,leftBlock,portBlock]
      using prescribed_at_port σ 0 0
  constructor
  · simpa [neighborColors,rightNeighbors,uniqueNeighborEquiv,rightBlock,portBlock]
      using prescribed_at_port σ (Fin.last n) 2
  · simpa [neighborColors,middleNeighbors,uniqueNeighborEquiv,middleBlock,portBlock]
      using prescribed_at_port σ t 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem internal_neighbor_colors {n : ℕ} (σ : ColorChoices n) (t : Fin n) :
    neighborColors σ (internalBlock t) (internalNeighbors t false)=σ t.castSucc 2 ∧
    neighborColors σ (internalBlock t) (internalNeighbors t true)=σ t.succ 0 := by
  constructor
  · simpa [neighborColors,internalNeighbors,internalBlock,portBlock]
      using prescribed_at_port σ t.castSucc 2
  · change prescribed σ t.succ (internalBlock t) _=σ t.succ 0
    have hp : portBlock t.succ 0=internalBlock t := by
      simp only [portBlock,ite_true]
      rfl
    have he := prescribed_at_port σ t.succ 0
    simpa only [hp] using he

end KroneckerChainNeighborIndices
end

/- Original module: KroneckerChainSlotAssignments -/
section
set_option autoImplicit false
namespace KroneckerChainSlotAssignments
open KroneckerChainIncidence KroneckerChainPortColors KroneckerChainNeighborIndices
open KroneckerAssignedSlotObjects KroneckerFiniteColoredTables KroneckerRetainedReflectionKernels
open KroneckerRetainedBlockSupport KroneckerActualSlotGluing KroneckerLinearCoverBlocks
open KroneckerProperColoredReflection
attribute [local instance] Classical.propDecidable

abbrev LocalObject {n : ℕ} (d : Block n → ℕ) (σ : ColorChoices n) (j : Block n) :=
  AssignedObject (Fin (d j+1)) (Fin (2*(d j+1)+1)) (Neighbors j) (neighborColors σ j)

abbrev RepresentativeFamily {n : ℕ} (d : Block n → ℕ) (σ : ColorChoices n) :=
  ∀ j,LocalObject d σ j

noncomputable def familyBlock {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (j : Block n) : LinearCoverBlock :=
  retainedBlock (Incidence (M j).1.1)

noncomputable def familyColoring {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (j : Block n) : ProperColoring (linearSupport (familyBlock M j)) :=
  retainedColoring (coloring (M j).1.1)

/-- Independent marked block representatives produce actual vacant-slot
attachments. Local ordered-pair injectivity and connector color permutations
supply the two different properness conditions. -/
noncomputable def familyAssignment {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) : SlotAssignment (familyBlock M) incidence (familyColoring M) where
  slot := fun i j h => (M j).2.1 ⟨i,h⟩
  distinctAtBlock := fun j => (M j).2.2.1
  distinctAtConnector := by
    intro i j k h
    apply prescribed_injective σ i
    change prescribed σ i j.1 j.2=prescribed σ i k.1 k.2
    exact ((M j.1).2.2.2 ⟨i,j.2⟩).symm.trans (h.trans ((M k.1).2.2.2 ⟨i,k.2⟩))

theorem assignment_uses_prescribed_colors {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (M : RepresentativeFamily d σ) (i : Connector n) (j : Block n) (h : incidence i j) :
    ((familyAssignment M).slot i j h).1.2=prescribed σ i j h := (M j).2.2.2 ⟨i,h⟩

theorem assignment_recovers_color_choices {n : ℕ} {d : Block n → ℕ} {σ τ : ColorChoices n}
    (M : RepresentativeFamily d σ) (N : RepresentativeFamily d τ)
    (h : ∀ i j (hij : incidence i j),((familyAssignment M).slot i j hij).1.2=
      ((familyAssignment N).slot i j hij).1.2) : σ=τ := by
  apply port_colors_recover_permutations
  intro i j hij
  simpa only [assignment_uses_prescribed_colors] using h i j hij

end KroneckerChainSlotAssignments
end

/- Original module: KroneckerChainLocalSlotClasses -/
section
set_option autoImplicit false
namespace KroneckerChainLocalSlotClasses
open KroneckerChainIncidence KroneckerChainBlockNeighbors KroneckerChainPortColors
open KroneckerChainNeighborIndices KroneckerAssignedSlotObjects KroneckerAssignedClassReindexing
open KroneckerReflectedSingleSlotCounts KroneckerReflectedPairSlotCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev LocalClass {n : ℕ} (d : Block n → ℕ) (σ : ColorChoices n) (j : Block n) :=
  AssignedClass (Fin (d j+1)) (Fin (2*(d j+1)+1)) (Neighbors j) (neighborColors σ j)

abbrev FamilyClass {n : ℕ} (d : Block n → ℕ) (σ : ColorChoices n) := ∀ j,LocalClass d σ j

theorem leaf_local_class_card {n : ℕ} (d : Block n → ℕ) (σ : ColorChoices n)
    (j : Block n) (k : Connector n) (hj : ∀ i,incidence i j ↔ i=k) :
    Fintype.card (LocalClass d σ j)=Fintype.card
      (SingleSlotClass (Fin (d j+1)) (Fin (2*(d j+1)+1)) (prescribed σ k j ((hj k).mpr rfl))) := by
  exact singleton_class_card (uniqueNeighborEquiv j k hj) (neighborColors σ j)

theorem internal_local_class_card {n : ℕ} (d : Block n → ℕ) (σ : ColorChoices n) (t : Fin n) :
    Fintype.card (LocalClass d σ (internalBlock t))=Fintype.card
      (PairSlotClass (Fin (d (internalBlock t)+1)) (Fin (2*(d (internalBlock t)+1)+1))
        (σ t.castSucc 2) (σ t.succ 0)) := by
  have hc := double_class_card (I:=Fin (d (internalBlock t)+1))
    (J:=Fin (2*(d (internalBlock t)+1)+1)) (internalNeighbors t) (neighborColors σ (internalBlock t))
  rw [(internal_neighbor_colors σ t).1,(internal_neighbor_colors σ t).2] at hc
  exact hc

theorem family_class_card {n : ℕ} (d : Block n → ℕ) (σ : ColorChoices n) :
    Fintype.card (FamilyClass d σ)=∏ j,Fintype.card (LocalClass d σ j) := Fintype.card_pi

end KroneckerChainLocalSlotClasses
end
