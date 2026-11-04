import KroneckerRetainedBlockSupport

/- Original module: KroneckerVacantSlotLeaves -/
section
set_option autoImplicit false
namespace KroneckerVacantSlotLeaves
open Module KroneckerReflectionKernel KroneckerProperColoredReflection
attribute [local instance] Classical.propDecidable

theorem source_color_bijective {I J : Type*} [Fintype J] {R : I → J → Prop}
    (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3) (i : I) :
    Function.Bijective (fun j : {j // R i j} => C.color i j j.2) := by
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨C.at_source i,by simpa using h3 i⟩

noncomputable def neighborAt {I J : Type*} [Fintype J] {R : I → J → Prop}
    (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3) (i : I) (d : Fin 3) :
    {j // R i j} := (Equiv.ofBijective _ (source_color_bijective C h3 i)).symm d

theorem neighborAt_color {I J : Type*} [Fintype J] {R : I → J → Prop}
    (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3) (i : I) (d : Fin 3) :
    C.color i (neighborAt C h3 i d) (neighborAt C h3 i d).2=d :=
  (Equiv.ofBijective _ (source_color_bijective C h3 i)).apply_symm_apply d

def Vacant {I J : Type*} [Fintype I] {R : I → J → Prop}
    (C : ProperColoring R) (i : I) (d : Fin 3) : Prop :=
  ¬∃ j,∃ h : R i j,C.color i j h=d ∧ 0<finrank ℂ (Kernel {k // R k j})

theorem vacant_iff_leaf {I J : Type*} [Fintype I] [Fintype J] {R : I → J → Prop}
    (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3) (i : I) (d : Fin 3) :
    Vacant C i d ↔ Fintype.card {k // R k (neighborAt C h3 i d)}=1 := by
  let j := neighborAt C h3 i d
  have hp : 0<Fintype.card {k // R k j} := by
    haveI : Nonempty {k // R k j} := ⟨⟨i,j.2⟩⟩
    exact Fintype.card_pos
  rw [←reflected_zero_iff_leaf R j hp]
  constructor
  · intro h
    by_contra hz
    exact h ⟨j,j.2,neighborAt_color C h3 i d,Nat.pos_of_ne_zero hz⟩
  · intro hz
    rintro ⟨k,hik,hcol,hpos⟩
    have hk : (⟨k,hik⟩ : {j // R i j})=j :=
      C.at_source i (hcol.trans (neighborAt_color C h3 i d).symm)
    have he : k=j := congrArg Subtype.val hk
    subst k
    omega

theorem vacant_leaf_unique_source {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (i : I) (d : Fin 3) (hv : Vacant C i d)
    (k : I) (hk : R k (neighborAt C h3 i d)) : k=i := by
  have hcard := (vacant_iff_leaf C h3 i d).mp hv
  haveI : Subsingleton {k // R k (neighborAt C h3 i d)} :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨k,hk⟩ : {k // R k (neighborAt C h3 i d)}) ⟨i,(neighborAt C h3 i d).2⟩)

noncomputable def slotLeaf {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R)
    (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (p : {p : I × Fin 3 // Vacant C p.1 p.2}) : {j : J // Fintype.card {i // R i j}=1} :=
  ⟨neighborAt C h3 p.1.1 p.1.2,(vacant_iff_leaf C h3 _ _).mp p.2⟩

theorem slotLeaf_bijective {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) : Function.Bijective (slotLeaf C h3) := by
  constructor
  · intro p q h
    have hj : (neighborAt C h3 p.1.1 p.1.2).1=(neighborAt C h3 q.1.1 q.1.2).1 :=
      congrArg Subtype.val h
    have hi : q.1.1=p.1.1 := vacant_leaf_unique_source C h3 _ _ p.2 q.1.1
      (by rw [hj]; exact (neighborAt C h3 q.1.1 q.1.2).2)
    apply Subtype.ext
    apply Prod.ext hi.symm
    have hc := neighborAt_color C h3 p.1.1 p.1.2
    have hd := neighborAt_color C h3 q.1.1 q.1.2
    rw [←hc,←hd]
    congr 1
    exact hi.symm
  · intro j
    haveI : Nonempty {i // R i j} := Fintype.card_pos_iff.mp (by rw [j.2]; omega)
    let i : {i // R i j} := Classical.arbitrary _
    let d := C.color i j i.2
    have hj : neighborAt C h3 i d=(⟨j,i.2⟩ : {j // R i j}) :=
      C.at_source i (neighborAt_color C h3 i d)
    have hv : Vacant C i d := (vacant_iff_leaf C h3 i d).mpr (by simpa [hj] using j.2)
    refine ⟨⟨(i,d),hv⟩,?_⟩
    apply Subtype.ext
    change (neighborAt C h3 i d).1=j.1
    exact congrArg Subtype.val hj

noncomputable def vacantLeafEquiv {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) :
    {p : I × Fin 3 // Vacant C p.1 p.2} ≃ {j : J // Fintype.card {i // R i j}=1} :=
  Equiv.ofBijective _ (slotLeaf_bijective C h3)

end KroneckerVacantSlotLeaves
end

/- Original module: KroneckerRetainedVacantSlots -/
section
set_option autoImplicit false
namespace KroneckerRetainedVacantSlots
open Module KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerRetainedReflectionKernels KroneckerProperColoredReflection
open KroneckerVacantSlotLeaves
attribute [local instance] Classical.propDecidable

def VacantSlot (B : LinearCoverBlock) (C : ProperColoring (linearSupport B))
    (i : B.Sink) (d : Fin 3) : Prop := ¬∃ s,∃ h : linearSupport B s i,C.color s i h=d

abbrev Slot (B : LinearCoverBlock) (C : ProperColoring (linearSupport B)) :=
  {p : B.Sink × Fin 3 // VacantSlot B C p.1 p.2}

theorem retained_vacant_iff {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (i : I) (d : Fin 3) :
    VacantSlot (retainedBlock R) (retainedColoring C) i d ↔ Vacant C i d := by
  constructor
  · intro h
    rintro ⟨j,hij,hcolor,hpos⟩
    let jr : Retained R := ⟨j,(retained_iff_kernel_positive R j).mpr hpos⟩
    have hs : linearSupport (retainedBlock R) jr i := (retained_support_iff R jr i).mpr hij
    exact h ⟨jr,hs,hcolor⟩
  · intro h
    rintro ⟨j,hij,hcolor⟩
    exact h ⟨j.1,(retained_support_iff R j i).mp hij,hcolor,
      (retained_iff_kernel_positive R j.1).mp j.2⟩

def actualSlotEquiv {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) :
    Slot (retainedBlock R) (retainedColoring C) ≃ {p : I × Fin 3 // Vacant C p.1 p.2} where
  toFun p := ⟨p.1,(retained_vacant_iff C _ _).mp p.2⟩
  invFun p := ⟨p.1,(retained_vacant_iff C _ _).mpr p.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

noncomputable def actualSlotLeafEquiv {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) :
    Slot (retainedBlock R) (retainedColoring C) ≃ {j : J // Fintype.card {i // R i j}=1} :=
  (actualSlotEquiv C).trans (vacantLeafEquiv C h3)

theorem actual_slot_leaf_value {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (p : Slot (retainedBlock R) (retainedColoring C)) :
    (actualSlotLeafEquiv C h3 p).1=(neighborAt C h3 p.1.1 p.1.2).1 := rfl

theorem actual_slot_leaf_incidence {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (p : Slot (retainedBlock R) (retainedColoring C)) (i : I) :
    R i (actualSlotLeafEquiv C h3 p).1 ↔ i=p.1.1 := by
  rw [actual_slot_leaf_value]
  constructor
  · exact vacant_leaf_unique_source C h3 _ _ ((retained_vacant_iff C _ _).mp p.2) i
  · intro h
    subst i
    exact (neighborAt C h3 p.1.1 p.1.2).2

theorem actual_slot_leaf_color {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (p : Slot (retainedBlock R) (retainedColoring C))
    (h : R p.1.1 (actualSlotLeafEquiv C h3 p).1) :
    C.color p.1.1 (actualSlotLeafEquiv C h3 p).1 h=p.1.2 :=
  neighborAt_color C h3 p.1.1 p.1.2

noncomputable def leafNeighbor {I J : Type} [Fintype I] {R : I → J → Prop}
    (j : {j : J // Fintype.card {i // R i j}=1}) : {i // R i j.1} :=
  Classical.choice (Fintype.card_pos_iff.mp (by rw [j.2]; omega))

noncomputable def leafColor {I J : Type} [Fintype I] {R : I → J → Prop}
    (C : ProperColoring R) (j : {j : J // Fintype.card {i // R i j}=1}) : Fin 3 :=
  C.color (leafNeighbor j).1 j.1 (leafNeighbor j).2

theorem actual_slot_leaf_preserves_color {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (p : Slot (retainedBlock R) (retainedColoring C)) :
    leafColor C (actualSlotLeafEquiv C h3 p)=p.1.2 := by
  have hi := (actual_slot_leaf_incidence C h3 p _).mp (leafNeighbor (actualSlotLeafEquiv C h3 p)).2
  unfold leafColor
  have hp := actual_slot_leaf_color C h3 p ((actual_slot_leaf_incidence C h3 p _).mpr rfl)
  simpa only [hi] using hp

noncomputable def coloredSlotLeafEquiv {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3) (d : Fin 3) :
    {p : Slot (retainedBlock R) (retainedColoring C) // p.1.2=d} ≃
      {j : {j : J // Fintype.card {i // R i j}=1} // leafColor C j=d} :=
  Equiv.subtypeEquiv (actualSlotLeafEquiv C h3) (fun p => by rw [actual_slot_leaf_preserves_color])

end KroneckerRetainedVacantSlots
end
