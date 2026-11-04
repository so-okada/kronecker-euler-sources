import KroneckerTableLeafMarks

/- Original module: KroneckerMarkedSlotPairs -/
section
set_option autoImplicit false
namespace KroneckerMarkedSlotPairs
open KroneckerProperColoredReflection KroneckerRetainedVacantSlots
open KroneckerRetainedReflectionKernels KroneckerRetainedBlockSupport
attribute [local instance] Classical.propDecidable

abbrev OrderedMarks {A : Type*} (color : A → Fin 3) (d e : Fin 3) :=
  {p : A × A // color p.1=d ∧ color p.2=e ∧ p.1≠p.2}

def marksEquiv {A B : Type*} {c : A → Fin 3} {c' : B → Fin 3}
    (f : A ≃ B) (hc : ∀ a,c' (f a)=c a) (d e : Fin 3) :
    OrderedMarks c d e ≃ OrderedMarks c' d e :=
  Equiv.subtypeEquiv (Equiv.prodCongr f f) (by intro p; simp [hc,f.injective.ne_iff])

def distinctColorProduct {A : Type*} (c : A → Fin 3) {d e : Fin 3} (hde : d≠e) :
    OrderedMarks c d e ≃ {a // c a=d} × {a // c a=e} where
  toFun p := (⟨p.1.1,p.2.1⟩,⟨p.1.2,p.2.2.1⟩)
  invFun p := ⟨(p.1.1,p.2.1),p.1.2,p.2.2,by
    intro h
    exact hde (p.1.2.symm.trans ((congrArg c h).trans p.2.2))⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

def equalColorSigma {A : Type*} (c : A → Fin 3) (d : Fin 3) :
    OrderedMarks c d d ≃ (Σ a : {a // c a=d},{b : {b // c b=d} // b≠a}) where
  toFun p := ⟨⟨p.1.1,p.2.1⟩,⟨⟨p.1.2,p.2.2.1⟩,by
    intro h; exact p.2.2.2 (congrArg Subtype.val h).symm⟩⟩
  invFun p := ⟨(p.1.1,p.2.1.1),p.1.2,p.2.1.2,by
    intro h; exact p.2.2 (Subtype.ext h.symm)⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

theorem distinct_color_count {A : Type*} [Fintype A] (c : A → Fin 3)
    {d e : Fin 3} (hde : d≠e) : Fintype.card (OrderedMarks c d e)=
      Fintype.card {a // c a=d}*Fintype.card {a // c a=e} := by
  rw [Fintype.card_congr (distinctColorProduct c hde),Fintype.card_prod]

theorem equal_color_count {A : Type*} [Fintype A] (c : A → Fin 3) (d : Fin 3) :
    Fintype.card (OrderedMarks c d d)=
      Fintype.card {a // c a=d}*(Fintype.card {a // c a=d}-1) := by
  classical
  rw [Fintype.card_congr (equalColorSigma c d),Fintype.card_sigma]
  simp [Fintype.card_subtype_compl]

/-- The actual ordered, distinct, color-prescribed slot marks correspond to
the same ordered leaf marks, including the repeated-color case. -/
noncomputable def markedSlotLeafEquiv {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (C : ProperColoring R) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (d e : Fin 3) :
    OrderedMarks (fun p : Slot (retainedBlock R) (retainedColoring C) => p.1.2) d e ≃
      OrderedMarks (leafColor C) d e :=
  marksEquiv (actualSlotLeafEquiv C h3) (actual_slot_leaf_preserves_color C h3) d e

end KroneckerMarkedSlotPairs
end

/- Original module: KroneckerTablePairMarks -/
section
set_option autoImplicit false
namespace KroneckerTablePairMarks
open KroneckerFiniteColoredTables KroneckerTableLeafMarks KroneckerRetainedVacantSlots
open KroneckerMarkedSlotPairs KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I]

def PairMark (T : ColoredTable I J) (d e : Fin 3) (p : J × J) : Prop :=
  LeafMark T d p.1 ∧ LeafMark T e p.2 ∧ p.1≠p.2

noncomputable def pairMarkEquiv (T : ColoredTable I J) (d e : Fin 3) :
    {p // PairMark T d e p} ≃ OrderedMarks (leafColor (coloring T)) d e where
  toFun p := ⟨((leafMarkEquiv T d ⟨p.1.1,p.2.1⟩).1,
      (leafMarkEquiv T e ⟨p.1.2,p.2.2.1⟩).1),
    (leafMarkEquiv T d ⟨p.1.1,p.2.1⟩).2,(leafMarkEquiv T e ⟨p.1.2,p.2.2.1⟩).2,
    fun h => p.2.2.2 (congrArg Subtype.val h)⟩
  invFun p := ⟨(p.1.1.1,p.1.2.1),
    ((leafMarkEquiv T d).symm ⟨p.1.1,p.2.1⟩).2,
    ((leafMarkEquiv T e).symm ⟨p.1.2,p.2.2.1⟩).2,fun h => p.2.2.2 (Subtype.ext h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem equal_color_pair_count [Fintype J] (T : ColoredTable I J) (d : Fin 3) :
    Fintype.card {p // PairMark T d d p}=
      Fintype.card {j // LeafMark T d j}*(Fintype.card {j // LeafMark T d j}-1) := by
  have h := equal_color_count (leafColor (coloring T)) d
  simp only [←Nat.card_eq_fintype_card] at h ⊢
  rw [Nat.card_congr (pairMarkEquiv T d d),h,←Nat.card_congr (leafMarkEquiv T d)]

theorem distinct_color_pair_count [Fintype J] (T : ColoredTable I J) {d e : Fin 3} (hde : d≠e) :
    Fintype.card {p // PairMark T d e p}=
      Fintype.card {j // LeafMark T d j}*Fintype.card {j // LeafMark T e j} := by
  have h := distinct_color_count (leafColor (coloring T)) hde
  simp only [←Nat.card_eq_fintype_card] at h ⊢
  rw [Nat.card_congr (pairMarkEquiv T d e),h,
    ←Nat.card_congr (leafMarkEquiv T d),←Nat.card_congr (leafMarkEquiv T e)]

theorem pair_mark_transport {I' J' : Type} [Fintype I']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (f : ColoredIso (coloring T) (coloring U)) (d e : Fin 3) (p : J × J) :
    PairMark U d e (f.sink p.1,f.sink p.2) ↔ PairMark T d e p := by
  simp only [PairMark,leaf_mark_transport,f.sink.injective.ne_iff]

end KroneckerTablePairMarks
end
