import KroneckerReflectedSupportClasses
import KroneckerQuarticBinomialLower
import KroneckerSlotBinomialComparison

/- Original module: KroneckerReflectedMarkedIsomorphisms -/
section
set_option autoImplicit false
namespace KroneckerReflectedMarkedIsomorphisms
open KroneckerProperColoredReflection KroneckerColoredIncidenceIso
open KroneckerRetainedVacantSlots KroneckerRetainedReflectionKernels KroneckerRetainedBlockSupport
open KroneckerSlotIsoTransport KroneckerRetainedIsoTransport KroneckerReflectionFaithfulness
open KroneckerReflectionNaturality KroneckerColoredLeafTransport
attribute [local instance] Classical.propDecidable

variable {I J I' J' A : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
  {R : I → J → Prop} {R' : I' → J' → Prop}
  {C : ProperColoring R} {C' : ProperColoring R'}
  (h3 : ∀ i,Fintype.card {j // R i j}=3) (h3' : ∀ i,Fintype.card {j // R' i j}=3)
  (hp : ∀ j,0<Fintype.card {i // R i j}) (hp' : ∀ j,0<Fintype.card {i // R' i j})
include hp hp'

/-- All specified slot marks are recovered simultaneously, so ordered pairs
and shared-vertex marks introduce no further ambiguity under reflection. -/
theorem marked_reflection_isomorphism_iff
    (p : A → Slot (retainedBlock R) (retainedColoring C))
    (q : A → Slot (retainedBlock R') (retainedColoring C')) :
    (∃ f : ColoredIso (retainedColoring C) (retainedColoring C'),∀ a,slotEquiv f (p a)=q a) ↔
    (∃ e : ColoredIso C C',∀ a,e.sink (actualSlotLeafEquiv C h3 (p a)).1=
      (actualSlotLeafEquiv C' h3' (q a)).1) := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨recoverIso h3 h3' hp hp' f,?_⟩
    intro a
    have h := slot_leaf_natural h3 h3' (recoverIso h3 h3' hp hp' f) (p a)
    rw [retained_recover_iso,hf a] at h
    exact (congrArg Subtype.val h).symm
  · rintro ⟨e,he⟩
    refine ⟨retainedIso e,?_⟩
    intro a
    apply (actualSlotLeafEquiv C' h3').injective
    rw [slot_leaf_natural h3 h3' e (p a)]
    exact Subtype.ext (he a)

end KroneckerReflectedMarkedIsomorphisms
end

/- Original module: KroneckerMarkedReflectionClasses -/
section
set_option autoImplicit false
namespace KroneckerMarkedReflectionClasses
open KroneckerColoredIncidenceIso KroneckerRetainedVacantSlots KroneckerSlotIsoTransport
open KroneckerReflectedSupportClasses KroneckerSaturatedBlockData KroneckerReflectedMarkedIsomorphisms

theorem slot_transport_symm {B D : ColoredBlock} (e : ColoredIso B.coloring D.coloring)
    (p : Slot B.block B.coloring) : slotEquiv e.symm (slotEquiv e p)=p := by
  apply Subtype.ext
  exact Prod.ext (e.sink.symm_apply_apply p.1.1) rfl

theorem slot_transport_trans {B D E : ColoredBlock}
    (e : ColoredIso B.coloring D.coloring) (f : ColoredIso D.coloring E.coloring)
    (p : Slot B.block B.coloring) : slotEquiv (e.trans f) p=slotEquiv f (slotEquiv e p) := rfl

structure MarkedSupport (A : Type) where
  block : ColoredBlock
  mark : A → Slot block.block block.coloring

def markedSupportSetoid (A : Type) : Setoid (MarkedSupport A) where
  r X Y := ∃ e : ColoredIso X.block.coloring Y.block.coloring,∀ a,slotEquiv e (X.mark a)=Y.mark a
  iseqv := by
    constructor
    · intro X
      exact ⟨identityIso X.block.coloring,fun _ => rfl⟩
    · rintro X Y ⟨e,he⟩
      refine ⟨e.symm,?_⟩
      intro a
      rw [←he a]
      exact slot_transport_symm e (X.mark a)
    · rintro X Y Z ⟨e,he⟩ ⟨f,hf⟩
      refine ⟨e.trans f,?_⟩
      intro a
      rw [slot_transport_trans,he a,hf a]

structure OriginalSlotData (A : Type) where
  tree : SaturatedBlockData
  mark : A → Slot (supportedBlock tree) (supportedColoring tree)

noncomputable def reflectMarks {A : Type} (X : OriginalSlotData A) : MarkedSupport A :=
  ⟨reflectedColoredBlock X.tree,X.mark⟩

def OriginalMarkedIso {A : Type} (X Y : OriginalSlotData A) : Prop :=
  ∃ e : ColoredIso X.tree.coloring Y.tree.coloring,∀ a,
    e.sink (actualSlotLeafEquiv X.tree.coloring X.tree.saturated (X.mark a)).1=
      (actualSlotLeafEquiv Y.tree.coloring Y.tree.saturated (Y.mark a)).1

theorem original_marked_iso_iff {A : Type} (X Y : OriginalSlotData A) :
    OriginalMarkedIso X Y ↔ markedSupportSetoid A (reflectMarks X) (reflectMarks Y) :=
  (marked_reflection_isomorphism_iff X.tree.saturated Y.tree.saturated
    (original_degrees_positive X.tree) (original_degrees_positive Y.tree) X.mark Y.mark).symm

def markedOriginalSetoid (A : Type) : Setoid (OriginalSlotData A) where
  r := OriginalMarkedIso
  iseqv := by
    constructor
    · intro X
      exact (original_marked_iso_iff X X).mpr ((markedSupportSetoid A).refl _)
    · intro X Y h
      exact (original_marked_iso_iff Y X).mpr
        ((markedSupportSetoid A).symm ((original_marked_iso_iff X Y).mp h))
    · intro X Y Z h₁ h₂
      exact (original_marked_iso_iff X Z).mpr
        ((markedSupportSetoid A).trans ((original_marked_iso_iff X Y).mp h₁)
          ((original_marked_iso_iff Y Z).mp h₂))

noncomputable def markedReflectionOnClasses (A : Type) :
    Quotient (markedOriginalSetoid A) → Quotient (markedSupportSetoid A) :=
  Quotient.map reflectMarks (fun X Y h => (original_marked_iso_iff X Y).mp h)


end KroneckerMarkedReflectionClasses
end

/- Original module: KroneckerSingleMarkedLowerBound -/
section
set_option autoImplicit false
namespace KroneckerSingleMarkedLowerBound
open KroneckerQuarticBinomialLower KroneckerSlotBinomialComparison
open KroneckerActualSourceClosedCounts KroneckerMarkedTreeClassCount
attribute [local instance] Classical.propDecidable

theorem single_marked_sqrt_lower (j : ℕ) (hj : 0<j) (d : Fin 3) :
    (binomialLowerConstant/7)*(256/27:ℝ)^j/(j*Real.sqrt j)≤
      (Fintype.card (MarkedClass (Fin (j+1)) (Fin (2*(j+1)+1)) d) : ℝ) := by
  have hjR : (0:ℝ)<j := by exact_mod_cast hj
  have hc : (Fintype.card (MarkedClass (Fin (j+1)) (Fin (2*(j+1)+1)) d) : ℝ)=
      ((4*j+4).choose (j+1) : ℝ)/(3*j+4) := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (actual_single_marked_count j d)
    simpa only [Rat.cast_natCast,Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using h
  have hb := (quartic_binomial_lower j hj).trans
    (show ((4*j).choose j : ℝ)≤((4*j+4).choose (j+1) : ℝ) by
      exact_mod_cast single_mark_binomial_comparison j)
  have hd : (3*j+4:ℝ)≤7*j := by
    have : (1:ℝ)≤j := by exact_mod_cast hj
    linarith
  rw [hc]
  calc
    _ = (binomialLowerConstant*(256/27:ℝ)^j/Real.sqrt j)/(7*j) := by ring
    _ ≤ ((4*j+4).choose (j+1) : ℝ)/(7*j) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hd

/-- The j^(-3/2) lower bound holds for all j≥1, hence in particular for j≥256. -/
theorem actual_single_marked_uniform_lower : ∃ A : ℝ,0<A ∧
    ∀ j : ℕ,0<j → ∀ d : Fin 3,
      A*(256/27:ℝ)^j*(j:ℝ)^(-3/2:ℝ)≤
        (Fintype.card (MarkedClass (Fin (j+1)) (Fin (2*(j+1)+1)) d) : ℝ) := by
  refine ⟨binomialLowerConstant/7,div_pos binomial_lower_constant_pos (by norm_num),?_⟩
  intro j hj d
  have hjR : (0:ℝ)<j := by exact_mod_cast hj
  have hp : (j:ℝ)^(-3/2:ℝ)=(j*Real.sqrt j)⁻¹ := by
    rw [show (-3/2:ℝ)=-(1+1/2) by norm_num,Real.rpow_neg hjR.le,
      Real.rpow_add hjR,Real.rpow_one,←Real.sqrt_eq_rpow]
  rw [hp,←div_eq_mul_inv]
  exact single_marked_sqrt_lower j hj d

end KroneckerSingleMarkedLowerBound
end

/- Original module: KroneckerReflectedSingleSlotCounts -/
section
set_option autoImplicit false
namespace KroneckerReflectedSingleSlotCounts
open KroneckerFiniteColoredTables KroneckerSaturatedTableAction KroneckerRetainedVacantSlots
open KroneckerRetainedReflectionKernels KroneckerRetainedBlockSupport KroneckerSlotIsoTransport
open KroneckerTableLeafMarks KroneckerMarkedTableAction KroneckerMarkedTreeClassCount
open KroneckerMarkedClassIsomorphisms KroneckerMarkedReflectionClasses KroneckerColoredIncidenceIso
open KroneckerReflectedMarkedIsomorphisms KroneckerSaturatedTreeDimensions
open KroneckerActualSourceClosedCounts KroneckerSingleMarkedLowerBound
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I] [Fintype J]

abbrev ReflectedSlot (T : SaturatedTable I J) :=
  Slot (retainedBlock (Incidence T.1)) (retainedColoring (coloring T.1))

noncomputable def slotMarkEquiv (T : SaturatedTable I J) (d : Fin 3) :
    {p : ReflectedSlot T // p.1.2=d} ≃ {j // LeafMark T.1 d j} :=
  (coloredSlotLeafEquiv (coloring T.1) T.2.2 d).trans (leafMarkEquiv T.1 d).symm

abbrev SingleSlotObject (I J : Type) [Fintype I] [Fintype J] (d : Fin 3) :=
  Σ T : SaturatedTable I J,{p : ReflectedSlot T // p.1.2=d}

noncomputable def singleSlotObjectEquiv (d : Fin 3) :
    SingleSlotObject I J d ≃ MarkedTable I J d where
  toFun M := ⟨(M.1,(slotMarkEquiv M.1 d M.2).1),(slotMarkEquiv M.1 d M.2).2⟩
  invFun N := ⟨N.1.1,(slotMarkEquiv N.1.1 d).symm ⟨N.1.2,N.2⟩⟩
  left_inv M := by
    rcases M with ⟨T,p⟩
    exact congrArg (fun q => (⟨T,q⟩ : SingleSlotObject I J d))
      ((slotMarkEquiv T d).symm_apply_apply p)
  right_inv N := by
    apply Subtype.ext
    change (N.1.1,((slotMarkEquiv N.1.1 d) ((slotMarkEquiv N.1.1 d).symm ⟨N.1.2,N.2⟩)).1)=N.1
    rw [Equiv.apply_symm_apply]

/-- The relation uses isomorphisms of the actual reflected colored supports and their slots. -/
def singleSlotSetoid (I J : Type) [Fintype I] [Fintype J] (d : Fin 3) :
    Setoid (SingleSlotObject I J d) where
  r M N := ∃ e : ColoredIso (retainedColoring (coloring M.1.1))
      (retainedColoring (coloring N.1.1)),slotEquiv e M.2.1=N.2.1
  iseqv := by
    constructor
    · intro M; exact ⟨1,rfl⟩
    · rintro M N ⟨e,he⟩
      refine ⟨e.symm,?_⟩
      rw [←he]
      apply Subtype.ext
      exact Prod.ext (e.sink.symm_apply_apply _) rfl
    · rintro M N P ⟨e,he⟩ ⟨f,hf⟩
      refine ⟨e.trans f,?_⟩
      change slotEquiv f (slotEquiv e M.2.1)=P.2.1
      rw [he,hf]

abbrev SingleSlotClass (I J : Type) [Fintype I] [Fintype J] (d : Fin 3) :=
  Quotient (singleSlotSetoid I J d)

noncomputable instance (d : Fin 3) : Fintype (SingleSlotClass I J d) := Fintype.ofFinite _

variable [Nonempty I] [Nonempty J]

theorem single_slot_relation_iff (d : Fin 3) (M N : SingleSlotObject I J d) :
    singleSlotSetoid I J d M N ↔
      (Quotient.mk'' (singleSlotObjectEquiv d M) : MarkedClass I J d)=
        Quotient.mk'' (singleSlotObjectEquiv d N) := by
  rw [marked_class_eq_iff]
  have h := marked_reflection_isomorphism_iff M.1.2.2 N.1.2.2
    (saturated_sink_degree_positive _ M.1.2.1) (saturated_sink_degree_positive _ N.1.2.1)
    (fun _ : Unit => M.2.1) (fun _ : Unit => N.2.1)
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨f,hf⟩ := h.mp ⟨e,fun _ => he⟩
    exact ⟨f,hf ()⟩
  · rintro ⟨e,he⟩
    obtain ⟨f,hf⟩ := h.mpr ⟨e,fun _ => he⟩
    exact ⟨f,hf ()⟩

/-- Reflection and leaf deletion give an equivalence on actual single-slot classes. -/
noncomputable def singleSlotClassEquiv (d : Fin 3) :
    SingleSlotClass I J d ≃ MarkedClass I J d :=
  Quotient.congr (singleSlotObjectEquiv d) (fun M N =>
    (single_slot_relation_iff d M N).trans Quotient.eq)

theorem single_slot_cardinality (d : Fin 3) :
    Fintype.card (SingleSlotClass I J d)=Fintype.card (MarkedClass I J d) := by
  simp only [←Nat.card_eq_fintype_card]
  exact Nat.card_congr (singleSlotClassEquiv d)


theorem reflected_single_slot_uniform_lower : ∃ A : ℝ,0<A ∧
    ∀ j : ℕ,0<j → ∀ d : Fin 3,
      A*(256/27:ℝ)^j*(j:ℝ)^(-3/2:ℝ)≤
        (Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d) : ℝ) := by
  obtain ⟨A,hA,h⟩ := actual_single_marked_uniform_lower
  refine ⟨A,hA,?_⟩
  intro j hj d
  have hc := single_slot_cardinality (I:=Fin (j+1)) (J:=Fin (2*(j+1)+1)) d
  have h' := h j hj d
  simp only [←Nat.card_eq_fintype_card] at hc h' ⊢
  rw [hc]
  exact h'

end KroneckerReflectedSingleSlotCounts
end
