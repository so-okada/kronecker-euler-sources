import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.Perm
import KroneckerReflectionFaithfulness

section

/- Original module: KroneckerColoredRootRigidity -/
section
set_option autoImplicit false
namespace KroneckerColoredRootRigidity
open SimpleGraph KroneckerProperColoredReflection KroneckerColoredIncidenceIso
open KroneckerBipartiteIncidence

variable {I J : Type} {R : I → J → Prop} {C : ProperColoring R}

theorem source_fix_propagates (e : ColoredIso C C) {i : I} {j : J}
    (hi : e.source i=i) (h : R i j) : e.sink j=j := by
  have hr : R i (e.sink j) := by simpa only [hi] using (e.incidence i j).mpr h
  have hc : C.color i (e.sink j) hr=C.color i j h := by simpa only [hi] using e.color i j h
  exact congrArg Subtype.val (C.at_source i (a₁:=⟨e.sink j,hr⟩) (a₂:=⟨j,h⟩) hc)

theorem sink_fix_propagates (e : ColoredIso C C) {i : I} {j : J}
    (hj : e.sink j=j) (h : R i j) : e.source i=i := by
  have hr : R (e.source i) j := by simpa only [hj] using (e.incidence i j).mpr h
  have hc : C.color (e.source i) j hr=C.color i j h := by simpa only [hj] using e.color i j h
  exact congrArg Subtype.val (C.at_sink j (a₁:=⟨e.source i,hr⟩) (a₂:=⟨i,h⟩) hc)

theorem fixed_adjacent (e : ColoredIso C C) {u v : I ⊕ J}
    (hu : e.graphIso u=u) (h : (incidenceGraph R).Adj u v) : e.graphIso v=v := by
  cases u with
  | inl i => cases v with
    | inl k => exact False.elim h
    | inr j =>
      have hi : e.source i=i := Sum.inl.inj hu
      exact congrArg Sum.inr (source_fix_propagates e hi h)
  | inr j => cases v with
    | inr k => exact False.elim h
    | inl i =>
      have hj : e.sink j=j := Sum.inr.inj hu
      exact congrArg Sum.inl (sink_fix_propagates e hj h)

theorem fixed_along_walk (e : ColoredIso C C) {u v : I ⊕ J} (p : (incidenceGraph R).Walk u v) :
    e.graphIso u=u → e.graphIso v=v := by
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hu => ih (fixed_adjacent e hu h)

/-- A color- and bipartition-preserving automorphism fixing one vertex is
identity on a connected support. Finiteness and acyclicity are not needed. -/
theorem connected_root_rigidity (hR : (incidenceGraph R).Connected)
    (e : ColoredIso C C) (u : I ⊕ J) (hu : e.graphIso u=u) :
    (∀ i,e.source i=i) ∧ (∀ j,e.sink j=j) := by
  have hv : ∀ v,e.graphIso v=v := by
    intro v
    obtain ⟨p⟩ := hR.preconnected u v
    exact fixed_along_walk e p hu
  exact ⟨fun i => Sum.inl.inj (hv (.inl i)),fun j => Sum.inr.inj (hv (.inr j))⟩

end KroneckerColoredRootRigidity
end

/- Original module: KroneckerColoredAutomorphismGroup -/
section
set_option autoImplicit false
namespace KroneckerColoredAutomorphismGroup
open KroneckerProperColoredReflection KroneckerColoredIncidenceIso

variable {I J I' J' : Type} {R : I → J → Prop} {R' : I' → J' → Prop}
  {C : ProperColoring R} {C' : ProperColoring R'}

theorem iso_ext {e f : ColoredIso C C'} (hs : e.source=f.source) (ht : e.sink=f.sink) : e=f := by
  cases e; cases f; cases hs; cases ht; rfl

def identity (C : ProperColoring R) : ColoredIso C C where
  source := Equiv.refl I
  sink := Equiv.refl J
  incidence := by intro i j; rfl
  color := by intro i j h; rfl

/-- Multiplication is composition in the permutation-group convention. -/
instance automorphismGroup (C : ProperColoring R) : Group (ColoredIso C C) where
  one := identity C
  mul e f := f.trans e
  inv := ColoredIso.symm
  mul_assoc e f g := by apply iso_ext <;> rfl
  one_mul e := by apply iso_ext <;> rfl
  mul_one e := by apply iso_ext <;> rfl
  inv_mul_cancel e := by
    apply iso_ext <;> apply Equiv.ext <;> intro x <;>
      exact Equiv.symm_apply_apply _ x

theorem automorphism_pair_injective :
    Function.Injective (fun e : ColoredIso C C => (e.source,e.sink)) := by
  intro e f h
  exact iso_ext (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable instance automorphismFintype [Fintype I] [Fintype J] : Fintype (ColoredIso C C) := by
  classical
  exact Fintype.ofInjective _ automorphism_pair_injective

theorem automorphism_eq_one_iff (e : ColoredIso C C) :
    e=1 ↔ (∀ i,e.source i=i) ∧ (∀ j,e.sink j=j) := by
  constructor
  · rintro rfl; exact ⟨fun _ => rfl,fun _ => rfl⟩
  · rintro ⟨hs,ht⟩
    exact iso_ext (Equiv.ext hs) (Equiv.ext ht)

end KroneckerColoredAutomorphismGroup
end
end

section

/- Original module: KroneckerReflectionNaturality -/
section
set_option autoImplicit false
namespace KroneckerReflectionNaturality
open KroneckerProperColoredReflection KroneckerColoredIncidenceIso KroneckerColoredAutomorphismGroup
open KroneckerReflectionFaithfulness KroneckerReflectedReconstruction KroneckerSlotCompletion
open KroneckerRetainedIsoTransport KroneckerRetainedReflectionKernels KroneckerRetainedBlockSupport
attribute [local instance] Classical.propDecidable

/-- If every target is incident, its image is forced by the source images
and by its incident color. -/
theorem iso_determined_by_source {I J I' J' : Type}
    {R : I → J → Prop} {R' : I' → J' → Prop}
    {C : ProperColoring R} {C' : ProperColoring R'}
    (hp : ∀ j,∃ i,R i j) (e f : ColoredIso C C') (hs : e.source=f.source) : e=f := by
  apply iso_ext hs
  apply Equiv.ext
  intro j
  obtain ⟨i,h⟩ := hp j
  have he : R' (f.source i) (e.sink j) := by rw [←hs]; exact (e.incidence i j).mpr h
  have hc : C'.color (f.source i) (e.sink j) he=
      C'.color (f.source i) (f.sink j) ((f.incidence i j).mpr h) := by
    have hec : C'.color (f.source i) (e.sink j) he=C.color i j h := by
      simpa only [hs] using e.color i j h
    exact hec.trans (f.color i j h).symm
  exact congrArg Subtype.val (C'.at_source (f.source i) (a₁:=⟨e.sink j,he⟩)
    (a₂:=⟨f.sink j,(f.incidence i j).mpr h⟩) hc)

variable {I J I' J' : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
  {R : I → J → Prop} {R' : I' → J' → Prop}
  {C : ProperColoring R} {C' : ProperColoring R'}
  (h3 : ∀ i,Fintype.card {j // R i j}=3) (h3' : ∀ i,Fintype.card {j // R' i j}=3)
  (hp : ∀ j,0<Fintype.card {i // R i j}) (hp' : ∀ j,0<Fintype.card {i // R' i j})


theorem recover_retained_sink_map
    (e : ColoredIso (retainedColoring C) (retainedColoring C')) (j : Retained R) :
    (recoverIso h3 h3' hp hp' e).sink j.1=(e.source j).1 := by
  have hj : (reconstructionIso C h3 hp).sink.symm j.1=Sum.inl j := by
    apply (reconstructionIso C h3 hp).sink.injective
    rw [Equiv.apply_symm_apply]
    rfl
  change (reconstructionIso C' h3' hp').sink
    ((completionIso e).sink ((reconstructionIso C h3 hp).sink.symm j.1))=(e.source j).1
  rw [hj]
  rfl

theorem recover_retained_iso (e : ColoredIso C C') :
    recoverIso h3 h3' hp hp' (retainedIso e)=e := by
  refine iso_determined_by_source ?_ (recoverIso h3 h3' hp hp' (retainedIso e)) e rfl
  intro j
  obtain ⟨i,hi⟩ := Fintype.card_pos_iff.mp (hp j)
  exact ⟨i,hi⟩

theorem retained_recover_iso (e : ColoredIso (retainedColoring C) (retainedColoring C')) :
    retainedIso (recoverIso h3 h3' hp hp' e)=e := by
  apply iso_ext
  · apply Equiv.ext
    intro j
    apply Subtype.ext
    exact recover_retained_sink_map h3 h3' hp hp' e j
  · rfl

/-- Reflection is fully faithful on actual color-preserving incidence maps,
not only on the proposition that an isomorphism exists. -/
noncomputable def reflectionIsoEquiv : ColoredIso C C' ≃
    ColoredIso (retainedColoring C) (retainedColoring C') where
  toFun := retainedIso
  invFun := recoverIso h3 h3' hp hp'
  left_inv := recover_retained_iso h3 h3' hp hp'
  right_inv := retained_recover_iso h3 h3' hp hp'

end KroneckerReflectionNaturality
end

/- Original module: KroneckerColoredLeafTransport -/
section
set_option autoImplicit false
namespace KroneckerColoredLeafTransport
open KroneckerProperColoredReflection KroneckerColoredIncidenceIso
open KroneckerRetainedVacantSlots KroneckerSlotIsoTransport
open KroneckerRetainedIsoTransport KroneckerRetainedReflectionKernels KroneckerRetainedBlockSupport
attribute [local instance] Classical.propDecidable

variable {I J I' J' : Type} [Fintype I] [Fintype I']
  {R : I → J → Prop} {R' : I' → J' → Prop}
  {C : ProperColoring R} {C' : ProperColoring R'}

def leafEquiv (e : ColoredIso C C') :
    {j : J // Fintype.card {i // R i j}=1} ≃ {j : J' // Fintype.card {i // R' i j}=1} where
  toFun j := ⟨e.sink j,(e.sink_degree j).trans j.2⟩
  invFun j := ⟨e.sink.symm j,(e.symm.sink_degree j).trans j.2⟩
  left_inv j := by apply Subtype.ext; exact e.sink.symm_apply_apply j
  right_inv j := by apply Subtype.ext; exact e.sink.apply_symm_apply j



/-- The slot-to-leaf dictionary commutes with actual relabeling. -/
theorem slot_leaf_natural [Fintype J] [Fintype J']
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (h3' : ∀ i,Fintype.card {j // R' i j}=3)
    (e : ColoredIso C C') (p : Slot (retainedBlock R) (retainedColoring C)) :
    actualSlotLeafEquiv C' h3' (slotEquiv (retainedIso e) p)=leafEquiv e (actualSlotLeafEquiv C h3 p) := by
  apply Subtype.ext
  change (actualSlotLeafEquiv C' h3' (slotEquiv (retainedIso e) p)).1=
    e.sink (actualSlotLeafEquiv C h3 p).1
  have h₁ := (actual_slot_leaf_incidence C h3 p p.1.1).mpr rfl
  have h₂ := (e.incidence _ _).mpr h₁
  have h₃ := (actual_slot_leaf_incidence C' h3' (slotEquiv (retainedIso e) p) (e.source p.1.1)).mpr rfl
  have hc : C'.color (e.source p.1.1) _ h₃=C'.color (e.source p.1.1) _ h₂ := by
    exact (actual_slot_leaf_color C' h3' (slotEquiv (retainedIso e) p) h₃).trans
      ((actual_slot_leaf_color C h3 p h₁).symm.trans (e.color _ _ h₁).symm)
  exact congrArg (fun q : {j // R' (e.source p.1.1) j} => q.1) (C'.at_source (e.source p.1.1) (a₁:=⟨_,h₃⟩) (a₂:=⟨_,h₂⟩) hc)

end KroneckerColoredLeafTransport
end
end

