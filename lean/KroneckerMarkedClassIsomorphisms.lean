import KroneckerTableLeafMarks

section

/- Original module: KroneckerLabelledTreeClassCount -/
section
set_option autoImplicit false
namespace KroneckerLabelledTreeClassCount
open KroneckerFiniteColoredTables KroneckerSaturatedTableAction KroneckerSaturatedTreeDimensions
open KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

variable (I J : Type) [Fintype I] [Fintype J]

abbrev TreeClass := Quotient (MulAction.orbitRel (Equiv.Perm I × Equiv.Perm J) (SaturatedTable I J))

omit [Fintype I] in
theorem class_eq_iff (T U : SaturatedTable I J) :
    (Quotient.mk'' T : TreeClass I J)=Quotient.mk'' U ↔
      Nonempty (ColoredIso (coloring T.1) (coloring U.1)) := by
  rw [Quotient.eq]
  exact saturated_orbit_iff_iso U T |>.trans
    ⟨fun ⟨e⟩ => ⟨e.symm⟩,fun ⟨e⟩ => ⟨e.symm⟩⟩




end KroneckerLabelledTreeClassCount
end

/- Original module: KroneckerMarkedTableAction -/
section
set_option autoImplicit false
namespace KroneckerMarkedTableAction
open KroneckerFiniteColoredTables KroneckerTableLeafMarks KroneckerSaturatedTableAction
open KroneckerTableRelabeling KroneckerLabelledTreeClassCount
attribute [local instance] Classical.propDecidable

variable (I J : Type) [Fintype I] [Fintype J] (d : Fin 3)

abbrev MarkedTable := {p : SaturatedTable I J × J // LeafMark p.1.1 d p.2}

variable {I J d}

noncomputable def relabelMark (p : Equiv.Perm I × Equiv.Perm J) (M : MarkedTable I J d) :
    MarkedTable I J d :=
  ⟨(p • M.1.1,p.2 M.1.2),(leaf_mark_transport (relabelIso p M.1.1.1) d M.1.2).mpr M.2⟩

noncomputable instance markedRelabelAction :
    MulAction (Equiv.Perm I × Equiv.Perm J) (MarkedTable I J d) where
  smul := relabelMark
  one_smul M := by apply Subtype.ext; apply Prod.ext; exact one_smul _ _; rfl
  mul_smul p q M := by apply Subtype.ext; apply Prod.ext; exact mul_smul p q M.1.1; rfl


def forgetMark (M : MarkedTable I J d) : SaturatedTable I J := M.1.1

theorem forget_mark_equivariant (p : Equiv.Perm I × Equiv.Perm J) (M : MarkedTable I J d) :
    forgetMark (p • M)=p • forgetMark M := rfl

def markFiberEquiv (T : SaturatedTable I J) :
    {M : MarkedTable I J d // forgetMark M=T} ≃ {j // LeafMark T.1 d j} where
  toFun M := ⟨M.1.1.2,by have h := M.1.2; change LeafMark (forgetMark M.1).1 d M.1.1.2 at h; rwa [M.2] at h⟩
  invFun j := ⟨⟨(T,j.1),j.2⟩,rfl⟩
  left_inv M := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext M.2.symm rfl
  right_inv j := rfl

end KroneckerMarkedTableAction
end
end

section

/- Original module: KroneckerFreeQuotientFibers -/
section
set_option autoImplicit false
namespace KroneckerFreeQuotientFibers

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
  (f : X → Y) (hf : ∀ (g : G) (x : X),f (g • x)=g • f x)

def quotientMap : Quotient (MulAction.orbitRel G X) → Quotient (MulAction.orbitRel G Y) :=
  Quotient.map f (by
    rintro a b ⟨g,hg⟩
    refine ⟨g,?_⟩
    change g • f b=f a
    exact (hf g b).symm.trans (congrArg f hg))

def fiberToOrbit (y : Y) : {x // f x=y} →
    {q : Quotient (MulAction.orbitRel G X) // quotientMap f hf q=Quotient.mk'' y} :=
  fun x => ⟨Quotient.mk'' x.1,congrArg Quotient.mk'' x.2⟩

theorem fiber_to_orbit_injective (hfree : ∀ g : G,∀ y : Y,g • y=y → g=1) (y : Y) :
    Function.Injective (fiberToOrbit f hf y) := by
  intro a b h
  obtain ⟨g,hg⟩ := Quotient.exact (congrArg Subtype.val h)
  change g • b.1=a.1 at hg
  have hfix : g • y=y := by rw [←b.2,←hf,hg,a.2]; exact b.2.symm
  have hg1 := hfree g y hfix
  apply Subtype.ext
  simpa [hg1] using hg.symm

theorem fiber_to_orbit_surjective (y : Y) : Function.Surjective (fiberToOrbit f hf y) := by
  rintro ⟨q,hq⟩
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨g,hg⟩ := Quotient.exact hq
    change g • y=f x at hg
    have hfx : f (g⁻¹ • x)=y := by rw [hf,←hg,inv_smul_smul]
    refine ⟨⟨g⁻¹ • x,hfx⟩,?_⟩
    apply Subtype.ext
    exact Quotient.sound ⟨g⁻¹,rfl⟩

/-- For a free base action, forgetting a mark has exactly the original
mark set as fiber over each unmarked orbit. -/
noncomputable def quotientFiberEquiv (hfree : ∀ g : G,∀ y : Y,g • y=y → g=1) (y : Y) :
    {x // f x=y} ≃
      {q : Quotient (MulAction.orbitRel G X) // quotientMap f hf q=Quotient.mk'' y} :=
  Equiv.ofBijective _ ⟨fiber_to_orbit_injective f hf hfree y,fiber_to_orbit_surjective f hf y⟩


end KroneckerFreeQuotientFibers
end

/- Original module: KroneckerMarkedTreeClassCount -/
section
set_option autoImplicit false
namespace KroneckerMarkedTreeClassCount
open KroneckerTableLeafMarks KroneckerSaturatedTableAction KroneckerLabelledTreeClassCount
open KroneckerMarkedTableAction KroneckerFreeQuotientFibers
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable (I J : Type) [Fintype I] [Fintype J] (d : Fin 3)

abbrev MarkedClass := Quotient
  (MulAction.orbitRel (Equiv.Perm I × Equiv.Perm J) (MarkedTable I J d))

noncomputable def forgetOnClasses : MarkedClass I J d → TreeClass I J :=
  quotientMap forgetMark forget_mark_equivariant

noncomputable def markedClassFiberEquiv (T : SaturatedTable I J) :
    {j // LeafMark T.1 d j} ≃ {q : MarkedClass I J d // forgetOnClasses I J d q=Quotient.mk'' T} :=
  (markFiberEquiv T).symm.trans
    (quotientFiberEquiv forgetMark forget_mark_equivariant saturated_relabel_free T)

theorem marked_class_fiber_count (T : SaturatedTable I J) :
    Fintype.card {q : MarkedClass I J d // forgetOnClasses I J d q=Quotient.mk'' T}=
      Fintype.card {j // LeafMark T.1 d j} :=
  (Fintype.card_congr (markedClassFiberEquiv I J d T)).symm



end KroneckerMarkedTreeClassCount
end
end

section

set_option autoImplicit false
namespace KroneckerMarkedClassIsomorphisms
open KroneckerFiniteColoredTables KroneckerMarkedTableAction KroneckerMarkedTreeClassCount
open KroneckerTableRelabeling KroneckerTableIsomorphisms KroneckerColoredIncidenceIso

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

theorem marked_orbit_iff_pointed (M N : MarkedTable I J d) :
    (∃ p : Equiv.Perm I × Equiv.Perm J,p • M=N) ↔
    ∃ e : ColoredIso (coloring M.1.1.1) (coloring N.1.1.1),e.sink M.1.2=N.1.2 := by
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨relabelIso p M.1.1.1,rfl⟩
  · rintro ⟨e,he⟩
    refine ⟨(e.source,e.sink),Subtype.ext (Prod.ext ?_ he)⟩
    exact Subtype.ext ((relabel_eq_iff _ _ _).mpr (iso_preserves_code _ _ e))

/-- The existing marked orbit quotient has precisely the intended marked colored isomorphisms. -/
theorem marked_class_eq_iff (M N : MarkedTable I J d) :
    (Quotient.mk'' M : MarkedClass I J d)=Quotient.mk'' N ↔
    ∃ e : ColoredIso (coloring M.1.1.1) (coloring N.1.1.1),e.sink M.1.2=N.1.2 := by
  rw [Quotient.eq]
  change (∃ p : Equiv.Perm I × Equiv.Perm J,p • N=M) ↔ _
  rw [marked_orbit_iff_pointed]
  constructor
  · rintro ⟨e,he⟩
    exact ⟨e.symm,by change e.sink.symm M.1.2=N.1.2; rw [←he,Equiv.symm_apply_apply]⟩
  · rintro ⟨e,he⟩
    exact ⟨e.symm,by change e.sink.symm N.1.2=M.1.2; rw [←he,Equiv.symm_apply_apply]⟩

end KroneckerMarkedClassIsomorphisms
end

