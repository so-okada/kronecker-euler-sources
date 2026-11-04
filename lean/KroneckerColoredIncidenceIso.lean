import KroneckerRetainedVacantSlots

/- Original module: KroneckerSlotCompletion -/
section
set_option autoImplicit false
namespace KroneckerSlotCompletion
open KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerProperColoredReflection KroneckerRetainedVacantSlots
attribute [local instance] Classical.propDecidable

abbrev CompletedSink (B : LinearCoverBlock) (C : ProperColoring (linearSupport B)) :=
  B.Source ⊕ Slot B C

def completedIncidence (B : LinearCoverBlock) (C : ProperColoring (linearSupport B)) :
    B.Sink → CompletedSink B C → Prop
  | i, .inl s => linearSupport B s i
  | i, .inr p => i=p.1.1

def completedColor (B : LinearCoverBlock) (C : ProperColoring (linearSupport B)) :
    ∀ i j,completedIncidence B C i j → Fin 3
  | i, .inl s, h => C.color s i h
  | _, .inr p, _ => p.1.2

theorem completed_color_injective (B : LinearCoverBlock) (C : ProperColoring (linearSupport B))
    (i : B.Sink) : Function.Injective
      (fun j : {j // completedIncidence B C i j} => completedColor B C i j j.2) := by
  rintro ⟨s,hs⟩ ⟨t,ht⟩ h
  apply Subtype.ext
  cases s with
  | inl s => cases t with
    | inl t => exact congrArg Sum.inl (congrArg Subtype.val
        (C.at_sink i (a₁:=⟨s,hs⟩) (a₂:=⟨t,ht⟩) h))
    | inr p =>
      change i=p.1.1 at ht
      subst i
      exact False.elim (p.2 ⟨s,hs,h⟩)
  | inr p => cases t with
    | inl t =>
      change i=p.1.1 at hs
      subst i
      exact False.elim (p.2 ⟨t,ht,h.symm⟩)
    | inr q =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext (hs.symm.trans ht) h


noncomputable def completedColoring (B : LinearCoverBlock) (C : ProperColoring (linearSupport B)) :
    ProperColoring (completedIncidence B C) where
  color := completedColor B C
  at_source := completed_color_injective B C
  at_sink := by
    intro j a b h
    apply Subtype.ext
    cases j with
    | inl s => exact congrArg Subtype.val (C.at_source s h)
    | inr p => exact a.2.trans b.2.symm


end KroneckerSlotCompletion
end

/- Original module: KroneckerColoredIncidenceIso -/
section
set_option autoImplicit false
namespace KroneckerColoredIncidenceIso
open KroneckerProperColoredReflection KroneckerBipartiteIncidence
attribute [local instance] Classical.propDecidable

structure ColoredIso {I J I' J' : Type} {R : I → J → Prop} {R' : I' → J' → Prop}
    (C : ProperColoring R) (C' : ProperColoring R') where
  source : I ≃ I'
  sink : J ≃ J'
  incidence : ∀ i j,R' (source i) (sink j) ↔ R i j
  color : ∀ i j (h : R i j),C'.color (source i) (sink j) ((incidence i j).mpr h)=C.color i j h

namespace ColoredIso
variable {I J I' J' I'' J'' : Type} {R : I → J → Prop} {R' : I' → J' → Prop}
  {R'' : I'' → J'' → Prop} {C : ProperColoring R} {C' : ProperColoring R'}
  {C'' : ProperColoring R''}

def symm (e : ColoredIso C C') : ColoredIso C' C where
  source := e.source.symm
  sink := e.sink.symm
  incidence := by intro i j; simpa using (e.incidence (e.source.symm i) (e.sink.symm j)).symm
  color := by intro i j h; simpa using (e.color (e.source.symm i) (e.sink.symm j) _).symm

def trans (e : ColoredIso C C') (f : ColoredIso C' C'') : ColoredIso C C'' where
  source := e.source.trans f.source
  sink := e.sink.trans f.sink
  incidence := by intro i j; exact (f.incidence _ _).trans (e.incidence i j)
  color := by intro i j h; exact (f.color _ _ _).trans (e.color i j h)

def sourceNeighbors (e : ColoredIso C C') (i : I) : {j // R i j} ≃ {j // R' (e.source i) j} where
  toFun j := ⟨e.sink j,(e.incidence i j).mpr j.2⟩
  invFun j := ⟨e.sink.symm j,(e.incidence i (e.sink.symm j)).mp (by simpa using j.2)⟩
  left_inv := by intro j; apply Subtype.ext; exact e.sink.symm_apply_apply j
  right_inv := by intro j; apply Subtype.ext; exact e.sink.apply_symm_apply j

def sinkNeighbors (e : ColoredIso C C') (j : J) : {i // R i j} ≃ {i // R' i (e.sink j)} where
  toFun i := ⟨e.source i,(e.incidence i j).mpr i.2⟩
  invFun i := ⟨e.source.symm i,(e.incidence (e.source.symm i) j).mp (by simpa using i.2)⟩
  left_inv := by intro i; apply Subtype.ext; exact e.source.symm_apply_apply i
  right_inv := by intro i; apply Subtype.ext; exact e.source.apply_symm_apply i

theorem source_degree [Fintype J] [Fintype J'] (e : ColoredIso C C') (i : I) :
    Fintype.card {j // R' (e.source i) j}=Fintype.card {j // R i j} :=
  (Fintype.card_congr (e.sourceNeighbors i)).symm

theorem sink_degree [Fintype I] [Fintype I'] (e : ColoredIso C C') (j : J) :
    Fintype.card {i // R' i (e.sink j)}=Fintype.card {i // R i j} :=
  (Fintype.card_congr (e.sinkNeighbors j)).symm

def graphIso (e : ColoredIso C C') : incidenceGraph R ≃g incidenceGraph R' where
  toEquiv := Equiv.sumCongr e.source e.sink
  map_rel_iff' := by
    intro u v
    cases u <;> cases v <;> simp only [Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr]
    · rfl
    · exact e.incidence _ _
    · exact e.incidence _ _
    · rfl

end ColoredIso
end KroneckerColoredIncidenceIso
end
