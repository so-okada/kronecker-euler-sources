import KroneckerProperBipartiteQuiver

/-! Weighted colored full-support isomorphisms compare DIFFERENT ambient
properly bipartite quivers. Their inverse and composition retain weights,
source/sink types and each actual arrow color. These data provide one common
cross-model relation without presupposing any deck-group identification. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedColoredSupportIso
open KroneckerAbelianCover KroneckerProperBipartiteQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportInducedQuiver
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q R : TypedQuiver}

structure ColoredIso (C : Coloring P) (D : Coloring Q) (d : P.V →₀ ℕ) (e : Q.V →₀ ℕ) where
  iso : TypedQuiverIso (supportQuiver P d) (supportQuiver Q e)
  weight : ∀ v, e (iso.vertexEquiv v).val = d v.val
  side : ∀ v, D.side (iso.vertexEquiv v).val = C.side v.val
  color : ∀ a, D.color (iso.arrowEquiv a).val = C.color a.val

def ColoredIso.refl (C : Coloring P) (d : P.V →₀ ℕ) : ColoredIso C C d d :=
  ⟨TypedQuiverIso.refl _,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

def ColoredIso.symm {C : Coloring P} {D : Coloring Q} {d : P.V →₀ ℕ} {e : Q.V →₀ ℕ}
    (f : ColoredIso C D d e) : ColoredIso D C e d where
  iso := f.iso.symm
  weight v := (f.weight (f.iso.vertexEquiv.symm v)).symm.trans (congrArg (fun w => e w.val) (f.iso.vertexEquiv.apply_symm_apply v))
  side v := (f.side (f.iso.vertexEquiv.symm v)).symm.trans (congrArg (fun w => D.side w.val) (f.iso.vertexEquiv.apply_symm_apply v))
  color a := (f.color (f.iso.arrowEquiv.symm a)).symm.trans (congrArg (fun b => D.color b.val) (f.iso.arrowEquiv.apply_symm_apply a))

def ColoredIso.trans {C : Coloring P} {D : Coloring Q} {E : Coloring R}
    {d : P.V →₀ ℕ} {e : Q.V →₀ ℕ} {k : R.V →₀ ℕ}
    (f : ColoredIso C D d e) (g : ColoredIso D E e k) : ColoredIso C E d k where
  iso := TypedQuiverIso.trans f.iso g.iso
  weight v := (g.weight (f.iso.vertexEquiv v)).trans (f.weight v)
  side v := (g.side (f.iso.vertexEquiv v)).trans (f.side v)
  color a := (g.color (f.iso.arrowEquiv a)).trans (f.color a)

theorem colored_iso_equivalence (C : Coloring P) : Equivalence (fun d e => Nonempty (ColoredIso C C d e)) :=
  ⟨fun d => ⟨ColoredIso.refl C d⟩,fun ⟨f⟩ => ⟨f.symm⟩,fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

def shapeSetoid (C : Coloring P) : Setoid (P.V →₀ ℕ) :=
  ⟨fun d e => Nonempty (ColoredIso C C d e),colored_iso_equivalence C⟩

end KroneckerWeightedColoredSupportIso
