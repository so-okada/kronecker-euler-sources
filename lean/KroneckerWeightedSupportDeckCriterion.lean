import KroneckerAccumulatedConnectedMapRigidity
import KroneckerAccumulatedDimensionClasses
import KroneckerQuiverSupportEulerTransport

/-! A connected weighted support isomorphism preserving original vertex and
arrow labels extends to an accumulated deck transformation. Conversely every
accumulated dimension relation gives exactly such a full support isomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedSupportDeckCriterion
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver LabeledWalk
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerTypedQuiverMaps KroneckerAccumulatedCoverDeckActions
open KroneckerAccumulatedConnectedMapRigidity KroneckerAccumulatedDimensionClasses
open KroneckerAccumulatedDeckBaseLabels KroneckerQuiverSupportEulerTransport
attribute [local instance] Classical.decEq Classical.propDecidable

def SupportConnected (Q : TypedQuiver) (d : Q.V →₀ ℕ) : Prop :=
  ∃ r : (supportQuiver Q d).V, ∀ v,
    Nonempty (LabeledWalk (supportQuiver Q d).source (supportQuiver Q d).target r v)

structure WeightedIso (Q : TypedQuiver) (n : ℕ) (d e : (Q.iterate n).V →₀ ℕ) where
  iso : TypedQuiverIso (supportQuiver (Q.iterate n) d) (supportQuiver (Q.iterate n) e)
  weight : ∀ v, e (iso.vertexEquiv v).val = d v.val
  vertex_label : ∀ v, baseVertex Q n (iso.vertexEquiv v).val = baseVertex Q n v.val
  arrow_label : ∀ a, baseArrow Q n (iso.arrowEquiv a).val = baseArrow Q n a.val

theorem weightedIso_deck (Q : TypedQuiver) (n : ℕ) (d e : (Q.iterate n).V →₀ ℕ)
    (hc : SupportConnected (Q.iterate n) d) (j : WeightedIso Q n d e) : Related Q n e d := by
  obtain ⟨r,hc⟩ := hc
  let P := supportQuiver (Q.iterate n) d
  let f : QuiverMap P (Q.iterate n) := ⟨Subtype.val,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  let g : QuiverMap P (Q.iterate n) :=
    ⟨fun v => (j.iso.vertexEquiv v).val,fun a => (j.iso.arrowEquiv a).val,
      fun a => congrArg Subtype.val (j.iso.map_source a),fun a => congrArg Subtype.val (j.iso.map_target a)⟩
  obtain ⟨k,hk,_⟩ := connected_maps_deck Q P n f g r hc (j.vertex_label r).symm
    (fun a => (j.arrow_label a).symm)
  refine ⟨k,?_⟩
  ext v
  rw [pullDimension_apply]
  by_cases hv : v ∈ d.support
  · exact (congrArg e (hk.1 ⟨v,hv⟩)).trans (j.weight ⟨v,hv⟩)
  · have hd : d v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hd]
    by_contra he
    let w : (supportQuiver (Q.iterate n) e).V := ⟨k.val.vertexEquiv v,Finsupp.mem_support_iff.mpr he⟩
    obtain ⟨u,hu⟩ := j.iso.vertexEquiv.surjective w
    have hku : k.val.vertexEquiv u.val = k.val.vertexEquiv v :=
      (hk.1 u).trans (congrArg Subtype.val hu)
    exact hv ((k.val.vertexEquiv.injective hku) ▸ u.property)

theorem deck_weightedIso (Q : TypedQuiver) (n : ℕ) {d e : (Q.iterate n).V →₀ ℕ}
    (h : Related Q n e d) : Nonempty (WeightedIso Q n d e) := by
  obtain ⟨f,rfl⟩ := h
  refine ⟨⟨supportQuiverIso f.val e,?_,?_,?_⟩⟩
  · intro v
    exact (pullDimension_apply f.val e v.val).symm
  · intro v
    exact vertex_base_invariant Q n f.val f.property v.val
  · intro a
    exact arrow_base_invariant Q n f.val f.property a.val

theorem weightedIso_iff_deck (Q : TypedQuiver) (n : ℕ) (d e : (Q.iterate n).V →₀ ℕ)
    (hc : SupportConnected (Q.iterate n) d) :
    Nonempty (WeightedIso Q n d e) ↔ Related Q n e d :=
  ⟨fun ⟨j⟩ => weightedIso_deck Q n d e hc j,deck_weightedIso Q n⟩

end KroneckerWeightedSupportDeckCriterion
