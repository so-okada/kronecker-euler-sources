import KroneckerTypedQuiverMaps

section

/-! Accumulated deck maps act freely on each original-vertex fiber. A single
vertex image therefore determines the entire quiver automorphism, including
its action on every arrow and on disconnected components. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDeckFreeAction
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerAccumulatedCoverDeckActions
open KroneckerAbelianAffineQuiverLift KroneckerAbelianCharacterReindex
attribute [local instance] Classical.decEq Classical.propDecidable

theorem fixed_vertex_identity (Q : TypedQuiver) (n : ℕ)
    (f : TypedQuiverIso (Q.iterate n) (Q.iterate n)) (hf : Accumulated Q n f)
    (u : (Q.iterate n).V) (hu : f.vertexEquiv u = u) :
    f = TypedQuiverIso.refl (Q.iterate n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    obtain ⟨g,ξ,hg,rfl⟩ := hf
    have hgu : g.vertexEquiv u.1 = u.1 := congrArg Prod.fst hu
    have he := ih g hg u.1 hgu
    subst g
    have hc : u.2 + ξ = u.2 := congrArg Prod.snd hu
    have hz : ξ = 0 := add_left_cancel (hc.trans (add_zero u.2).symm)
    subst ξ
    exact affine_identity (Q.iterate n)

theorem deck_ext_at (Q : TypedQuiver) (n : ℕ) (f g : Deck Q n)
    (u : (Q.iterate n).V) (h : f.val.vertexEquiv u = g.val.vertexEquiv u) : f = g := by
  have hu : (TypedQuiverIso.trans f.val g.val.symm).vertexEquiv u = u := by
    change g.val.vertexEquiv.symm (f.val.vertexEquiv u) = u
    rw [h,Equiv.symm_apply_apply]
  have he := fixed_vertex_identity Q n _ (compose f (inverse g)).property u hu
  apply Subtype.ext
  apply quiverIso_ext
  · ext x
    have hx := congrArg (fun k : TypedQuiverIso (Q.iterate n) (Q.iterate n) => k.vertexEquiv x) he
    change g.val.vertexEquiv.symm (f.val.vertexEquiv x) = x at hx
    exact g.val.vertexEquiv.symm.injective (hx.trans (g.val.vertexEquiv.symm_apply_apply x).symm)
  · ext a
    have ha := congrArg (fun k : TypedQuiverIso (Q.iterate n) (Q.iterate n) => k.arrowEquiv a) he
    change g.val.arrowEquiv.symm (f.val.arrowEquiv a) = a at ha
    exact g.val.arrowEquiv.symm.injective (ha.trans (g.val.arrowEquiv.symm_apply_apply a).symm)

end KroneckerAccumulatedDeckFreeAction
end
end

section

/- Original module: KroneckerAccumulatedDeckFiberEquivalence -/
section
/-! The accumulated deck group is a torsor for each base-vertex fiber. The
unique transport between two chosen roots has identity, inverse, and cocycle
laws as actual quiver automorphisms. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDeckFiberEquivalence
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver
open KroneckerAccumulatedCoverDeckActions KroneckerAccumulatedDeckBaseLabels
open KroneckerAccumulatedDeckRootTransitivity KroneckerAccumulatedDeckFreeAction
attribute [local instance] Classical.decEq Classical.propDecidable

def fiberEquiv (Q : TypedQuiver) (n : ℕ) (u : (Q.iterate n).V) :
    Deck Q n ≃ {v : (Q.iterate n).V // baseVertex Q n v = baseVertex Q n u} :=
  Equiv.ofBijective (fun f => ⟨f.val.vertexEquiv u,vertex_base_invariant Q n f.val f.property u⟩)
    ⟨fun f g h => deck_ext_at Q n f g u (congrArg Subtype.val h),by
      intro v
      obtain ⟨f,hf⟩ := exists_deck_to_root Q n u v.val v.property.symm
      exact ⟨f,Subtype.ext hf⟩⟩

def rootTransport (Q : TypedQuiver) (n : ℕ) (u v : (Q.iterate n).V)
    (h : baseVertex Q n u = baseVertex Q n v) : Deck Q n :=
  (fiberEquiv Q n u).symm ⟨v,h.symm⟩

theorem rootTransport_apply (Q : TypedQuiver) (n : ℕ) (u v : (Q.iterate n).V)
    (h : baseVertex Q n u = baseVertex Q n v) :
    (rootTransport Q n u v h).val.vertexEquiv u = v :=
  congrArg Subtype.val ((fiberEquiv Q n u).apply_symm_apply ⟨v,h.symm⟩)



theorem rootTransport_inverse (Q : TypedQuiver) (n : ℕ) (u v : (Q.iterate n).V)
    (h : baseVertex Q n u = baseVertex Q n v) :
    inverse (rootTransport Q n u v h) = rootTransport Q n v u h.symm := by
  apply deck_ext_at Q n _ _ v
  change (rootTransport Q n u v h).val.vertexEquiv.symm v = _
  rw [rootTransport_apply]
  exact (Equiv.symm_apply_eq _).2 (rootTransport_apply Q n u v h).symm

end KroneckerAccumulatedDeckFiberEquivalence
end
end

/- Original module: KroneckerAccumulatedConnectedMapRigidity -/
section
/-! Two connected labeled realizations in the same iterated cover differ by
one unique accumulated deck transformation whenever their original arrow labels
and chosen base vertex agree. The theorem identifies all actual arrows too. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedConnectedMapRigidity
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver LabeledWalk
open KroneckerTypedQuiverMaps KroneckerAccumulatedCoverDeckActions
open KroneckerAccumulatedDeckBaseLabels KroneckerAccumulatedDeckWalkTransport
open KroneckerAccumulatedDeckFiberEquivalence KroneckerAccumulatedDeckFreeAction
open KroneckerIteratedQuiverBaseProjection
attribute [local instance] Classical.decEq Classical.propDecidable

theorem connected_maps_deck (Q P : TypedQuiver) (n : ℕ)
    (f g : QuiverMap P (Q.iterate n)) (r : P.V)
    (hc : ∀ v, Nonempty (LabeledWalk P.source P.target r v))
    (hr : baseVertex Q n (f.vertex r) = baseVertex Q n (g.vertex r))
    (ha : ∀ a, baseArrow Q n (f.arrow a) = baseArrow Q n (g.arrow a)) :
    ∃! k : Deck Q n, (∀ v, k.val.vertexEquiv (f.vertex v) = g.vertex v) ∧
      (∀ a, k.val.arrowEquiv (f.arrow a) = g.arrow a) := by
  let k := rootTransport Q n (f.vertex r) (g.vertex r) hr
  have hv : ∀ v, k.val.vertexEquiv (f.vertex v) = g.vertex v := by
    intro v
    obtain ⟨p⟩ := hc v
    apply endpoint_of_base_word Q n k (f.walk p) (g.walk p) (rootTransport_apply Q n _ _ hr)
    rw [base_labels,base_labels,QuiverMap.walk,QuiverMap.walk,transport_labels,transport_labels,
      List.map_map,List.map_map]
    congr 1
    funext x
    exact Prod.ext (ha x.1) rfl
  refine ⟨k,⟨hv,?_⟩,?_⟩
  · intro a
    apply baseArrow_source_injective Q n
    · exact (arrow_base_invariant Q n k.val k.property (f.arrow a)).trans (ha a)
    · rw [k.val.map_source,f.source,hv,g.source]
  · intro l hl
    exact deck_ext_at Q n l k (f.vertex r) ((hl.1 r).trans (hv r).symm)

end KroneckerAccumulatedConnectedMapRigidity
end
end
end

