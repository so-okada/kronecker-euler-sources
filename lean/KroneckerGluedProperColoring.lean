import KroneckerGluedSupportGraph

set_option autoImplicit false
namespace KroneckerGluedProperColoring
open KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport KroneckerProperColoredReflection
open KroneckerGluedSupportGraph

/-- Slot injectivity permits equal colors at different sinks and different
colors at the same sink. No proper coloring of the skeleton's block nodes is assumed. -/
structure GluingColors {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) (C : ∀ j,ProperColoring (linearSupport (B j))) where
  color : ∀ i j,R i j → Fin 3
  connectorProper : ∀ i,Function.Injective (fun j : {j // R i j} => color i j.1 j.2)
  slotInjective : ∀ j,Function.Injective
    (fun i : {i // R i j} => (attach i.1 j i.2,color i.1 j i.2))
  vacant : ∀ i j (h : R i j) s (hs : linearSupport (B j) s (attach i j h)),
    (C j).color s (attach i j h) hs≠color i j h

noncomputable def gluedColor {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : ∀ j,ProperColoring (linearSupport (B j))) (D : GluingColors B R attach C) :
    ∀ s t,GlueEdge B R attach s t → Fin 3 := by
  rintro (i | ⟨j,s⟩) ⟨k,t⟩ h
  · exact D.color i k (Classical.choose ((glue_edge_connector_iff B R attach i k t).mp h))
  · have he : j=k := by
      by_contra hn
      exact glue_edge_internal_other B R attach hn s t h
    subst k
    exact (C j).color s t ((glue_edge_internal_iff B R attach j s t).mp h)



theorem glued_color_source_injective {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : ∀ j,ProperColoring (linearSupport (B j))) (D : GluingColors B R attach C)
    (s : I ⊕ (Σ j,(B j).Source)) :
    Function.Injective (fun t : {t // GlueEdge B R attach s t} =>
      gluedColor B R attach C D s t.1 t.2) := by
  rintro ⟨⟨j,t⟩,ht⟩ ⟨⟨k,u⟩,hu⟩ he
  cases s with
  | inl i =>
    obtain ⟨hij,htj⟩ := (glue_edge_connector_iff B R attach i j t).mp ht
    obtain ⟨hik,huk⟩ := (glue_edge_connector_iff B R attach i k u).mp hu
    subst t
    subst u
    change D.color i j hij=D.color i k hik at he
    have hjk := D.connectorProper i (a₁:=⟨j,hij⟩) (a₂:=⟨k,hik⟩) he
    have hval : j=k := congrArg (fun q : {q // R i q} => q.1) hjk
    subst k
    rfl
  | inr p =>
    rcases p with ⟨l,s⟩
    have hj : l=j := by
      by_contra h
      exact glue_edge_internal_other B R attach h s t ht
    have hk : l=k := by
      by_contra h
      exact glue_edge_internal_other B R attach h s u hu
    subst j
    subst k
    have ht' := (glue_edge_internal_iff B R attach l s t).mp ht
    have hu' := (glue_edge_internal_iff B R attach l s u).mp hu
    change (C l).color s t ht'=(C l).color s u hu' at he
    have htu := (C l).at_source s (a₁:=⟨t,ht'⟩) (a₂:=⟨u,hu'⟩) he
    have hval : t=u := congrArg (fun q : {q // linearSupport (B l) s q} => q.1) htu
    subst u
    rfl

theorem glued_color_sink_injective {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : ∀ j,ProperColoring (linearSupport (B j))) (D : GluingColors B R attach C)
    (t : Σ j,(B j).Sink) :
    Function.Injective (fun s : {s // GlueEdge B R attach s t} =>
      gluedColor B R attach C D s.1 t s.2) := by
  rcases t with ⟨j,t⟩
  rintro ⟨s,hs⟩ ⟨u,hu⟩ he
  cases s with
  | inl i => cases u with
    | inl k =>
      obtain ⟨hij,ht⟩ := (glue_edge_connector_iff B R attach i j t).mp hs
      obtain ⟨hkj,hut⟩ := (glue_edge_connector_iff B R attach k j t).mp hu
      have hc : D.color i j hij=D.color k j hkj := he
      have hi := D.slotInjective j (a₁:=⟨i,hij⟩) (a₂:=⟨k,hkj⟩)
        (Prod.ext (ht.trans hut.symm) hc)
      have hik : i=k := congrArg (fun q : {q // R q j} => q.1) hi
      subst k
      rfl
    | inr p =>
      rcases p with ⟨k,u⟩
      have hk : k=j := by
        by_contra h
        exact glue_edge_internal_other B R attach h u t hu
      subst k
      obtain ⟨hij,ht⟩ := (glue_edge_connector_iff B R attach i j t).mp hs
      subst t
      have hu' := (glue_edge_internal_iff B R attach j u (attach i j hij)).mp hu
      have hc : D.color i j hij=(C j).color u (attach i j hij) hu' := he
      exact False.elim (D.vacant i j hij u hu' hc.symm)
  | inr p =>
    rcases p with ⟨k,s⟩
    have hk : k=j := by
      by_contra h
      exact glue_edge_internal_other B R attach h s t hs
    subst k
    cases u with
    | inl i =>
      obtain ⟨hij,ht⟩ := (glue_edge_connector_iff B R attach i j t).mp hu
      subst t
      have hs' := (glue_edge_internal_iff B R attach j s (attach i j hij)).mp hs
      have hc : (C j).color s (attach i j hij) hs'=D.color i j hij := he
      exact False.elim (D.vacant i j hij s hs' hc)
    | inr p =>
      rcases p with ⟨k,u⟩
      have hk : k=j := by
        by_contra h
        exact glue_edge_internal_other B R attach h u t hu
      subst k
      have hs' := (glue_edge_internal_iff B R attach j s t).mp hs
      have hu' := (glue_edge_internal_iff B R attach j u t).mp hu
      have hc : (C j).color s t hs'=(C j).color u t hu' := he
      have hsu := (C j).at_sink t (a₁:=⟨s,hs'⟩) (a₂:=⟨u,hu'⟩) hc
      have hval : s=u := congrArg (fun q : {q // linearSupport (B j) q t} => q.1) hsu
      subst u
      rfl

noncomputable def gluedProperColoring {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : ∀ j,ProperColoring (linearSupport (B j))) (D : GluingColors B R attach C) :
    ProperColoring (GlueEdge B R attach) where
  color := gluedColor B R attach C D
  at_source := glued_color_source_injective B R attach C D
  at_sink := glued_color_sink_injective B R attach C D

noncomputable def gluedLinearColoring {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (C : ∀ j,ProperColoring (linearSupport (B j))) (D : GluingColors B R attach C) :
    ProperColoring (linearSupport (KroneckerGluedLinearRepresentation.gluedBlock B R attach)) := by
  have he : linearSupport (KroneckerGluedLinearRepresentation.gluedBlock B R attach)=
      GlueEdge B R attach := by
    funext s t
    exact propext (glued_arrow_support_iff B R attach s t)
  rw [he]
  exact gluedProperColoring B R attach C D

end KroneckerGluedProperColoring
