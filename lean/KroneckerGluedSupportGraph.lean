import KroneckerRetainedBlockSupport

set_option autoImplicit false
namespace KroneckerGluedSupportGraph
open SimpleGraph KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedLinearRepresentation KroneckerBipartiteIncidence
attribute [local instance] Classical.propDecidable

inductive GlueEdge {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) : (I ⊕ (Σ j,(B j).Source)) → (Σ j,(B j).Sink) → Prop
  | internal (j : J) (s : (B j).Source) (t : (B j).Sink) (h : linearSupport (B j) s t) :
      GlueEdge B R attach (.inr ⟨j,s⟩) ⟨j,t⟩
  | attachment (i : I) (j : J) (h : R i j) : GlueEdge B R attach (.inl i) ⟨j,attach i j h⟩

theorem glue_edge_connector_iff {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (i : I) (j : J) (t : (B j).Sink) :
    GlueEdge B R attach (.inl i) ⟨j,t⟩ ↔ ∃ h : R i j,attach i j h=t := by
  constructor
  · intro h
    cases h with | attachment i j h => exact ⟨h,rfl⟩
  · rintro ⟨h,ht⟩
    subst t
    exact GlueEdge.attachment i j h

theorem glue_edge_internal_iff {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (j : J) (s : (B j).Source) (t : (B j).Sink) :
    GlueEdge B R attach (.inr ⟨j,s⟩) ⟨j,t⟩ ↔ linearSupport (B j) s t := by
  constructor
  · intro h
    cases h with | internal j s t h => exact h
  · exact GlueEdge.internal j s t

theorem glue_edge_internal_other {I J : Type}
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    {j k : J} (h : j≠k) (s : (B j).Source) (t : (B k).Sink) :
    ¬GlueEdge B R attach (.inr ⟨j,s⟩) ⟨k,t⟩ := by
  intro he
  cases he
  exact h rfl

theorem glued_arrow_support_iff {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (s : I ⊕ (Σ j,(B j).Source)) (t : Σ j,(B j).Sink) :
    linearSupport (gluedBlock B R attach) s t ↔ GlueEdge B R attach s t := by
  have hid : (LinearMap.id : ℂ →ₗ[ℂ] ℂ)≠0 := by
    intro h
    have he := congrArg (fun f : ℂ →ₗ[ℂ] ℂ => f 1) h
    simp at he
  rcases t with ⟨j,t⟩
  cases s with
  | inl i =>
    rw [glue_edge_connector_iff]
    simp only [linearSupport]
    split_ifs <;> simp_all
  | inr p =>
    rcases p with ⟨k,s⟩
    by_cases h : k=j
    · subst k
      rw [glue_edge_internal_iff]
      simp [linearSupport, internalArrow]
    · simp [linearSupport, internalArrow, h,
        glue_edge_internal_other B R attach h]

def gluedGraph {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) := incidenceGraph (GlueEdge B R attach)

theorem glued_support_graph {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink) :
    supportGraph (gluedBlock B R attach)=gluedGraph B R attach := by
  unfold supportGraph gluedGraph
  congr 1
  funext s t
  exact propext (glued_arrow_support_iff B R attach s t)

def blockVertex {I J : Type} (B : J → LinearCoverBlock) (j : J) :
    ((B j).Source ⊕ (B j).Sink) → ((I ⊕ (Σ j,(B j).Source)) ⊕ (Σ j,(B j).Sink))
  | .inl s => .inl (.inr ⟨j,s⟩)
  | .inr t => .inr ⟨j,t⟩

def blockHom {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) (j : J) : supportGraph (B j) →g gluedGraph B R attach where
  toFun := blockVertex B j
  map_rel' := by
    intro u v h
    cases u with
    | inl s => cases v with
      | inl k => exact False.elim h
      | inr t => exact GlueEdge.internal j s t h
    | inr t => cases v with
      | inr k => exact False.elim h
      | inl s => exact GlueEdge.internal j s t h

theorem block_vertex_injective {I J : Type} (B : J → LinearCoverBlock) (j : J) :
    Function.Injective (blockVertex (I:=I) B j) := by
  intro u v h
  cases u <;> cases v <;> simp_all [blockVertex]

end KroneckerGluedSupportGraph
