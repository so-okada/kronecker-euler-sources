import KroneckerGluedSupportTree

/- Original module: KroneckerDeletedConnectorGraph -/
section
set_option autoImplicit false
namespace KroneckerDeletedConnectorGraph
open SimpleGraph KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedSupportGraph

abbrev RemainingVertex {J : Type} (B : J → LinearCoverBlock) := Σ j,(B j).Source ⊕ (B j).Sink

inductive BlockAdj {J : Type} (B : J → LinearCoverBlock) : RemainingVertex B → RemainingVertex B → Prop
  | internal (j : J) (u v : (B j).Source ⊕ (B j).Sink) (h : (supportGraph (B j)).Adj u v) :
      BlockAdj B ⟨j,u⟩ ⟨j,v⟩

def remainingGraph {J : Type} (B : J → LinearCoverBlock) : SimpleGraph (RemainingVertex B) where
  Adj := BlockAdj B
  symm := ⟨by intro u v h; cases h with | internal j u v h => exact .internal j v u h.symm⟩
  loopless := ⟨by intro u h; cases h with | internal j u u h => exact h.ne rfl⟩

def remainingEmbedding {I J : Type} (B : J → LinearCoverBlock) :
    RemainingVertex B → ((I ⊕ (Σ j,(B j).Source)) ⊕ (Σ j,(B j).Sink)) :=
  fun p => blockVertex B p.1 p.2

theorem remaining_embedding_injective {I J : Type} (B : J → LinearCoverBlock) :
    Function.Injective (remainingEmbedding (I:=I) B) := by
  rintro ⟨j,u⟩ ⟨k,v⟩ h
  cases u <;> cases v <;> simp_all [remainingEmbedding,blockVertex]
  all_goals rcases h with ⟨rfl,h⟩; cases h; rfl

theorem remaining_adj_iff {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) (u v : RemainingVertex B) :
    (gluedGraph B R attach).Adj (remainingEmbedding B u) (remainingEmbedding B v) ↔
      (remainingGraph B).Adj u v := by
  constructor
  · rcases u with ⟨j,u⟩
    rcases v with ⟨k,v⟩
    intro h
    have hjk : j=k := by
      by_contra hn
      cases u with
      | inl s => cases v with
        | inl t => exact h
        | inr t => exact glue_edge_internal_other B R attach hn s t h
      | inr s => cases v with
        | inr t => exact h
        | inl t => exact glue_edge_internal_other B R attach (Ne.symm hn) t s h
    subst k
    apply BlockAdj.internal
    cases u with
    | inl s => cases v with
      | inl t => exact h
      | inr t => exact (glue_edge_internal_iff B R attach j s t).mp h
    | inr s => cases v with
      | inr t => exact h
      | inl t => exact (glue_edge_internal_iff B R attach j t s).mp h
  · intro h
    cases h with
    | internal j u v h => exact (blockHom B R attach j).map_rel h


theorem remaining_walk_same_block {J : Type} (B : J → LinearCoverBlock)
    {u v : RemainingVertex B} (p : (remainingGraph B).Walk u v) : u.1=v.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => cases h with | internal j u v h => exact ih

end KroneckerDeletedConnectorGraph
end

/- Original module: KroneckerRecoveredBlockComponents -/
section
set_option autoImplicit false
namespace KroneckerRecoveredBlockComponents
open SimpleGraph KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerDeletedConnectorGraph

def componentBlockHom {J : Type} (B : J → LinearCoverBlock) (j : J) :
    supportGraph (B j) →g remainingGraph B where
  toFun v := ⟨j,v⟩
  map_rel' := fun h => BlockAdj.internal j _ _ h

/-- After deleting connectors, two surviving vertices are connected exactly
when they belong to the same original block. -/
theorem remaining_reachable_iff {J : Type} (B : J → LinearCoverBlock)
    (hB : ∀ j,(supportGraph (B j)).Connected) (u v : RemainingVertex B) :
    (remainingGraph B).Reachable u v ↔ u.1=v.1 := by
  constructor
  · rintro ⟨p⟩; exact remaining_walk_same_block B p
  · rcases u with ⟨j,u⟩
    rcases v with ⟨k,v⟩
    intro h
    dsimp at h
    subst k
    exact (hB j u v).map (componentBlockHom B j)

def recoveredBlockIndex {J : Type} (B : J → LinearCoverBlock) :
    (remainingGraph B).ConnectedComponent → J :=
  Quot.lift (fun v : RemainingVertex B => v.1) (by
    rintro u v ⟨p⟩; exact remaining_walk_same_block B p)

theorem recovered_index_bijective {J : Type} (B : J → LinearCoverBlock)
    (hB : ∀ j,(supportGraph (B j)).Connected) : Function.Bijective (recoveredBlockIndex B) := by
  constructor
  · intro x y
    refine ConnectedComponent.ind₂ ?_ x y
    intro u v h
    exact ConnectedComponent.sound ((remaining_reachable_iff B hB u v).mpr h)
  · intro j
    let v := Classical.choice (hB j).nonempty
    exact ⟨(remainingGraph B).connectedComponentMk ⟨j,v⟩,rfl⟩

noncomputable def recoveredBlockEquiv {J : Type} (B : J → LinearCoverBlock)
    (hB : ∀ j,(supportGraph (B j)).Connected) : (remainingGraph B).ConnectedComponent ≃ J :=
  Equiv.ofBijective (recoveredBlockIndex B) (recovered_index_bijective B hB)


end KroneckerRecoveredBlockComponents
end
