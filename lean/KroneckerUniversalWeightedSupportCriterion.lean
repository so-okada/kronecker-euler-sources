import KroneckerDimensionedCoverIsomorphisms
import KroneckerDirectSumWordEvaluation
import KroneckerWeightedSupportDeckCriterion

/- Original module: KroneckerActualDeckIsomorphismClasses -/
section
/-! Actual deck-and-isomorphism equivalence of dimensioned cover representations.
This relation uses commuting linear equivalences, not only dimension labels. -/
set_option autoImplicit false
namespace KroneckerActualDeckIsomorphismClasses
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerDimensionedCoverIsomorphisms
open KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses

theorem deck_ext {g h : Deck} (he : g.equiv = h.equiv) : g = h := by
  cases g
  cases h
  cases he
  rfl

theorem deck_symm_trans (g : Deck) : Deck.trans (Deck.symm g) g = Deck.refl := by
  apply deck_ext
  apply Equiv.ext
  intro w
  exact g.equiv.apply_symm_apply w


def DeckIso (S T : SupportedRepresentation coloredCoverQuiver) : Prop :=
  ∃ g : Deck, Nonempty (AcrossIso (deckPull g S) T)

theorem deckIso_refl (S : SupportedRepresentation coloredCoverQuiver) : DeckIso S S := by
  refine ⟨Deck.refl, ?_⟩
  rw [deckPull_refl]
  exact ⟨AcrossIso.refl S⟩

theorem deckIso_symm {S T : SupportedRepresentation coloredCoverQuiver} (h : DeckIso S T) :
    DeckIso T S := by
  obtain ⟨g, ⟨e⟩⟩ := h
  refine ⟨Deck.symm g, ?_⟩
  have ep := pullAcrossIso (deckQuiverAuto (Deck.symm g)) e.symm
  change AcrossIso (deckPull (Deck.symm g) T) (deckPull (Deck.symm g) (deckPull g S)) at ep
  rw [← deckPull_trans, deck_symm_trans, deckPull_refl] at ep
  exact ⟨ep⟩

theorem deckIso_trans {S T U : SupportedRepresentation coloredCoverQuiver}
    (hST : DeckIso S T) (hTU : DeckIso T U) : DeckIso S U := by
  obtain ⟨g, ⟨e⟩⟩ := hST
  obtain ⟨h, ⟨f⟩⟩ := hTU
  refine ⟨Deck.trans h g, ?_⟩
  have ep := pullAcrossIso (deckQuiverAuto h) e
  change AcrossIso (deckPull h (deckPull g S)) (deckPull h T) at ep
  rw [← deckPull_trans] at ep
  exact ⟨ep.trans f⟩

def actualDeckSetoid : Setoid (SupportedRepresentation coloredCoverQuiver) where
  r := DeckIso
  iseqv := ⟨deckIso_refl, deckIso_symm, deckIso_trans⟩

theorem deckIso_dimension_relation {S T : SupportedRepresentation coloredCoverQuiver}
    (h : DeckIso S T) : dimensionSetoid.r S.1 T.1 := by
  obtain ⟨g, ⟨e⟩⟩ := h
  refine ⟨Deck.symm g, ?_⟩
  intro w
  have hw := congrArg (fun d => d (g.equiv.symm w)) e.dimension_eq
  change S.1 (g.equiv (g.equiv.symm w)) = T.1 (g.equiv.symm w) at hw
  rw [Equiv.apply_symm_apply] at hw
  exact hw.symm


end KroneckerActualDeckIsomorphismClasses
end

/- Original module: KroneckerUniversalColoredMapRigidity -/
section
/-! Agreement at a single vertex propagates along every actual typed walk
for two maps into the universal word quiver preserving arrow colors. The
argument treats forward and backward traversal separately and retains the
actual arrow map, not only an underlying uncolored graph map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalColoredMapRigidity
open KroneckerAbelianCover KroneckerReducedColorWords KroneckerTypedQuiverMaps
open KroneckerFiniteSupportDeckRepresentationTransport LabeledWalk
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P : TypedQuiver}

theorem map_target_toggle (f : QuiverMap P coloredCoverQuiver) (a : P.A) :
    f.vertex (P.target a) = toggle (f.arrow a).1 (f.vertex (P.source a)) := by
  exact (f.target a).symm.trans (congrArg (toggle (f.arrow a).1) (f.source a))

theorem walk_agreement (f g : QuiverMap P coloredCoverQuiver)
    (hc : ∀ a, (f.arrow a).1 = (g.arrow a).1) {u v : P.V}
    (p : LabeledWalk P.source P.target u v) (h : f.vertex u = g.vertex u) : f.vertex v = g.vertex v := by
  induction p with
  | nil => exact h
  | forward a p ih =>
    apply ih
    rw [map_target_toggle,map_target_toggle,hc a,h]
  | backward a p ih =>
    apply ih
    apply toggle_injective (f.arrow a).1
    rw [← map_target_toggle, hc a, ← map_target_toggle]
    exact h

theorem arrow_agreement (f g : QuiverMap P coloredCoverQuiver)
    (hc : ∀ a, (f.arrow a).1 = (g.arrow a).1) (hv : ∀ v, f.vertex v = g.vertex v) :
    ∀ a, f.arrow a = g.arrow a := by
  intro a
  apply Prod.ext (hc a)
  apply Subtype.ext
  exact (f.source a).trans ((hv (P.source a)).trans (g.source a).symm)

end KroneckerUniversalColoredMapRigidity
end
end

/- Original module: KroneckerUniversalDeckRootTorsor -/
section
/-! Universal colored deck transformations act freely and transitively on
each parity fiber. Equality at ANY chosen root determines the complete deck
action, and each equal-parity root pair has a unique transporting deck map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalDeckRootTorsor
open KroneckerReducedColorWords KroneckerColorWordAction KroneckerCoverDeckTranslations
open KroneckerWordParity KroneckerActualDeckIsomorphismClasses KroneckerWordTranslations

theorem deck_ext_at (g h : Deck) (r : Word) (he : g r = h r) : g = h := by
  have hr : g root = h root := by
    apply act_injective r.val
    change translate (g root) r = translate (h root) r
    rwa [← deck_determined_by_root,← deck_determined_by_root]
  apply deck_ext
  apply Equiv.ext
  intro w
  exact (deck_determined_by_root g w).trans
    ((congrArg (fun t => translate t w) hr).trans (deck_determined_by_root h w).symm)




end KroneckerUniversalDeckRootTorsor
end
end

/- Original module: KroneckerUniversalConnectedMapDeck -/
section
/-! Any two connected colored realizations in the universal directed word
quiver, with equally typed chosen roots, differ by a UNIQUE even deck action.
The action agrees on every vertex and actual arrow, giving the universal
counterpart of the checked direct-sum connected-map extension theorem. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalConnectedMapDeck
open KroneckerAbelianCover LabeledWalk KroneckerTypedQuiverMaps
open KroneckerReducedColorWords KroneckerWordParity KroneckerCoverDeckTranslations
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerUniversalColoredMapRigidity
open KroneckerUniversalDeckRootTorsor
attribute [local instance] Classical.decEq Classical.propDecidable

def deckMap (g : Deck) : QuiverMap coloredCoverQuiver coloredCoverQuiver :=
  ⟨g.equiv,(deckQuiverAuto g).arrowEquiv,(deckQuiverAuto g).map_source,(deckQuiverAuto g).map_target⟩

theorem connected_maps_deck (P : TypedQuiver) (f g : QuiverMap P coloredCoverQuiver) (r : P.V)
    (hc : ∀ v, Nonempty (LabeledWalk P.source P.target r v))
    (hr : parity (f.vertex r) = parity (g.vertex r))
    (ha : ∀ a, (f.arrow a).1 = (g.arrow a).1) :
    ∃! k : Deck, (∀ v, k (f.vertex v) = g.vertex v) ∧
      (∀ a, (deckQuiverAuto k).arrowEquiv (f.arrow a) = g.arrow a) := by
  obtain ⟨k,hk⟩ := deck_transitive_same_parity hr
  have hv : ∀ v, k (f.vertex v) = g.vertex v := by
    intro v
    obtain ⟨p⟩ := hc v
    exact walk_agreement (f.comp (deckMap k)) g ha p hk
  refine ⟨k,⟨hv,arrow_agreement (f.comp (deckMap k)) g ha hv⟩,?_⟩
  intro l hl
  exact deck_ext_at l k (f.vertex r) ((hl.1 r).trans (hv r).symm)

end KroneckerUniversalConnectedMapDeck
end
end

/- Original module: KroneckerUniversalWeightedSupportCriterion -/
section
/-! For connected word supports, weighted full-support isomorphisms preserving
parity and actual colors are equivalent to universal deck dimension relations.
Outside-support vertices are checked explicitly, so the result concerns the
complete finitely supported functions, not just their positive restrictions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalWeightedSupportCriterion
open KroneckerAbelianCover LabeledWalk KroneckerReducedColorWords KroneckerWordParity
open KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses KroneckerTypedQuiverMaps
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedSupportDeckCriterion KroneckerUniversalConnectedMapDeck
open KroneckerQuiverSupportEulerTransport
attribute [local instance] Classical.decEq Classical.propDecidable

structure WeightedIso (d e : Word →₀ ℕ) where
  iso : TypedQuiverIso (supportQuiver coloredCoverQuiver d) (supportQuiver coloredCoverQuiver e)
  weight : ∀ v, e (iso.vertexEquiv v).val = d v.val
  parity_label : ∀ v, parity (iso.vertexEquiv v).val = parity v.val
  color_label : ∀ a, (iso.arrowEquiv a).val.1 = a.val.1

theorem weightedIso_dimension_relation (d e : Word →₀ ℕ)
    (hc : SupportConnected coloredCoverQuiver d) (j : WeightedIso d e) : dimensionSetoid d e := by
  obtain ⟨r,hc⟩ := hc
  let P := supportQuiver coloredCoverQuiver d
  let f : QuiverMap P coloredCoverQuiver := ⟨Subtype.val,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  let g : QuiverMap P coloredCoverQuiver :=
    ⟨fun v => (j.iso.vertexEquiv v).val,fun a => (j.iso.arrowEquiv a).val,
      fun a => congrArg Subtype.val (j.iso.map_source a),fun a => congrArg Subtype.val (j.iso.map_target a)⟩
  obtain ⟨k,hk,_⟩ := connected_maps_deck P f g r hc (j.parity_label r).symm
    (fun a => (j.color_label a).symm)
  refine ⟨k,fun v => ?_⟩
  by_cases hv : v ∈ d.support
  · exact (congrArg e (hk.1 ⟨v,hv⟩)).trans (j.weight ⟨v,hv⟩)
  · rw [Finsupp.notMem_support_iff.mp hv]
    by_contra he
    let w : SupportVertex e := ⟨k v,Finsupp.mem_support_iff.mpr he⟩
    obtain ⟨u,hu⟩ := j.iso.vertexEquiv.surjective w
    have hku : k u.val = k v := (hk.1 u).trans (congrArg Subtype.val hu)
    exact hv ((k.equiv.injective hku) ▸ u.property)

theorem dimension_relation_weightedIso {d e : Word →₀ ℕ} (h : dimensionSetoid d e) : Nonempty (WeightedIso d e) := by
  obtain ⟨g,hg⟩ := h
  have hd : pullDimension (deckQuiverAuto g) e = d := by
    ext w
    exact hg w
  rw [← hd]
  refine ⟨⟨supportQuiverIso (deckQuiverAuto g) e,?_,?_,?_⟩⟩
  · intro v
    rfl
  · intro v
    exact g.preserves_parity v.val
  · intro a
    rfl


end KroneckerUniversalWeightedSupportCriterion
end
end
