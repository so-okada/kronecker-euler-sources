import KroneckerUniversalWeightedSupportCriterion
import KroneckerColoredAmbientPullSupport
import KroneckerUniversalToDirectStableRealization
import KroneckerUniversalEulerRealization

/- Original module: KroneckerDirectSumConnectedMapRigidity -/
section
/-! Connected labeled realizations in the genuine direct-sum iterated cover
differ by a unique direct-sum accumulated deck transformation. The proof
restricts the product transformation using the actual chosen root, then
identifies every vertex and every arrow through the faithful embedding. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumConnectedMapRigidity
open KroneckerAbelianCover LabeledWalk KroneckerTypedQuiverMaps
open KroneckerDirectSumIteratedEmbedding KroneckerDirectSumAccumulatedActions
open KroneckerDirectSumAccumulatedRestriction KroneckerDirectSumDeckRootTorsor
attribute [local instance] Classical.decEq Classical.propDecidable

theorem connected_maps_deck (Q P : TypedQuiver) (n : ℕ)
    (f g : QuiverMap P (KroneckerDirectSumIteratedGirth.iterate Q n)) (r : P.V)
    (hc : ∀ v, Nonempty (LabeledWalk P.source P.target r v))
    (hr : baseVertex Q n (f.vertex r) = baseVertex Q n (g.vertex r))
    (ha : ∀ a, baseArrow Q n (f.arrow a) = baseArrow Q n (g.arrow a)) :
    ∃! k : Deck Q n, (∀ v, k.val.vertexEquiv (f.vertex v) = g.vertex v) ∧
      (∀ a, k.val.arrowEquiv (f.arrow a) = g.arrow a) := by
  obtain ⟨F,hF,_⟩ := KroneckerAccumulatedConnectedMapRigidity.connected_maps_deck Q P n
    (f.comp (embedding Q n)) (g.comp (embedding Q n)) r hc
    (by simpa only [QuiverMap.comp,Function.comp_apply,embedding_base_vertex] using hr)
    (by intro a; simpa only [QuiverMap.comp,Function.comp_apply,embedding_base_arrow] using ha a)
  obtain ⟨k,hk⟩ := exists_restriction Q n F.val F.property (f.vertex r) (g.vertex r) (hF.1 r)
  have hv : ∀ v, k.val.vertexEquiv (f.vertex v) = g.vertex v := by
    intro v
    exact (embedding_injective Q n).1 ((hk.1 (f.vertex v)).symm.trans (hF.1 v))
  refine ⟨k,⟨hv,?_⟩,?_⟩
  · intro a
    exact (embedding_injective Q n).2 ((hk.2 (f.arrow a)).symm.trans (hF.2 a))
  · intro l hl
    exact deck_ext_at Q n l k (f.vertex r) ((hl.1 r).trans (hv r).symm)

end KroneckerDirectSumConnectedMapRigidity
end
end

/- Original module: KroneckerDirectSumWeightedSupportCriterion -/
section
/-! In the precise direct-sum model, a connected weighted full-support isomorphism preserving original vertex and
arrow labels extends to an accumulated deck transformation. Conversely every
accumulated dimension relation gives exactly such a full support isomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumWeightedSupportCriterion
open KroneckerAbelianCover LabeledWalk
open KroneckerDirectSumIteratedEmbedding KroneckerWeightedSupportDeckCriterion
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerTypedQuiverMaps KroneckerDirectSumAccumulatedActions
open KroneckerDirectSumConnectedMapRigidity KroneckerDirectSumDimensionClasses
open KroneckerDirectSumDeckRootTorsor KroneckerQuiverSupportEulerTransport
attribute [local instance] Classical.decEq Classical.propDecidable

structure WeightedIso (Q : TypedQuiver) (n : ℕ) (d e : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ) where
  iso : TypedQuiverIso (supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q n) d) (supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q n) e)
  weight : ∀ v, e (iso.vertexEquiv v).val = d v.val
  vertex_label : ∀ v, baseVertex Q n (iso.vertexEquiv v).val = baseVertex Q n v.val
  arrow_label : ∀ a, baseArrow Q n (iso.arrowEquiv a).val = baseArrow Q n a.val

theorem weightedIso_deck (Q : TypedQuiver) (n : ℕ) (d e : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ)
    (hc : SupportConnected (KroneckerDirectSumIteratedGirth.iterate Q n) d) (j : WeightedIso Q n d e) : Related Q n e d := by
  obtain ⟨r,hc⟩ := hc
  let P := supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q n) d
  let f : QuiverMap P (KroneckerDirectSumIteratedGirth.iterate Q n) := ⟨Subtype.val,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  let g : QuiverMap P (KroneckerDirectSumIteratedGirth.iterate Q n) :=
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
    let w : (supportQuiver (KroneckerDirectSumIteratedGirth.iterate Q n) e).V := ⟨k.val.vertexEquiv v,Finsupp.mem_support_iff.mpr he⟩
    obtain ⟨u,hu⟩ := j.iso.vertexEquiv.surjective w
    have hku : k.val.vertexEquiv u.val = k.val.vertexEquiv v :=
      (hk.1 u).trans (congrArg Subtype.val hu)
    exact hv ((k.val.vertexEquiv.injective hku) ▸ u.property)

theorem deck_weightedIso (Q : TypedQuiver) (n : ℕ) {d e : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ}
    (h : Related Q n e d) : Nonempty (WeightedIso Q n d e) := by
  obtain ⟨f,rfl⟩ := h
  refine ⟨⟨supportQuiverIso f.val e,?_,?_,?_⟩⟩
  · intro v
    exact (pullDimension_apply f.val e v.val).symm
  · intro v
    exact vertex_base_invariant Q n f v.val
  · intro a
    exact arrow_base_invariant Q n f a.val

theorem weightedIso_iff_deck (Q : TypedQuiver) (n : ℕ) (d e : (KroneckerDirectSumIteratedGirth.iterate Q n).V →₀ ℕ)
    (hc : SupportConnected (KroneckerDirectSumIteratedGirth.iterate Q n) d) :
    Nonempty (WeightedIso Q n d e) ↔ Related Q n e d :=
  ⟨fun ⟨j⟩ => weightedIso_deck Q n d e hc j,deck_weightedIso Q n⟩

end KroneckerDirectSumWeightedSupportCriterion
end
end

/- Original module: KroneckerColoredSupportDeckRelations -/
section
/-! The common weighted-colored support relation agrees with the previously
proved genuine direct-sum and universal-word deck dimension relations on
connected supports. The direct relation's contravariant direction is handled
explicitly; source/sink side equality recovers equality of original Fin2 labels. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerColoredSupportDeckRelations
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerWeightedColoredSupportIso
open KroneckerWeightedSupportDeckCriterion KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerReducedColorWords
attribute [local instance] Classical.decEq Classical.propDecidable

def directWeightedIso (n : ℕ)
    {d e : (KroneckerDirectSumIteratedGirth.iterate baseQuiver n).V →₀ ℕ}
    (f : ColoredIso (KroneckerDirectSumBaseColoring.coloring n) (KroneckerDirectSumBaseColoring.coloring n) d e) :
    KroneckerDirectSumWeightedSupportCriterion.WeightedIso baseQuiver n d e :=
  ⟨f.iso,f.weight,fun v => Fin.ext (f.side v),f.color⟩

def directColoredIso (n : ℕ)
    {d e : (KroneckerDirectSumIteratedGirth.iterate baseQuiver n).V →₀ ℕ}
    (f : KroneckerDirectSumWeightedSupportCriterion.WeightedIso baseQuiver n d e) :
    ColoredIso (KroneckerDirectSumBaseColoring.coloring n) (KroneckerDirectSumBaseColoring.coloring n) d e :=
  ⟨f.iso,f.weight,fun v => congrArg Fin.val (f.vertex_label v),f.arrow_label⟩

theorem direct_relation_iff_colored (n : ℕ)
    (d e : (KroneckerDirectSumIteratedGirth.iterate baseQuiver n).V →₀ ℕ)
    (hc : SupportConnected (KroneckerDirectSumIteratedGirth.iterate baseQuiver n) d) :
    KroneckerDirectSumDimensionClasses.Related baseQuiver n d e ↔
      Nonempty (ColoredIso (KroneckerDirectSumBaseColoring.coloring n) (KroneckerDirectSumBaseColoring.coloring n) d e) := by
  constructor
  · intro h
    obtain ⟨f⟩ := KroneckerDirectSumWeightedSupportCriterion.deck_weightedIso baseQuiver n
      ((KroneckerDirectSumDimensionClasses.dimensionSetoid baseQuiver n).symm h)
    exact ⟨directColoredIso n f⟩
  · rintro ⟨f⟩
    exact (KroneckerDirectSumDimensionClasses.dimensionSetoid baseQuiver n).symm
      (KroneckerDirectSumWeightedSupportCriterion.weightedIso_deck baseQuiver n d e hc (directWeightedIso n f))

theorem word_relation_iff_colored (d e : Word →₀ ℕ) (hc : SupportConnected coloredCoverQuiver d) :
    KroneckerDeckDimensionClasses.dimensionSetoid d e ↔
      Nonempty (ColoredIso KroneckerUniversalWordBaseProjection.coloring KroneckerUniversalWordBaseProjection.coloring d e) := by
  constructor
  · intro h
    obtain ⟨f⟩ := KroneckerUniversalWeightedSupportCriterion.dimension_relation_weightedIso h
    exact ⟨⟨f.iso,f.weight,f.parity_label,f.color_label⟩⟩
  · rintro ⟨f⟩
    exact KroneckerUniversalWeightedSupportCriterion.weightedIso_dimension_relation d e hc
      ⟨f.iso,f.weight,f.side,f.color⟩

end KroneckerColoredSupportDeckRelations
end
end

/- Original module: KroneckerTransportCompleteSupportIso -/
section
/-! The complete support of a transported actual representation is EXACTLY
the embedded original full support. Explicit vertex and actual-arrow
bijections make a typed quiver isomorphism; positivity and full-on-image
surjectivity rule out extra vertices or extra internal arrows. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTransportCompleteSupportIso
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFullImagePushforward KroneckerFiniteSupportFullInclusion
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerFullSupportRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q W : TypedQuiver} (S : SupportedRepresentation Q)
  (f : QuiverMap (supportQuiver Q S.1) W) (hv : Function.Injective f.vertex)
  (ha : Function.Injective f.arrow) (hf : FullOnImage f)

def vertexMap (v : SupportVertex S.1) : SupportVertex (transport S f hv ha hf).1 :=
  ⟨f.vertex v,by
    rw [Finsupp.mem_support_iff,transport_dimension]
    exact Finsupp.mem_support_iff.mp v.property⟩

theorem vertexMap_bijective : Function.Bijective (vertexMap S f hv ha hf) := by
  constructor
  · intro v w h
    exact hv (congrArg Subtype.val h)
  · intro w
    obtain ⟨v,hv⟩ := push_image f hv ha hf (restricted Q S) w.property
    exact ⟨v,Subtype.ext hv⟩

def arrowMap (a : (supportQuiver Q S.1).A) :
    (supportQuiver W (transport S f hv ha hf).1).A :=
  ⟨f.arrow a,by
    constructor
    · rw [f.source]
      exact (vertexMap S f hv ha hf ((supportQuiver Q S.1).source a)).property
    · rw [f.target]
      exact (vertexMap S f hv ha hf ((supportQuiver Q S.1).target a)).property⟩

theorem arrowMap_bijective : Function.Bijective (arrowMap S f hv ha hf) := by
  constructor
  · intro a b h
    exact ha (congrArg Subtype.val h)
  · intro a
    obtain ⟨u,hu⟩ := (vertexMap_bijective S f hv ha hf).2 ((supportQuiver W (transport S f hv ha hf).1).source a)
    obtain ⟨v,hv'⟩ := (vertexMap_bijective S f hv ha hf).2 ((supportQuiver W (transport S f hv ha hf).1).target a)
    obtain ⟨b,hb⟩ := hf a.val u v (congrArg Subtype.val hu).symm (congrArg Subtype.val hv').symm
    exact ⟨b,Subtype.ext hb⟩

def supportIso : TypedQuiverIso (supportQuiver Q S.1) (supportQuiver W (transport S f hv ha hf).1) where
  vertexEquiv := Equiv.ofBijective (vertexMap S f hv ha hf) (vertexMap_bijective S f hv ha hf)
  arrowEquiv := Equiv.ofBijective (arrowMap S f hv ha hf) (arrowMap_bijective S f hv ha hf)
  map_source a := Subtype.ext (f.source a)
  map_target a := Subtype.ext (f.target a)

theorem supportIso_weight (v : SupportVertex S.1) :
    (transport S f hv ha hf).1 ((supportIso S f hv ha hf).vertexEquiv v).val = S.1 v.val :=
  transport_dimension S f hv ha hf v

end KroneckerTransportCompleteSupportIso
end
end

/- Original module: KroneckerTransportColoredSupportIso -/
section
/-! A full support embedding preserving sides and actual colors gives an
explicit weighted colored isomorphism onto the COMPLETE transported support.
This strengthens mere two-way realization to the concrete relation needed
for choice-independent quotient maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTransportColoredSupportIso
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerProperBipartiteQuiver KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportInducedQuiver KroneckerFullSupportRepresentationTransport
open KroneckerWeightedColoredSupportIso KroneckerTransportCompleteSupportIso
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q W : TypedQuiver} (C : Coloring Q) (D : Coloring W) (S : SupportedRepresentation Q)
  (f : QuiverMap (supportQuiver Q S.1) W) (hv : Function.Injective f.vertex)
  (ha : Function.Injective f.arrow) (hf : FullOnImage f)

def transportColoredIso (hs : ∀ v, D.side (f.vertex v) = C.side v.val)
    (hc : ∀ a, D.color (f.arrow a) = C.color a.val) :
    ColoredIso C D S.1 (transport S f hv ha hf).1 where
  iso := supportIso S f hv ha hf
  weight := supportIso_weight S f hv ha hf
  side := hs
  color := hc


end KroneckerTransportColoredSupportIso
end
end

/- Original module: KroneckerDirectColoredRealization -/
section
/-! The reverse stable realization retains an explicit weighted colored
isomorphism from the ORIGINAL universal support to the realized direct-sum
support. Its construction composes the actual normalization deck support map
with the full bounded-evaluation support map; no arbitrary matching is assumed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectColoredRealization
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerFullSupportRepresentationTransport KroneckerWeightedColoredSupportIso
open KroneckerTransportColoredSupportIso KroneckerDirectSumBoundedWordEmbedding
open KroneckerUniversalStableNormalization KroneckerColoredAmbientPullSupport
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_colored_realization (B : ℕ) (S : SupportedRepresentation coloredCoverQuiver)
    (hS : S.1 ≠ 0) (hB : S.1.sum (fun _ k => k) ≤ B) (θ : Fin 2 → ℤ)
    (hstable : FiniteSupportStable S.1 (θ ∘ KroneckerUniversalWordBaseProjection.baseVertex) S.2) :
    ∃ T : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)),
      T.1 ≠ 0 ∧ T.1.sum (fun _ k => k) ≤ B ∧
      FiniteSupportStable T.1 (θ ∘ KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B)) T.2 ∧
      Nonempty (ColoredIso KroneckerUniversalWordBaseProjection.coloring
        (KroneckerDirectSumBaseColoring.coloring (depth B)) S.1 T.1) := by
  obtain ⟨g,hn,ht,hD,hs,hball⟩ := exists_normalized_pull S hS θ hstable
  let N := deckPull g S
  obtain ⟨hv,ha,hf⟩ := boundedMap_embedding B N.1 (fun w hw => (hball w hw).trans hB)
  let f := boundedMap B N.1
  have hbase : ∀ v, KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B) (f.vertex v) =
      KroneckerUniversalWordBaseProjection.baseVertex v.val := fun v =>
    KroneckerDirectSumWordEvaluation.wordMap_base (depth B) v.val
  refine ⟨transport N f hv ha hf,(not_congr (transport_zero_iff N f hv ha hf)).mpr hn,?_,?_,?_⟩
  · rw [transport_sum,ht]
    exact hB
  · exact (transport_stable_iff N f hv ha hf _ _ (fun v => congrArg θ (hbase v))).mpr hs
  · exact ⟨(wordDeckPullIso g S).symm.trans
      (transportColoredIso _ _ N f hv ha hf (fun v => congrArg Fin.val (hbase v))
        (fun a => KroneckerDirectSumWordEvaluation.wordMap_color (depth B) a.val))⟩

end KroneckerDirectColoredRealization
end
end

/- Original module: KroneckerUniversalColoredRealization -/
section
/-! The forward stable realization comes with an explicit weighted colored
isomorphism between the complete original and realized support quivers. This
records exactly how its dimension index relates across models, retaining
full actual arrows, multiplicities and bipartition. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalColoredRealization
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability KroneckerFiniteSupportEulerTransport
open KroneckerFullSupportRepresentationTransport KroneckerWeightedColoredSupportIso
open KroneckerTransportColoredSupportIso
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_colored_realization (B : ℕ)
    (S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)))
    (hS : S.1 ≠ 0) (hB : S.1.sum (fun _ k => k) ≤ B) (θ : Fin 2 → ℤ)
    (hstable : FiniteSupportStable S.1 (θ ∘ KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B)) S.2) :
    ∃ T : SupportedRepresentation coloredCoverQuiver,
      T.1 ≠ 0 ∧ T.1.sum (fun _ k => k) ≤ B ∧
      FiniteSupportStable T.1 (θ ∘ KroneckerUniversalWordBaseProjection.baseVertex) T.2 ∧
      Nonempty (ColoredIso (KroneckerDirectSumBaseColoring.coloring (depth B))
        KroneckerUniversalWordBaseProjection.coloring S.1 T.1) := by
  obtain ⟨f,hv,ha,hf,hpar,hcolor⟩ := exists_full_colored_support_embedding B S.1 hS hB _ S.2 hstable
  have hb : ∀ v, KroneckerUniversalWordBaseProjection.baseVertex (f.vertex v) =
      KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B) v.val := fun v => Fin.ext (hpar v)
  refine ⟨transport S f hv ha hf,(not_congr (transport_zero_iff S f hv ha hf)).mpr hS,?_,?_,?_⟩
  · rw [transport_sum]
    exact hB
  · exact (transport_stable_iff S f hv ha hf _ _ (fun v => congrArg θ (hb v))).mpr hstable
  · exact ⟨transportColoredIso _ _ S f hv ha hf hpar hcolor⟩

end KroneckerUniversalColoredRealization
end
end

/- Original module: KroneckerStableColoredRepresentatives -/
section
/-! Stable dimension-index representatives keep an actual nonzero stable
representation witnessing membership. The equivalence relations identify
only deck-equivalent DIMENSIONS, and are proved equivalent to weighted
colored support isomorphism using stability-derived connectedness. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableColoredRepresentatives
open KroneckerAbelianCover KroneckerThreeArrowBaseQuiver KroneckerDirectSumUniversalSupportEmbedding
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteSupportStability KroneckerWeightedColoredSupportIso
open KroneckerColoredSupportDeckRelations
attribute [local instance] Classical.decEq Classical.propDecidable

def DirectStable (B : ℕ) (θ : Fin 2 → ℤ) :=
  {S : SupportedRepresentation (KroneckerDirectSumIteratedGirth.iterate baseQuiver (depth B)) //
    S.1 ≠ 0 ∧ S.1.sum (fun _ k => k) ≤ B ∧
    FiniteSupportStable S.1 (θ ∘ KroneckerDirectSumIteratedEmbedding.baseVertex baseQuiver (depth B)) S.2}

def WordStable (B : ℕ) (θ : Fin 2 → ℤ) :=
  {S : SupportedRepresentation coloredCoverQuiver // S.1 ≠ 0 ∧ S.1.sum (fun _ k => k) ≤ B ∧
    FiniteSupportStable S.1 (θ ∘ KroneckerUniversalWordBaseProjection.baseVertex) S.2}

def directSetoid (B : ℕ) (θ : Fin 2 → ℤ) : Setoid (DirectStable B θ) :=
  Setoid.comap (fun S => S.val.1) (KroneckerDirectSumDimensionClasses.dimensionSetoid baseQuiver (depth B))

def wordSetoid (B : ℕ) (θ : Fin 2 → ℤ) : Setoid (WordStable B θ) :=
  Setoid.comap (fun S => S.val.1) KroneckerDeckDimensionClasses.dimensionSetoid

theorem direct_related_iff_colored (B : ℕ) (θ : Fin 2 → ℤ) (S T : DirectStable B θ) :
    directSetoid B θ S T ↔ Nonempty (ColoredIso (KroneckerDirectSumBaseColoring.coloring (depth B))
      (KroneckerDirectSumBaseColoring.coloring (depth B)) S.val.1 T.val.1) :=
  direct_relation_iff_colored _ _ _ (KroneckerDirectSumStableSupportTree.stable_support_connected _ _ S.property.1 _ _ S.property.2.2)

theorem word_related_iff_colored (B : ℕ) (θ : Fin 2 → ℤ) (S T : WordStable B θ) :
    wordSetoid B θ S T ↔ Nonempty (ColoredIso KroneckerUniversalWordBaseProjection.coloring
      KroneckerUniversalWordBaseProjection.coloring S.val.1 T.val.1) :=
  word_relation_iff_colored _ _ (KroneckerDirectSumStableSupportTree.stable_support_connected _ _ S.property.1 _ _ S.property.2.2)

end KroneckerStableColoredRepresentatives
end
end
