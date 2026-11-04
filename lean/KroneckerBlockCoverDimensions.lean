import KroneckerTreeInducedEmbedding
import KroneckerDeckDimensionClasses
import KroneckerDimensionedSupportClasses

/- Original module: KroneckerIncidenceEdgeColoring -/
section
set_option autoImplicit false
namespace KroneckerIncidenceEdgeColoring
open KroneckerProperColoredReflection KroneckerBipartiteIncidence
open KroneckerGraphColorWords KroneckerReducedColorWords

variable {I J : Type} {R : I → J → Prop}

def incidenceColor (C : ProperColoring R) :
    ∀ {u v : I ⊕ J}, (incidenceGraph R).Adj u v → Color
  | .inl i, .inr j, h => C.color i j h
  | .inr j, .inl i, h => C.color i j h
  | .inl _, .inl _, h => False.elim h
  | .inr _, .inr _, h => False.elim h

def incidenceColoring (C : ProperColoring R) : EdgeColoring (incidenceGraph R) where
  color := incidenceColor C
  symm := by
    intro u v h
    cases u <;> cases v
    · exact False.elim h
    · rfl
    · rfl
    · exact False.elim h
  proper := by
    intro u v w h k hc
    cases u with
    | inl i =>
      cases v with
      | inl i' => exact False.elim h
      | inr j =>
        cases w with
        | inl i' => exact False.elim k
        | inr j' =>
          exact congrArg Sum.inr (congrArg Subtype.val
            (C.at_source i (a₁ := ⟨j,h⟩) (a₂ := ⟨j',k⟩) hc))
    | inr j =>
      cases v with
      | inr j' => exact False.elim h
      | inl i =>
        cases w with
        | inr j' => exact False.elim k
        | inl i' =>
          exact congrArg Sum.inl (congrArg Subtype.val
            (C.at_sink j (a₁ := ⟨i,h⟩) (a₂ := ⟨i',k⟩) hc))

def side : I ⊕ J → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem side_step {u v : I ⊕ J} (h : (incidenceGraph R).Adj u v) :
    side u = (side v + 1) % 2 := by
  cases u <;> cases v
  · exact False.elim h
  · norm_num [side]
  · norm_num [side]
  · exact False.elim h

theorem walk_side {u v : I ⊕ J} (p : (incidenceGraph R).Walk u v) :
    side u = (p.length + side v) % 2 := by
  induction p with
  | @nil u => cases u <;> norm_num [side]
  | cons h p ih =>
    have hs := side_step h
    rw [ih] at hs
    simp only [SimpleGraph.Walk.length_cons]
    omega

end KroneckerIncidenceEdgeColoring
end

/- Original module: KroneckerBipartiteEquivSplit -/
section
set_option autoImplicit false
namespace KroneckerBipartiteEquivSplit
open KroneckerIncidenceEdgeColoring

theorem side_preserving_equiv_splits {I J I' J' : Type} (e : (I ⊕ J) ≃ (I' ⊕ J'))
    (he : ∀ v, side (e v) = side v) :
    ∃ (s : I ≃ I') (t : J ≃ J'), ∀ v, Equiv.sumCongr s t v = e v := by
  classical
  have hl (i : I) : ∃ j, e (.inl i) = .inl j := by
    cases h : e (.inl i) with
    | inl j => exact ⟨j,rfl⟩
    | inr j => have hh := he (.inl i); simp [h,side] at hh
  have hr (j : J) : ∃ i, e (.inr j) = .inr i := by
    cases h : e (.inr j) with
    | inr i => exact ⟨i,rfl⟩
    | inl i => have hh := he (.inr j); simp [h,side] at hh
  choose s hs using hl
  choose t ht using hr
  have si : Function.Injective s := by
    intro i j h
    exact Sum.inl.inj (e.injective ((hs i).trans ((congrArg Sum.inl h).trans (hs j).symm)))
  have ti : Function.Injective t := by
    intro i j h
    exact Sum.inr.inj (e.injective ((ht i).trans ((congrArg Sum.inr h).trans (ht j).symm)))
  have ss : Function.Surjective s := by
    intro i
    obtain ⟨v,hv⟩ := e.surjective (.inl i)
    cases v with
    | inl j => exact ⟨j,Sum.inl.inj ((hs j).symm.trans hv)⟩
    | inr j => have hh := he (.inr j); simp [hv,side] at hh
  have ts : Function.Surjective t := by
    intro i
    obtain ⟨v,hv⟩ := e.surjective (.inr i)
    cases v with
    | inr j => exact ⟨j,Sum.inr.inj ((ht j).symm.trans hv)⟩
    | inl j => have hh := he (.inl j); simp [hv,side] at hh
  refine ⟨Equiv.ofBijective s ⟨si,ss⟩,Equiv.ofBijective t ⟨ti,ts⟩,?_⟩
  intro v
  cases v with
  | inl i => exact (hs i).symm
  | inr j => exact (ht j).symm

end KroneckerBipartiteEquivSplit
end

/- Original module: KroneckerColoredLiftUniqueness -/
section
set_option autoImplicit false
namespace KroneckerColoredLiftUniqueness
open SimpleGraph KroneckerReducedColorWords KroneckerColorWordAction
open KroneckerWordTranslations KroneckerGraphColorWords KroneckerTreeRootPaths
open KroneckerColoredTreeLift

variable {V : Type*} {G : SimpleGraph V} (C : EdgeColoring G)

def RespectsColors (f : V → Word) : Prop :=
  ∀ {u v} (h : G.Adj u v), f u = toggle (C.color h) (f v)

theorem respects_walk {f : V → Word} (hf : RespectsColors C f)
    {u v : V} (p : G.Walk u v) : f u = act (colors C p) (f v) := by
  induction p with
  | nil => rfl
  | cons h p ih => rw [hf h, ih]; rfl

theorem lift_factorization (hT : G.IsTree) (r : V) {f : V → Word}
    (hf : RespectsColors C f) (v : V) : f v = translate (f r) (rootLift C hT r v) :=
  respects_walk C hf (rootPath hT r v)

theorem connected_lift_unique (hG : G.Preconnected) (r : V) {f g : V → Word}
    (hf : RespectsColors C f) (hg : RespectsColors C g) (hr : f r = g r) : f = g := by
  funext v
  obtain ⟨p⟩ := hG v r
  rw [respects_walk C hf p, respects_walk C hg p, hr]

theorem root_change (hT : G.IsTree) (r s v : V) :
    rootLift C hT s v = translate (rootLift C hT s r) (rootLift C hT r v) :=
  lift_factorization C hT r (fun h => rootLift_step C hT s h) v

theorem colored_map_lift {W : Type*} {H : SimpleGraph W} (D : EdgeColoring H)
    (hG : G.IsTree) (hH : H.IsTree) (f : G →g H)
    (hf : ∀ {u v} (h : G.Adj u v), D.color (f.map_adj h) = C.color h)
    (r : V) (s : W) (v : V) :
    rootLift D hH s (f v) =
      translate (rootLift D hH s (f r)) (rootLift C hG r v) := by
  apply lift_factorization C hG r (f := fun v => rootLift D hH s (f v))
  intro u v h
  change rootLift D hH s (f u) = toggle (C.color h) (rootLift D hH s (f v))
  rw [rootLift_step D hH s (f.map_adj h), hf h]

end KroneckerColoredLiftUniqueness
end

/- Original module: KroneckerBipartiteTreeLift -/
section
set_option autoImplicit false
namespace KroneckerBipartiteTreeLift
open SimpleGraph KroneckerProperColoredReflection KroneckerBipartiteIncidence
open KroneckerReducedColorWords KroneckerWordParity KroneckerIncidenceEdgeColoring
open KroneckerGraphColorWords KroneckerTreeRootPaths KroneckerColoredTreeLift
open KroneckerColoredLiftUniqueness KroneckerCoverDeckTranslations

variable {I J : Type} {R : I → J → Prop} (C : ProperColoring R)
  (hT : (incidenceGraph R).IsTree)

theorem source_root_lift_parity (r : I) (v : I ⊕ J) :
    parity (rootLift (incidenceColoring C) hT (.inl r) v) = side v := by
  have hs := walk_side (rootPath hT (.inl r) v)
  change (colors (incidenceColoring C) (rootPath hT (.inl r) v)).length % 2 = side v
  rw [colors_length]
  simpa only [side, add_zero] using hs.symm

theorem source_root_change (r s : I) : ∃ d : Deck, ∀ v,
    rootLift (incidenceColoring C) hT (.inl s) v =
      d (rootLift (incidenceColoring C) hT (.inl r) v) := by
  let g := rootLift (incidenceColoring C) hT (.inl s) (.inl r)
  have hg : parity g = 0 := source_root_lift_parity C hT s (.inl r)
  exact ⟨evenTranslation g hg, fun v => root_change (incidenceColoring C) hT _ _ v⟩

theorem lift_nonzero_source_parity (r : I) (i : I) :
    parity (rootLift (incidenceColoring C) hT (.inl r) (.inl i)) = 0 :=
  source_root_lift_parity C hT r (.inl i)

theorem lift_sink_parity (r : I) (j : J) :
    parity (rootLift (incidenceColoring C) hT (.inl r) (.inr j)) = 1 :=
  source_root_lift_parity C hT r (.inr j)

end KroneckerBipartiteTreeLift
end

/- Original module: KroneckerLiftedSupportIso -/
section
set_option autoImplicit false
namespace KroneckerLiftedSupportIso
open SimpleGraph KroneckerProperColoredReflection KroneckerColoredIncidenceIso
open KroneckerBipartiteIncidence KroneckerIncidenceEdgeColoring KroneckerBipartiteEquivSplit
open KroneckerReducedColorWords KroneckerWordParity KroneckerColoredTreeLift
open KroneckerTreeInducedEmbedding KroneckerBipartiteTreeLift KroneckerColorWordCover
open KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses

theorem lifted_equiv_colored_iso {I J I' J' : Type} {R : I → J → Prop} {R' : I' → J' → Prop}
    (C : ProperColoring R) (D : ProperColoring R')
    (hT : (incidenceGraph R).IsTree) (hT' : (incidenceGraph R').IsTree)
    (r : I) (s : I') (d : Deck) (e : (I ⊕ J) ≃ (I' ⊕ J'))
    (he : ∀ v, rootLift (incidenceColoring D) hT' (.inl s) (e v) =
      d (rootLift (incidenceColoring C) hT (.inl r) v)) :
    ∃ q : ColoredIso C D, ∀ v, q.graphIso v = e v := by
  let f := rootLift (incidenceColoring C) hT (.inl r)
  let g := rootLift (incidenceColoring D) hT' (.inl s)
  change ∀ v, g (e v) = d (f v) at he
  have hside : ∀ v, side (e v) = side v := by
    intro v
    calc
      side (e v) = parity (g (e v)) := (source_root_lift_parity D hT' s (e v)).symm
      _ = parity (d (f v)) := congrArg parity (he v)
      _ = parity (f v) := d.preserves_parity (f v)
      _ = side v := source_root_lift_parity C hT r v
  obtain ⟨es,et,het⟩ := side_preserving_equiv_splits e hside
  have hgraph (u v : I ⊕ J) : (incidenceGraph R').Adj (e u) (e v) ↔
      (incidenceGraph R).Adj u v := by
    calc
      (incidenceGraph R').Adj (e u) (e v) ↔ cover.Adj (g (e u)) (g (e v)) :=
        (treeEmbedding (incidenceColoring D) hT' (.inl s)).map_rel_iff.symm
      _ ↔ cover.Adj (d (f u)) (d (f v)) := by rw [he u, he v]
      _ ↔ cover.Adj (f u) (f v) := (Deck.graphIso d).map_rel_iff
      _ ↔ (incidenceGraph R).Adj u v :=
        (treeEmbedding (incidenceColoring C) hT (.inl r)).map_rel_iff
  have hi (i : I) (j : J) : R' (es i) (et j) ↔ R i j := by
    change (incidenceGraph R').Adj (Equiv.sumCongr es et (.inl i))
      (Equiv.sumCongr es et (.inr j)) ↔ (incidenceGraph R).Adj (.inl i) (.inr j)
    rw [het, het]
    exact hgraph _ _
  have hs (i : I) : g (.inl (es i)) = d (f (.inl i)) := by
    change g (Equiv.sumCongr es et (.inl i)) = _
    rw [het]
    exact he _
  have ht (j : J) : g (.inr (et j)) = d (f (.inr j)) := by
    change g (Equiv.sumCongr es et (.inr j)) = _
    rw [het]
    exact he _
  refine ⟨⟨es,et,hi,?_⟩,het⟩
  intro i j h
  apply toggle_color_injective (d (f (.inr j)))
  have hD := rootLift_step (incidenceColoring D) hT' (.inl s)
    (u := .inl (es i)) (v := .inr (et j)) ((hi i j).mpr h)
  change g (.inl (es i)) = toggle (D.color (es i) (et j) ((hi i j).mpr h)) (g (.inr (et j))) at hD
  rw [hs, ht] at hD
  have hC := rootLift_step (incidenceColoring C) hT (.inl r)
    (u := .inl i) (v := .inr j) h
  change f (.inl i) = toggle (C.color i j h) (f (.inr j)) at hC
  exact hD.symm.trans ((congrArg d hC).trans (d.commutes _ _))

end KroneckerLiftedSupportIso
end

/- Original module: KroneckerColoredIsoDeckLift -/
section
set_option autoImplicit false
namespace KroneckerColoredIsoDeckLift
open SimpleGraph
open KroneckerProperColoredReflection KroneckerColoredIncidenceIso KroneckerBipartiteIncidence
open KroneckerIncidenceEdgeColoring KroneckerColoredLiftUniqueness KroneckerColoredTreeLift
open KroneckerCoverDeckTranslations KroneckerWordParity KroneckerBipartiteTreeLift

variable {I J I' J' : Type} {R : I → J → Prop} {R' : I' → J' → Prop}
  {C : ProperColoring R} {D : ProperColoring R'}

theorem coloredIso_edge_color (e : ColoredIso C D) {u v : I ⊕ J}
    (h : (incidenceGraph R).Adj u v) :
    (incidenceColoring D).color (e.graphIso.toHom.map_adj h) = (incidenceColoring C).color h := by
  cases u with
  | inl i => cases v with
    | inl k => exact False.elim h
    | inr j => exact e.color i j h
  | inr j => cases v with
    | inr k => exact False.elim h
    | inl i => exact e.color i j h

theorem colored_iso_lifts_by_deck (e : ColoredIso C D)
    (hT : (incidenceGraph R).IsTree) (hT' : (incidenceGraph R').IsTree)
    (r : I) (s : I') : ∃ d : Deck, ∀ v,
    rootLift (incidenceColoring D) hT' (.inl s) (e.graphIso v) =
      d (rootLift (incidenceColoring C) hT (.inl r) v) := by
  let g := rootLift (incidenceColoring D) hT' (.inl s) (.inl (e.source r))
  have hg : parity g = 0 := source_root_lift_parity D hT' s (.inl (e.source r))
  refine ⟨evenTranslation g hg,fun v => ?_⟩
  exact colored_map_lift (incidenceColoring C) (incidenceColoring D) hT hT'
    e.graphIso.toHom (fun h => coloredIso_edge_color e h) (.inl r) (.inl s) v

end KroneckerColoredIsoDeckLift
end

/- Original module: KroneckerFiniteWeightedImages -/
section
set_option autoImplicit false
namespace KroneckerFiniteWeightedImages
open KroneckerReducedColorWords

variable {V : Type} [Fintype V]

noncomputable def weightedImage (f : V ↪ Word) (w : V → ℕ) : Word →₀ ℕ :=
  Finsupp.embDomain f (Finsupp.equivFunOnFinite.symm w)

theorem weightedImage_at (f : V ↪ Word) (w : V → ℕ) (v : V) : weightedImage f w (f v) = w v :=
  Finsupp.embDomain_apply_self _ _ _

theorem weightedImage_outside (f : V ↪ Word) (w : V → ℕ) {x : Word}
    (hx : x ∉ Set.range f) : weightedImage f w x = 0 := Finsupp.embDomain_of_notMem_range _ _ _ hx

theorem weightedImage_positive_iff (f : V ↪ Word) (w : V → ℕ) (hw : ∀ v, 0 < w v)
    (x : Word) : 0 < weightedImage f w x ↔ ∃ v, f v = x := by
  constructor
  · intro h
    by_contra hn
    rw [weightedImage_outside f w hn] at h
    omega
  · rintro ⟨v,rfl⟩
    rw [weightedImage_at]
    exact hw v

theorem weightedImage_support (f : V ↪ Word) (w : V → ℕ) (hw : ∀ v, 0 < w v) :
    (weightedImage f w).support = Finset.univ.map f := by
  classical
  ext x
  simp only [Finsupp.mem_support_iff, ←Nat.pos_iff_ne_zero, weightedImage_positive_iff f w hw,
    Finset.mem_map, Finset.mem_univ, true_and]

theorem weightedImage_total (f : V ↪ Word) (w : V → ℕ) :
    (weightedImage f w).sum (fun _ n => n) = ∑ v, w v := by
  classical
  rw [weightedImage, Finsupp.sum_embDomain]
  exact Finsupp.sum_fintype _ _ (fun _ => rfl)

end KroneckerFiniteWeightedImages
end

/- Original module: KroneckerWeightedImageRecovery -/
section
set_option autoImplicit false
namespace KroneckerWeightedImageRecovery
open KroneckerReducedColorWords KroneckerFiniteWeightedImages

variable {V W : Type} [Fintype V] [Fintype W]

theorem recover_weighted_equiv (f : V ↪ Word) (g : W ↪ Word) (w : V → ℕ) (z : W → ℕ)
    (hw : ∀ v, 0 < w v) (hz : ∀ v, 0 < z v) (d : Word ≃ Word)
    (h : ∀ x, weightedImage g z (d x) = weightedImage f w x) :
    ∃ e : V ≃ W, (∀ v, g (e v) = d (f v)) ∧ ∀ v, z (e v) = w v := by
  classical
  have hex (v : V) : ∃ t, g t = d (f v) := by
    apply (weightedImage_positive_iff g z hz _).mp
    rw [h, weightedImage_at]
    exact hw v
  choose k hk using hex
  have hi : Function.Injective k := by
    intro u v huv
    apply f.injective
    apply d.injective
    rw [←hk u, ←hk v, huv]
  have hs : Function.Surjective k := by
    intro t
    have hp : 0 < weightedImage f w (d.symm (g t)) := by
      rw [←h, d.apply_symm_apply, weightedImage_at]
      exact hz t
    obtain ⟨v,hv⟩ := (weightedImage_positive_iff f w hw _).mp hp
    refine ⟨v,g.injective ?_⟩
    rw [hk, hv, d.apply_symm_apply]
  let e := Equiv.ofBijective k ⟨hi,hs⟩
  refine ⟨e,hk,fun v => ?_⟩
  calc
    z (e v) = weightedImage g z (g (k v)) := (weightedImage_at g z (k v)).symm
    _ = weightedImage g z (d (f v)) := congrArg (weightedImage g z) (hk v)
    _ = weightedImage f w (f v) := h (f v)
    _ = w v := weightedImage_at f w v

theorem weighted_equiv_gives_image (f : V ↪ Word) (g : W ↪ Word) (w : V → ℕ) (z : W → ℕ)
    (d : Word ≃ Word) (e : V ≃ W) (he : ∀ v, g (e v) = d (f v))
    (hw : ∀ v, z (e v) = w v) : ∀ x, weightedImage g z (d x) = weightedImage f w x := by
  classical
  intro x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨v,rfl⟩ := hx
    rw [←he v, weightedImage_at, weightedImage_at, hw]
  · rw [weightedImage_outside f w hx]
    apply weightedImage_outside
    rintro ⟨t,ht⟩
    apply hx
    refine ⟨e.symm t,d.injective ?_⟩
    rw [←he, e.apply_symm_apply, ht]

theorem weighted_image_equiv_iff (f : V ↪ Word) (g : W ↪ Word) (w : V → ℕ) (z : W → ℕ)
    (hw : ∀ v, 0 < w v) (hz : ∀ v, 0 < z v) (d : Word ≃ Word) :
    (∀ x, weightedImage g z (d x) = weightedImage f w x) ↔
    ∃ e : V ≃ W, (∀ v, g (e v) = d (f v)) ∧ ∀ v, z (e v) = w v :=
  ⟨recover_weighted_equiv f g w z hw hz d,
    fun ⟨e,he,hw⟩ => weighted_equiv_gives_image f g w z d e he hw⟩

end KroneckerWeightedImageRecovery
end

/- Original module: KroneckerBlockCoverDimensions -/
section
set_option autoImplicit false
namespace KroneckerBlockCoverDimensions
open Module KroneckerLinearCoverBlocks KroneckerReflectedSupportClasses
open KroneckerRetainedBlockSupport KroneckerBipartiteIncidence KroneckerIncidenceEdgeColoring
open KroneckerReducedColorWords KroneckerColoredTreeLift KroneckerTreeInducedEmbedding
open KroneckerFiniteWeightedImages KroneckerWordParity KroneckerBipartiteTreeLift
open scoped BigOperators

noncomputable def vertexWeight (B : LinearCoverBlock) : B.Source ⊕ B.Sink → ℕ
  | .inl i => finrank ℂ (B.Space i)
  | .inr _ => 1

noncomputable def blockEmbedding (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) : (X.block.Source ⊕ X.block.Sink) ↪ Word :=
  (treeEmbedding (incidenceColoring X.coloring) hT (.inl r)).toEmbedding

noncomputable def coverDimensions (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) : Word →₀ ℕ := weightedImage (blockEmbedding X hT r) (vertexWeight X.block)

theorem coverDimensions_at (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) (v : X.block.Source ⊕ X.block.Sink) :
    coverDimensions X hT r (blockEmbedding X hT r v) = vertexWeight X.block v :=
  weightedImage_at _ _ _

theorem vertexWeight_positive (B : LinearCoverBlock) (hB : ∀ i, 0 < finrank ℂ (B.Space i)) :
    ∀ v, 0 < vertexWeight B v := by
  intro v
  cases v with
  | inl i => exact hB i
  | inr j => exact Nat.zero_lt_one

theorem cover_source_total (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) :
    (coverDimensions X hT r).sum (fun w n => if parity w = 0 then n else 0) =
      sourceDimension X.block := by
  classical
  rw [coverDimensions, weightedImage, Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (by intro v; split_ifs <;> rfl)]
  simp only [Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_sum_type]
  have hs (v) : parity (blockEmbedding X hT r v) = side v :=
    source_root_lift_parity X.coloring hT r v
  simp [hs, side, vertexWeight, sourceDimension]

theorem cover_sink_total (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) :
    (coverDimensions X hT r).sum (fun w n => if parity w = 1 then n else 0) =
      Fintype.card X.block.Sink := by
  classical
  rw [coverDimensions, weightedImage, Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (by intro v; split_ifs <;> rfl)]
  simp only [Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_sum_type]
  have hs (v) : parity (blockEmbedding X hT r v) = side v :=
    source_root_lift_parity X.coloring hT r v
  simp [hs, side, vertexWeight]

end KroneckerBlockCoverDimensions
end
