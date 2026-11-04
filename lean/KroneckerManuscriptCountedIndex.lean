import KroneckerManuscriptSupportBound
import KroneckerStableActualCoverObjects
import KroneckerManuscriptLocalizationIndex

/- Original module: KroneckerSupportDeckDictionary -/
section
set_option autoImplicit false
namespace KroneckerSupportDeckDictionary
open Module KroneckerReflectedSupportClasses KroneckerRetainedBlockSupport
open KroneckerDimensionedSupportClasses KroneckerBlockCoverDimensions
open KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses
open KroneckerColoredIsoDeckLift KroneckerWeightedImageRecovery KroneckerLiftedSupportIso
open KroneckerColoredIncidenceIso

theorem dimensioned_iso_gives_deck (X Y : ColoredBlock)
    (hX : (supportGraph X.block).IsTree) (hY : (supportGraph Y.block).IsTree)
    (r : X.block.Source) (s : Y.block.Source) (h : dimensionedSetoid X Y) :
    dimensionSetoid (coverDimensions X hX r) (coverDimensions Y hY s) := by
  obtain ⟨e,he⟩ := h
  obtain ⟨d,hd⟩ := colored_iso_lifts_by_deck e hX hY r s
  refine ⟨d, weighted_equiv_gives_image (blockEmbedding X hX r) (blockEmbedding Y hY s)
    (vertexWeight X.block) (vertexWeight Y.block) d.equiv e.graphIso.toEquiv hd ?_⟩
  intro v
  cases v with
  | inl i => exact he i
  | inr j => rfl

theorem deck_gives_dimensioned_iso (X Y : ColoredBlock)
    (hX : (supportGraph X.block).IsTree) (hY : (supportGraph Y.block).IsTree)
    (pX : ∀ i, 0 < finrank ℂ (X.block.Space i)) (pY : ∀ i, 0 < finrank ℂ (Y.block.Space i))
    (r : X.block.Source) (s : Y.block.Source)
    (h : dimensionSetoid (coverDimensions X hX r) (coverDimensions Y hY s)) :
    dimensionedSetoid X Y := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨e,he,hw⟩ := recover_weighted_equiv (blockEmbedding X hX r) (blockEmbedding Y hY s)
    (vertexWeight X.block) (vertexWeight Y.block) (vertexWeight_positive X.block pX)
    (vertexWeight_positive Y.block pY) d.equiv hd
  obtain ⟨q,hq⟩ := lifted_equiv_colored_iso X.coloring Y.coloring hX hY r s d e he
  refine ⟨q,fun i => ?_⟩
  have hp := hw (.inl i)
  rw [←hq] at hp
  exact hp

theorem support_deck_dictionary (X Y : ColoredBlock)
    (hX : (supportGraph X.block).IsTree) (hY : (supportGraph Y.block).IsTree)
    (pX : ∀ i, 0 < finrank ℂ (X.block.Space i)) (pY : ∀ i, 0 < finrank ℂ (Y.block.Space i))
    (r : X.block.Source) (s : Y.block.Source) :
    dimensionedSetoid X Y ↔
    dimensionSetoid (coverDimensions X hX r) (coverDimensions Y hY s) :=
  ⟨dimensioned_iso_gives_deck X Y hX hY r s,
    deck_gives_dimensioned_iso X Y hX hY pX pY r s⟩

end KroneckerSupportDeckDictionary
end

/- Original module: KroneckerStableChainCoverData -/
section
set_option autoImplicit false
namespace KroneckerStableChainCoverData
open Module KroneckerLinearCoverBlocks KroneckerReflectedSupportClasses
open KroneckerFiniteChainInputs KroneckerFiniteStableChainFamily
open KroneckerChainRepresentativeIndependence KroneckerChainSlotAssignments
open KroneckerRetainedReflectionKernels KroneckerRetainedBlockSupport
open KroneckerBlockCoverDimensions KroneckerSupportDeckDictionary KroneckerDeckDimensionClasses

noncomputable def chainBlock {n a : ℕ} (X : ChainInput n a) : ColoredBlock :=
  gluedRepresentative (representatives X.2.2)

def chainRoot {n a : ℕ} (X : ChainInput n a) : (chainBlock X).block.Source := .inl 0

theorem chain_source_positive {n a : ℕ} (X : ChainInput n a) :
    ∀ s, 0 < finrank ℂ ((chainBlock X).block.Space s) := by
  intro s
  cases s with
  | inl i => change 0 < finrank ℂ ℂ; norm_num
  | inr p =>
    rcases p with ⟨j,s⟩
    exact (retained_iff_kernel_positive _ s.val).mp s.property

abbrev StableInput (n a : ℕ) := {X : ChainInput n a // X ∈ stableInputs n a}

theorem chain_tree {n a : ℕ} (X : StableInput n a) :
    (supportGraph (chainBlock X.val).block).IsTree := (stable_input_realization X.val X.property).2.1

noncomputable def stableDimensions {n a : ℕ} (X : StableInput n a) :=
  coverDimensions (chainBlock X.val) (chain_tree X) (chainRoot X.val)

noncomputable def stableCoverClass {n a : ℕ} (X : StableInput n a) : DimensionClass :=
  Quotient.mk dimensionSetoid (stableDimensions X)

theorem stable_cover_class_iff {n a : ℕ} (X Y : StableInput n a) :
    stableCoverClass X = stableCoverClass Y ↔ forgetInput X.val = forgetInput Y.val := by
  rw [stableCoverClass, stableCoverClass, Quotient.eq]
  change dimensionSetoid (coverDimensions (chainBlock X.val) (chain_tree X) (chainRoot X.val))
    (coverDimensions (chainBlock Y.val) (chain_tree Y) (chainRoot Y.val)) ↔
    (Quotient.mk _ (chainBlock X.val) : Quotient KroneckerDimensionedSupportClasses.dimensionedSetoid) =
      Quotient.mk _ (chainBlock Y.val)
  rw [Quotient.eq]
  exact (support_deck_dictionary _ _ _ _ (chain_source_positive X.val)
    (chain_source_positive Y.val) _ _).symm

theorem stable_cover_totals {n a : ℕ} (X : StableInput n a) :
    (stableDimensions X).sum (fun w k => if KroneckerWordParity.parity w = 0 then k else 0) = a ∧
    (stableDimensions X).sum (fun w k => if KroneckerWordParity.parity w = 1 then k else 0) = a+n+2 := by
  have h := stable_input_realization X.val X.property
  constructor
  · exact (cover_source_total _ _ _).trans h.2.2.2.1
  · exact (cover_sink_total _ _ _).trans (h.2.2.2.2.trans (by omega))

end KroneckerStableChainCoverData
end

/- Original module: KroneckerEnumeratedCoverClasses -/
section
set_option autoImplicit false
namespace KroneckerEnumeratedCoverClasses
open KroneckerFiniteChainInputs KroneckerLatticeFamilyCounting
open KroneckerStableChainCoverData KroneckerDeckDimensionClasses
attribute [local instance] Classical.propDecidable

theorem equal_kernel_image_card {A : Type*} {B : Type*} {C : Type*}
    (S : Finset A) (f : A → B) (g : A → C)
    [DecidableEq B] [DecidableEq C]
    (h : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ g a = g b) :
    (S.image f).card = (S.image g).card := by
  classical
  let rep (b : {b // b ∈ S.image f}) := (Finset.mem_image.mp b.property).choose
  have hm (b : {b // b ∈ S.image f}) : rep b ∈ S :=
    (Finset.mem_image.mp b.property).choose_spec.1
  have hf (b : {b // b ∈ S.image f}) : f (rep b) = b.val :=
    (Finset.mem_image.mp b.property).choose_spec.2
  apply Finset.card_bij (fun b hb => g (rep ⟨b,hb⟩))
  · intro b hb
    exact Finset.mem_image.mpr ⟨_,hm ⟨b,hb⟩,rfl⟩
  · intro b hb c hc he
    exact (hf ⟨b,hb⟩).symm.trans (((h _ (hm ⟨b,hb⟩) _ (hm ⟨c,hc⟩)).mpr he).trans (hf ⟨c,hc⟩))
  · intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    have hb : f a ∈ S.image f := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    exact ⟨f a,hb,(h _ (hm ⟨f a,hb⟩) a ha).mp (hf ⟨f a,hb⟩)⟩

noncomputable def enumeratedStable {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x)
    (ha : ((n : ℝ)+2)*x=a) (X : {X // X ∈ enumeratedInputs hx ha}) : StableInput n a :=
  ⟨X.val,enumerated_inputs_subset hx ha X.property⟩

noncomputable def enumeratedCoverClasses {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x)
    (ha : ((n : ℝ)+2)*x=a) : Finset DimensionClass :=
  (enumeratedInputs hx ha).attach.image (fun X => stableCoverClass (enumeratedStable hx ha X))

theorem enumerated_cover_card {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x)
    (ha : ((n : ℝ)+2)*x=a) :
    (enumeratedCoverClasses hx ha).card = ((enumeratedInputs hx ha).image forgetInput).card := by
  classical
  unfold enumeratedCoverClasses
  let g : {X // X ∈ enumeratedInputs hx ha} →
    Quotient KroneckerDimensionedSupportClasses.dimensionedSetoid := fun X => forgetInput X.val
  trans ((enumeratedInputs hx ha).attach.image g).card
  · exact equal_kernel_image_card (enumeratedInputs hx ha).attach
      (fun X => stableCoverClass (enumeratedStable hx ha X)) g
      (fun X _ Y _ => stable_cover_class_iff (enumeratedStable hx ha X) (enumeratedStable hx ha Y))
  congr 1
  ext q
  dsimp only [g]
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, exists_prop]

end KroneckerEnumeratedCoverClasses
end

/- Original module: KroneckerManuscriptCoverBound -/
section
set_option autoImplicit false
namespace KroneckerManuscriptCoverBound
open KroneckerManuscriptSupportBound KroneckerEnumeratedCoverClasses KroneckerLatticeFamilyCounting
open KroneckerStableChainCoverData KroneckerDeckDimensionClasses KroneckerFiniteStableChainFamily
open KroneckerGluedSubrepEquivalence KroneckerRetainedBlockSupport KroneckerCoverTitsForm
open KroneckerLinearCoverBlocks
attribute [local instance] Classical.propDecidable

/-- The finite dimension vectors are on the explicit three-colored covering
tree, modulo color- and bipartition-preserving deck transformations. -/
theorem uniform_manuscript_cover_bound : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    ∀ (n a : ℕ) (x : ℝ) (hx : 100000 ≤ x) (ha : ((n : ℝ)+2)*x=a),
      manuscriptLower n a x A B ≤ (enumeratedCoverClasses hx ha).card := by
  obtain ⟨A,B,hA,hB,H⟩ := uniform_manuscript_support_bound
  refine ⟨A,B,hA,hB,fun n a x hx ha => ?_⟩
  rw [enumerated_cover_card]
  exact H n a x hx ha

/-- Each counted cover-dimension orbit is realized by the actual constructed
stable finite tree representation. This does not assert a moduli/Euler theorem. -/
theorem enumerated_cover_realization {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x)
    (ha : ((n : ℝ)+2)*x=a) (q : DimensionClass) (hq : q ∈ enumeratedCoverClasses hx ha) :
    ∃ X : StableInput n a, stableCoverClass X = q ∧
      BlockKingStable (chainBlock X.val).block ∧
      (supportGraph (chainBlock X.val).block).IsTree ∧
      titsForm (chainBlock X.val).block = 1 ∧
      (stableDimensions X).sum (fun w k => if KroneckerWordParity.parity w = 0 then k else 0) = a ∧
      (stableDimensions X).sum (fun w k => if KroneckerWordParity.parity w = 1 then k else 0) = a+n+2 := by
  obtain ⟨Y,_,hY⟩ := Finset.mem_image.mp hq
  let X := enumeratedStable hx ha Y
  have h := stable_input_realization X.val X.property
  exact ⟨X,hY,h.1,h.2.1,h.2.2.1,(stable_cover_totals X).1,(stable_cover_totals X).2⟩

end KroneckerManuscriptCoverBound
end

/- Original module: KroneckerEnumeratedActualCoverClasses -/
section
set_option autoImplicit false
namespace KroneckerEnumeratedActualCoverClasses
open KroneckerActualCoverClasses KroneckerManuscriptCoverBound
open KroneckerEnumeratedCoverClasses KroneckerStableChainCoverData
open KroneckerDeckDimensionClasses KroneckerFiniteStableChainFamily
open KroneckerManuscriptSupportBound KroneckerWordParity
attribute [local instance] Classical.propDecidable

variable {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x) (ha : ((n : ℝ)+2)*x=a)

noncomputable def chosenInput (q : {q // q ∈ enumeratedCoverClasses hx ha}) : StableInput n a :=
  (enumerated_cover_realization hx ha q.val q.property).choose

theorem chosen_input_dimension (q : {q // q ∈ enumeratedCoverClasses hx ha}) :
    stableCoverClass (chosenInput hx ha q) = q.val :=
  (enumerated_cover_realization hx ha q.val q.property).choose_spec.1

noncomputable def chosenObject (q : {q // q ∈ enumeratedCoverClasses hx ha}) : Object :=
  blockObject (chainBlock (chosenInput hx ha q).val) (chain_tree (chosenInput hx ha q))
    (chainRoot (chosenInput hx ha q).val)

theorem chosen_object_stable (q : {q // q ∈ enumeratedCoverClasses hx ha}) :
    ObjectStable (chosenObject hx ha q) := by
  apply blockObject_stable
  exact (stable_input_realization (chosenInput hx ha q).val (chosenInput hx ha q).property).1

/-- Choosing one actual stable object for each counted dimension orbit yields
an injection into representation classes generated by genuine deck isomorphisms. -/
theorem chosen_class_injective : Function.Injective (fun q : {q // q ∈ enumeratedCoverClasses hx ha} =>
    (Quot.mk DeckRelated (chosenObject hx ha q) : ActualClass)) := by
  apply family_class_injective
  intro q r h
  apply Subtype.ext
  exact (chosen_input_dimension hx ha q).symm.trans (h.trans (chosen_input_dimension hx ha r))

noncomputable def enumeratedActualClasses : Finset ActualClass :=
  (enumeratedCoverClasses hx ha).attach.image (fun q => Quot.mk DeckRelated (chosenObject hx ha q))

theorem enumerated_actual_card :
    (enumeratedActualClasses hx ha).card = (enumeratedCoverClasses hx ha).card := by
  classical
  rw [enumeratedActualClasses, Finset.card_image_of_injective _ (chosen_class_injective hx ha),
    Finset.card_attach]

/-- Every class being counted contains an intrinsically stable actual cover
representation with the manuscript source and sink totals. -/
theorem enumerated_actual_realization (q : ActualClass) (hq : q ∈ enumeratedActualClasses hx ha) :
    ∃ R : Object, ObjectStable R ∧ Quot.mk DeckRelated R = q ∧
      R.dimension.sum (fun w k => if parity w = 0 then k else 0) = a ∧
      R.dimension.sum (fun w k => if parity w = 1 then k else 0) = a+n+2 := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  exact ⟨chosenObject hx ha i, chosen_object_stable hx ha i, rfl,
    (stable_cover_totals (chosenInput hx ha i)).1, (stable_cover_totals (chosenInput hx ha i)).2⟩

/-- This lower bound now counts actual stable cover representation classes.
It is still NOT an Euler-characteristic lower bound. -/
theorem uniform_manuscript_actual_class_bound : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    ∀ (n a : ℕ) (x : ℝ) (hx : 100000 ≤ x) (ha : ((n : ℝ)+2)*x=a),
      manuscriptLower n a x A B ≤ (enumeratedActualClasses hx ha).card := by
  obtain ⟨A,B,hA,hB,H⟩ := uniform_manuscript_cover_bound
  refine ⟨A,B,hA,hB,fun n a x hx ha => ?_⟩
  rw [enumerated_actual_card]
  exact H n a x hx ha

end KroneckerEnumeratedActualCoverClasses
end

/- Original module: KroneckerManuscriptGlobalCoverRealization -/
section
/-! Construct the exact finite-support coordinate witness from an actual global
stable cover representation, using its arrow maps and the two proved restriction
equivalences. No nonemptiness of a geometric moduli space is assumed here. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptGlobalCoverRealization
open KroneckerManuscriptCoverParameters KroneckerManuscriptLocalizationIndex
open KroneckerActualCoverClasses KroneckerGlobalCoverCoordinates
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerColoredCoverPairDictionary KroneckerFiniteSupportStability
open KroneckerUniversalWordBaseProjection KroneckerFiniteQuiverHom
attribute [local instance] Classical.propDecidable

/-- All arrows, including zero arrow maps and off-support vertices, are retained. -/
def coordinates (R : Object) : Representation coloredCoverQuiver.source
    coloredCoverQuiver.target (fun w => R.dimension w) :=
  extendByZero coloredCoverQuiver R.dimension
    (pairRepresentationEquiv R.dimension
      (toCoordinates R.representation R.dimension R.source_dimension R.sink_dimension))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem coordinates_stable (R : Object) (hR : ObjectStable R) (a b : ℕ)
    (hD : R.dimension.mapDomain baseVertex = pairDimension a b) :
    FiniteSupportStable R.dimension (negativeWeight a b ∘ baseVertex) (coordinates R) := by
  let := objectSourceFintype R
  let := objectSinkFintype R
  have hchar : negativeWeight a b ∘ baseVertex = ambientKingWeight R.dimension := by
    funext w
    obtain ⟨hs,ht⟩ := compatible_cast_totals R.dimension a b hD
    simp only [Function.comp_apply, negativeWeight, ambientKingWeight, hs, ht]
    congr 1
    simp [baseVertex, Fin.ext_iff]
  rw [hchar]
  apply (ambient_stable_iff_pair _ _).mpr
  have he : restrictToSupport coloredCoverQuiver R.dimension (coordinates R) =
      pairRepresentationEquiv R.dimension
        (toCoordinates R.representation R.dimension R.source_dimension R.sink_dimension) := by
    apply representation_ext
    funext e
    dsimp only [restrictToSupport, coordinates, extendByZero]
    split
    · congr 1
    · rename_i hn
      exact (hn e.property).elim
  have hp : toPairRepresentation R.dimension (coordinates R) =
      toCoordinates R.representation R.dimension R.source_dimension R.sink_dimension := by
    unfold toPairRepresentation
    exact (congrArg (pairRepresentationEquiv R.dimension).symm he).trans
      ((pairRepresentationEquiv R.dimension).symm_apply_apply _)
  exact hp.symm ▸ global_support_stable_coordinates R.representation R.dimension
    R.source_dimension R.sink_dimension hR

def toDatum (R : Object) (hR : ObjectStable R) (a b : ℕ) (ha : 0<a)
    (hD : R.dimension.mapDomain baseVertex = pairDimension a b) : Datum a b :=
  ⟨⟨R.dimension,coordinates R⟩,compatible_nonzero _ a b ha hD,hD,
    (stability_sign_dictionary _ a b hD _).mp (coordinates_stable R hR a b hD)⟩

theorem realized_index_dimension (R : Object) (hR : ObjectStable R) (a b : ℕ) (ha : 0<a)
    (hD : R.dimension.mapDomain baseVertex = pairDimension a b) :
    (toIndex (toDatum R hR a b ha hD)).val =
      Quotient.mk KroneckerDeckDimensionClasses.dimensionSetoid R.dimension := by
  rfl

end KroneckerManuscriptGlobalCoverRealization
end
end

/- Original module: KroneckerManuscriptCountedIndex -/
section
/-! The counted block-chain family injects into the full fixed stable dimension
index, with its actual global representation and exact total dimensions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptCountedIndex
open KroneckerManuscriptCoverParameters KroneckerManuscriptLocalizationIndex
open KroneckerManuscriptGlobalCoverRealization KroneckerEnumeratedActualCoverClasses
open KroneckerEnumeratedCoverClasses KroneckerStableChainCoverData
open KroneckerUniversalWordBaseProjection KroneckerManuscriptCoverBound
open KroneckerManuscriptSupportBound
attribute [local instance] Classical.decEq Classical.propDecidable

variable {n a : ℕ} {x : ℝ} (hx : 100000 ≤ x) (ha : ((n : ℝ)+2)*x=a)

include hx ha in
theorem source_positive : 0<a := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h : (0 : ℝ) < a := by rw [← ha]; nlinarith
  exact_mod_cast h

theorem chosen_compatible (q : {q // q ∈ enumeratedCoverClasses hx ha}) :
    (chosenObject hx ha q).dimension.mapDomain baseVertex = pairDimension a (a+n+2) := by
  apply (compatible_iff _ _ _).mpr
  exact stable_cover_totals (chosenInput hx ha q)

def countedDatum (q : {q // q ∈ enumeratedCoverClasses hx ha}) : Datum a (a+n+2) :=
  toDatum (chosenObject hx ha q) (chosen_object_stable hx ha q) a (a+n+2)
    (source_positive hx ha) (chosen_compatible hx ha q)

def countedIndex (q : {q // q ∈ enumeratedCoverClasses hx ha}) : Index a (a+n+2) :=
  toIndex (countedDatum hx ha q)

theorem countedIndex_value (q : {q // q ∈ enumeratedCoverClasses hx ha}) :
    (countedIndex hx ha q).val = q.val := chosen_input_dimension hx ha q

theorem countedIndex_injective : Function.Injective (countedIndex hx ha) := by
  intro q r h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  simpa only [countedIndex_value] using he

theorem counted_classes_le_full_index :
    (enumeratedCoverClasses hx ha).card ≤ Fintype.card (Index a (a+n+2)) := by
  have h := Fintype.card_le_of_injective _ (countedIndex_injective hx ha)
  simpa using h

/-- The quantitative count is now a lower bound for the full fixed index;
no geometric Euler characteristic is used in this statement. -/
theorem uniform_manuscript_index_bound : ∃ A B : ℝ, 0<A ∧ 0<B ∧
    ∀ (n a : ℕ) (x : ℝ) (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a),
      manuscriptLower n a x A B ≤ (Fintype.card (Index a (a+n+2)) : ℝ) := by
  obtain ⟨A,B,hA,hB,H⟩ := uniform_manuscript_cover_bound
  refine ⟨A,B,hA,hB,fun n a x hx ha => ?_⟩
  exact (H n a x hx ha).trans (by exact_mod_cast counted_classes_le_full_index hx ha)

end KroneckerManuscriptCountedIndex
end
end
