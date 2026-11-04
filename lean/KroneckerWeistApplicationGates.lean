import KroneckerWeistDimensionTransport
import KroneckerStableOrbitHomeomorphism
import KroneckerPositiveFiberTotals
import KroneckerPublishedModuli
import KroneckerCanonicalKroneckerModuli
import KroneckerSupportDimensionPushforward
import KroneckerManuscriptCountedIndex

section

/- Original module: KroneckerWeistDimensionClasses -/
section
/-! No collisions or new identifications are created by using Weist's
possibly disconnected free-group-word cover in place of the connected model. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistDimensionClasses
open KroneckerWeistSignedWords KroneckerWeistCoverEmbedding KroneckerWeistTranslations
open KroneckerWeistDeckDictionary KroneckerWeistDimensionTransport
open KroneckerReducedColorWords KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

def ShiftRelated (D E : cover.V →₀ ℕ) : Prop := ∃ g : GroupWord, D.mapDomain (shift g)=E

theorem push_related_iff (D E : Word →₀ ℕ) :
    ShiftRelated (push D) (push E) ↔ dimensionSetoid.r D E := by
  constructor
  · rintro ⟨g,hg⟩
    by_cases hz : D=0
    · have he : E=0 := by
        apply push_injective
        simpa [hz,push] using hg.symm
      subst D
      subst E
      exact ⟨Deck.refl,fun _ => rfl⟩
    · obtain ⟨u,hu⟩ := Finsupp.support_nonempty_iff.mpr hz
      have hdu : D u≠0 := Finsupp.mem_support_iff.mp hu
      have he : push E (shift g (vertex u))=D u := by
        rw [←hg,Finsupp.mapDomain_apply_of_injective (shift_injective g),push_at]
      obtain ⟨v,hv⟩ := push_nonzero_range E (shift g (vertex u)) (by rwa [he])
      obtain ⟨d,_,hd⟩ := shift_match_deck g u v hv.symm
      apply (dimension_related_iff_pushforward D E).mpr
      refine ⟨d,push_injective ?_⟩
      calc
        push (D.mapDomain d) = (push D).mapDomain (shift g) := by
          unfold push
          rw [←Finsupp.mapDomain_comp,←Finsupp.mapDomain_comp]
          apply Finsupp.mapDomain_congr
          intro w _
          exact (hd w).symm
        _ = push E := hg
  · intro h
    obtain ⟨d,rfl⟩ := (dimension_related_iff_pushforward D E).mp h
    exact ⟨encode (d root),deck_transport d D⟩

end KroneckerWeistDimensionClasses
end
end

/- Original module: KroneckerWeistClassInjection -/
section
/-! The published translation quotient and the injective map from the project's
unmarked dimension quotient. Quotient equality has been proved both ways. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistClassInjection
open KroneckerWeistSignedWords KroneckerWeistCoverEmbedding KroneckerWeistTranslations
open KroneckerWeistDimensionTransport KroneckerWeistDimensionClasses
open KroneckerReducedColorWords KroneckerDeckDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

def shifted (g : GroupWord) (D : cover.V →₀ ℕ) := D.mapDomain (shift g)

theorem shifted_one (D : cover.V →₀ ℕ) : shifted 1 D=D := by
  have hs : shift 1 = id := by funext v; simp [shift]; rfl
  unfold shifted
  rw [hs,Finsupp.mapDomain_id]

theorem shifted_mul (g h : GroupWord) (D : cover.V →₀ ℕ) :
    shifted (g*h) D = shifted g (shifted h D) := by
  unfold shifted
  rw [←Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro v _
  simp [shift,mul_assoc]
  rfl

def translationSetoid : Setoid (cover.V →₀ ℕ) where
  r := ShiftRelated
  iseqv := by
    constructor
    · intro D
      exact ⟨1,shifted_one D⟩
    · rintro D E ⟨g,hg⟩
      change shifted g D=E at hg
      refine ⟨g⁻¹,?_⟩
      change shifted g⁻¹ E=D
      rw [←hg,←shifted_mul,inv_mul_cancel,shifted_one]
    · rintro D E F ⟨g,hg⟩ ⟨h,hh⟩
      change shifted g D=E at hg
      change shifted h E=F at hh
      refine ⟨h*g,?_⟩
      change shifted (h*g) D=F
      rw [shifted_mul,hg,hh]

abbrev Class := Quotient translationSetoid

def classMap : DimensionClass → Class :=
  Quotient.map push (fun _ _ h => (push_related_iff _ _).mpr h)

theorem classMap_injective : Function.Injective classMap := by
  intro x y
  induction x using Quotient.inductionOn with | h D =>
    induction y using Quotient.inductionOn with | h E =>
      intro h
      apply Quotient.sound
      exact (push_related_iff D E).mp (Quotient.exact h)

end KroneckerWeistClassInjection
end
end
end

section

/-! Transport the actual stable cover representation, including all arrow maps
and all subrepresentations, to the published free-word-cover presentation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistStablePush
open KroneckerWeistSignedWords KroneckerWeistCoverEmbedding KroneckerWeistDimensionTransport
open KroneckerManuscriptCoverParameters KroneckerManuscriptLocalizationIndex
open KroneckerFullImageQuiverEmbedding KroneckerFullImagePushforward
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportStability
open KroneckerUniversalWordBaseProjection KroneckerWordParity
attribute [local instance] Classical.decEq Classical.propDecidable

theorem embedding_full : FullOnImage embedding := by
  intro e u v hs _
  have hp : parity u=0 := (congrArg (fun z : cover.V => z.1.val) hs).symm
  have hg : encode u=e.2 := (congrArg Prod.snd hs).symm
  exact ⟨(e.1,⟨u,hp⟩),Prod.ext rfl hg⟩

def liftDatum {a b : ℕ} (S : Datum a b) : SupportedRepresentation cover :=
  KroneckerFullImagePushforward.push embedding vertex_injective arrow_injective embedding_full S.val

theorem lift_dimension {a b : ℕ} (S : Datum a b) :
    (liftDatum S).1 = KroneckerWeistDimensionTransport.push S.val.1 :=
  push_dimension embedding vertex_injective arrow_injective embedding_full S.val

theorem lift_stable {a b : ℕ} (S : Datum a b) :
    FiniteSupportStable (liftDatum S).1 (fun v => negativeWeight a b v.1) (liftDatum S).2 := by
  apply (push_stable_iff embedding vertex_injective arrow_injective embedding_full S.val _).mpr
  exact (stability_sign_dictionary _ _ _ S.property.2.1 _).mpr S.property.2.2

theorem lift_compatible {a b : ℕ} (S : Datum a b) :
    (liftDatum S).1.mapDomain Prod.fst=pairDimension a b := by
  exact (KroneckerFullImageNumericalTransport.push_original_dimension
    embedding vertex_injective arrow_injective embedding_full S.val Prod.fst).trans S.property.2.1

theorem lift_nonzero {a b : ℕ} (S : Datum a b) : (liftDatum S).1 ≠ 0 := by
  rw [lift_dimension]
  intro h
  apply S.property.1
  apply KroneckerWeistDimensionTransport.push_injective
  simp only [KroneckerWeistDimensionTransport.push]
  exact h

end KroneckerWeistStablePush
end
end

section

/- Original module: KroneckerFullImageOrbitTopology -/
section
/-! Zero extension along a full embedding preserves canonical finite-support
stable orbit spaces up to homeomorphism, including parallel arrows. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullImageOrbitTopology
open KroneckerAbelianCover KroneckerTypedQuiverMaps
open KroneckerEmbeddedFiniteDimensions KroneckerFullImageQuiverEmbedding
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerCanonicalStableOrbit
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver} (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
  (ha : Function.Injective f.arrow) (hf : FullOnImage f)
  (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
  [Fintype (supportQuiver P (descend f.vertex hv d)).A]
  [Fintype (supportQuiver Q d).A]
  (θ : Q.V → ℤ)
local instance leftVertices : Fintype (supportQuiver P (descend f.vertex hv d)).V :=
  inferInstanceAs (Fintype (SupportVertex (descend f.vertex hv d)))
local instance rightVertices : Fintype (supportQuiver Q d).V :=
  inferInstanceAs (Fintype (SupportVertex d))

def supportOrbitHomeomorph :
    space (supportQuiver Q d).source (supportQuiver Q d).target
      (supportDimension d) (supportCharacter d θ) ≃ₜ
    space (supportQuiver P (descend f.vertex hv d)).source
      (supportQuiver P (descend f.vertex hv d)).target
      (supportDimension (descend f.vertex hv d))
      (supportCharacter (descend f.vertex hv d) (θ ∘ f.vertex)) :=
  KroneckerStableOrbitHomeomorphism.orbitHomeomorph (supportIso f hv ha hf d hd)
    (supportDimension (descend f.vertex hv d))
    (Finsupp.equivFunOnFinite.symm (supportDimension d)) (fun _ => rfl)
    (supportCharacter d θ)

end KroneckerFullImageOrbitTopology
end
end

/- Original module: KroneckerPushedSupportTopology -/
section
/-! Explicit homeomorphism for pushforward dimensions along a full embedding.
The finite support equality is proved, not assumed as an extra comparison. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPushedSupportTopology
open KroneckerAbelianCover KroneckerTypedQuiverMaps
open KroneckerEmbeddedFiniteDimensions KroneckerFullImageQuiverEmbedding
open KroneckerFiniteSupportInducedQuiver KroneckerCanonicalSupportOrbit
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver} (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
  (ha : Function.Injective f.arrow) (hf : FullOnImage f)
  [∀ d : P.V →₀ ℕ, Fintype (supportQuiver P d).A]
  [∀ d : Q.V →₀ ℕ, Fintype (supportQuiver Q d).A]
  (d : P.V →₀ ℕ) (θ : Q.V → ℤ)

def pushedHomeomorph : space Q (d.mapDomain f.vertex) θ ≃ₜ space P d (θ ∘ f.vertex) := by
  have hi : InImage f.vertex (d.mapDomain f.vertex) := (dimensionEquiv f.vertex hv d).property
  have hd : descend f.vertex hv (d.mapDomain f.vertex)=d :=
    Finsupp.comapDomain_mapDomain f.vertex hv d
  have H := KroneckerFullImageOrbitTopology.supportOrbitHomeomorph f hv ha hf
    (d.mapDomain f.vertex) hi θ
  change space Q (d.mapDomain f.vertex) θ ≃ₜ
    space P (descend f.vertex hv (d.mapDomain f.vertex)) (θ ∘ f.vertex) at H
  have hs : space P (descend f.vertex hv (d.mapDomain f.vertex)) (θ ∘ f.vertex) =
      space P d (θ ∘ f.vertex) := congrArg (fun D => space P D (θ ∘ f.vertex)) hd
  exact H.trans (TopCat.homeoOfIso (CategoryTheory.eqToIso hs))

end KroneckerPushedSupportTopology
end
end

/- Original module: KroneckerWeistFiniteArrows -/
section
/-! Finite support in the free-word cover has finitely many actual arrows,
with a quantitative bound retaining all three colors. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistFiniteArrows
open KroneckerWeistCoverEmbedding KroneckerWeistSignedWords KroneckerReducedColorWords
open KroneckerFiniteSupportInducedQuiver
attribute [local instance] Classical.decEq Classical.propDecidable
variable (d : cover.V →₀ ℕ)

def arrowCode (a : (supportQuiver cover d).A) : Color × SupportVertex d :=
  (a.val.1,⟨cover.source a.val,a.property.1⟩)

theorem arrowCode_injective : Function.Injective (arrowCode d) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Color × SupportVertex d => z.1) h
  · exact congrArg (fun z : Color × SupportVertex d => z.2.val.2) h

instance supportVertices : Fintype (supportQuiver cover d).V :=
  inferInstanceAs (Fintype (SupportVertex d))

instance supportArrows : Fintype (supportQuiver cover d).A :=
  Fintype.ofInjective (arrowCode d) (arrowCode_injective d)


end KroneckerWeistFiniteArrows
end
end

/- Original module: KroneckerWeistStableTranslation -/
section
/-! Translate actual representations, preserving stability, original dimensions,
and the exact free-word translation class. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistStableTranslation
open KroneckerWeistCoverEmbedding KroneckerWeistTranslations KroneckerWeistSignedWords
open KroneckerWeistDimensionTransport KroneckerWeistClassInjection
open KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFullImagePushforward KroneckerFullImageNumericalTransport
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportStability
attribute [local instance] Classical.decEq Classical.propDecidable

def shiftMap (g : GroupWord) : QuiverMap cover cover :=
  ⟨(translation g).vertexEquiv,(translation g).arrowEquiv,
    (translation g).map_source,(translation g).map_target⟩

theorem shift_full (g : GroupWord) : FullOnImage (shiftMap g) := by
  intro e _ _ _ _
  exact (translation g).arrowEquiv.surjective e

def translateRep (g : GroupWord) (S : SupportedRepresentation cover) : SupportedRepresentation cover :=
  push (shiftMap g) (translation g).vertexEquiv.injective
    (translation g).arrowEquiv.injective (shift_full g) S

theorem translated_dimension (g : GroupWord) (S : SupportedRepresentation cover) :
    (translateRep g S).1=shifted g S.1 :=
  push_dimension (shiftMap g) _ _ _ S

theorem translated_original (g : GroupWord) (S : SupportedRepresentation cover) :
    (translateRep g S).1.mapDomain Prod.fst=S.1.mapDomain Prod.fst :=
  push_original_dimension (shiftMap g) _ _ _ S Prod.fst

theorem translated_nonzero (g : GroupWord) (S : SupportedRepresentation cover) :
    (translateRep g S).1≠0 ↔ S.1≠0 :=
  not_congr (push_zero_iff (shiftMap g) _ _ _ S)

theorem translated_stability (g : GroupWord) (S : SupportedRepresentation cover) (θ : Fin 2 → ℤ) :
    FiniteSupportStable (translateRep g S).1 (fun v => θ v.1) (translateRep g S).2 ↔
      FiniteSupportStable S.1 (fun v => θ v.1) S.2 :=
  push_stable_iff (shiftMap g) _ _ _ S (fun v => θ v.1)

theorem translated_class (g : GroupWord) (S : SupportedRepresentation cover) :
    (Quotient.mk translationSetoid (translateRep g S).1 : Class)=Quotient.mk translationSetoid S.1 := by
  apply Eq.symm
  apply Quotient.sound
  exact ⟨g,(translated_dimension g S).symm⟩

end KroneckerWeistStableTranslation
end
end

/- Original module: KroneckerWeistOrbitTopology -/
section
/-! Concrete free-word support orbit spaces and homeomorphisms implementing both
connected-cover embedding and the translation equivalence used by the source. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistOrbitTopology
open KroneckerWeistCoverEmbedding KroneckerWeistSignedWords
open KroneckerWeistStablePush KroneckerWeistStableTranslation
open KroneckerWeistDimensionTransport KroneckerWeistTranslations
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerManuscriptCoverParameters KroneckerUniversalWordBaseProjection
open KroneckerCanonicalSupportOrbit KroneckerPushedSupportTopology
attribute [local instance] Classical.decEq Classical.propDecidable

instance connectedArrows (d : coloredCoverQuiver.V →₀ ℕ) :
    Fintype (supportQuiver coloredCoverQuiver d).A :=
  Fintype.ofEquiv _ (KroneckerColoredCoverPairDictionary.supportArrowEquiv d).symm

def coverSpace (d : cover.V →₀ ℕ) (a b : ℕ) : TopCat.{0} :=
  space cover d (fun v => negativeWeight a b v.1)

def embeddingHomeomorph (d : KroneckerReducedColorWords.Word →₀ ℕ) (a b : ℕ) :
    coverSpace (push d) a b ≃ₜ
      space coloredCoverQuiver d (negativeWeight a b ∘ baseVertex) :=
  pushedHomeomorph embedding vertex_injective arrow_injective embedding_full d
    (fun v => negativeWeight a b v.1)

def translationHomeomorph (g : GroupWord) (d : cover.V →₀ ℕ) (a b : ℕ) :
    coverSpace (KroneckerWeistClassInjection.shifted g d) a b ≃ₜ coverSpace d a b :=
  pushedHomeomorph (shiftMap g) (shift_injective g) (translation g).arrowEquiv.injective
    (shift_full g) d (fun v => negativeWeight a b v.1)

end KroneckerWeistOrbitTopology
end
end

/- Original module: KroneckerWeistClassTopology -/
section
/-! Equality of source translation classes preserves actual support-moduli
homeomorphism type, homological admissibility and ordinary Euler characteristic. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistClassTopology
open KroneckerWeistCoverEmbedding KroneckerWeistClassInjection KroneckerWeistOrbitTopology
open KroneckerOrdinarySingularEuler
variable (a b : ℕ) {d e : cover.V →₀ ℕ}
  (h : Quotient.mk translationSetoid d=Quotient.mk translationSetoid e)

def classHomeomorph : coverSpace d a b ≃ₜ coverSpace e a b := by
  let g := (Quotient.exact h).choose
  have hg := (Quotient.exact h).choose_spec
  change shifted g d=e at hg
  have hs := congrArg (fun D => coverSpace D a b) hg
  exact (translationHomeomorph g d a b).symm.trans
    (TopCat.homeoOfIso (CategoryTheory.eqToIso hs))

include h in
theorem class_admissible_iff : Admissible (coverSpace d a b) ↔ Admissible (coverSpace e a b) :=
  KroneckerHomologyHomeomorphism.admissible_iff (classHomeomorph a b h)

include h in
theorem class_euler_eq (hd : Admissible (coverSpace d a b)) (he : Admissible (coverSpace e a b)) :
    ordinaryEuler (coverSpace d a b) hd=ordinaryEuler (coverSpace e a b) he :=
  KroneckerHomologyHomeomorphism.euler_eq (classHomeomorph a b h) hd he

end KroneckerWeistClassTopology
end
end

/- Original module: KroneckerWeistSupportNormalization -/
section
/-! Every compatible stable support with positive source dimension lies in a
component that can be translated into the project's based cover. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistSupportNormalization
open KroneckerWeistCoverEmbedding KroneckerWeistBaseComponent KroneckerWeistTranslations
open KroneckerWeistSignedWords KroneckerManuscriptCoverParameters
open KroneckerAbelianCover KroneckerFiniteSupportInducedQuiver
open KroneckerWeightedSupportDeckCriterion
attribute [local instance] Classical.decEq Classical.propDecidable

theorem adj_symm {u v : cover.V} (h : Adj u v) : Adj v u := by
  obtain ⟨e,h | h⟩ := h
  · exact ⟨e,Or.inr ⟨h.2,h.1⟩⟩
  · exact ⟨e,Or.inl ⟨h.2,h.1⟩⟩

theorem support_walk_reach (D : cover.V →₀ ℕ) {u v : (supportQuiver cover D).V}
    (p : LabeledWalk (supportQuiver cover D).source (supportQuiver cover D).target u v) :
    Reach u.val v.val := by
  induction p with
  | nil => exact .refl
  | forward e p ih => exact ih.head ⟨e.val,Or.inl ⟨rfl,rfl⟩⟩
  | backward e p ih => exact ih.head ⟨e.val,Or.inr ⟨rfl,rfl⟩⟩

theorem connected_support_reach (D : cover.V →₀ ℕ) (hc : SupportConnected cover D)
    (u v : SupportVertex D) : Reach u.val v.val := by
  obtain ⟨r,hr⟩ := hc
  obtain ⟨p⟩ := hr u
  obtain ⟨q⟩ := hr v
  let : Std.Symm Adj := ⟨fun _ _ h => adj_symm h⟩
  exact ((Relation.ReflTransGen.stdSymm (r := Adj)).symm _ _
    (support_walk_reach D p)).trans (support_walk_reach D q)

theorem compatible_source_exists (D : cover.V →₀ ℕ) (a b : ℕ) (ha : 0<a)
    (hD : D.mapDomain Prod.fst=pairDimension a b) :
    ∃ g : GroupWord, (0,g) ∈ D.support := by
  have hz : (0 : Fin 2) ∈ (D.mapDomain Prod.fst).support := by
    rw [hD,Finsupp.mem_support_iff,pairDimension_zero]
    omega
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hz)
  refine ⟨v.2,?_⟩
  have h : (0,v.2)=v := Prod.ext he.symm rfl
  rwa [h]

theorem connected_support_normalizes (D : cover.V →₀ ℕ)
    (hc : SupportConnected cover D) (a b : ℕ) (ha : 0<a)
    (hD : D.mapDomain Prod.fst=pairDimension a b) :
    ∃ g : GroupWord, ∀ v ∈ D.support, InBase (shift g v) := by
  obtain ⟨g,hg⟩ := compatible_source_exists D a b ha hD
  refine ⟨g⁻¹,fun v hv => ?_⟩
  exact source_component_normalization g v (connected_support_reach D hc ⟨(0,g),hg⟩ ⟨v,hv⟩)

end KroneckerWeistSupportNormalization
end
end

/- Original module: KroneckerWeistStableNormalization -/
section
/-! A stable compatible representation with positive source total has an actual
translated representative supported on the based component. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistStableNormalization
open KroneckerWeistCoverEmbedding KroneckerWeistBaseComponent KroneckerWeistTranslations
open KroneckerWeistSignedWords KroneckerWeistClassInjection KroneckerWeistStableTranslation
open KroneckerWeistSupportNormalization KroneckerManuscriptCoverParameters
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportStability
open KroneckerEmbeddedFiniteDimensions
attribute [local instance] Classical.decEq Classical.propDecidable

theorem stable_normalization (S : SupportedRepresentation cover) (a b : ℕ) (ha : 0<a)
    (hn : S.1≠0) (hD : S.1.mapDomain Prod.fst=pairDimension a b)
    (hs : FiniteSupportStable S.1 (fun v => negativeWeight a b v.1) S.2) :
    ∃ g : GroupWord, InImage embedding.vertex (translateRep g S).1 := by
  have hc := KroneckerDirectSumStableSupportTree.stable_support_connected cover S.1 hn _ S.2 hs
  obtain ⟨g,hg⟩ := connected_support_normalizes S.1 hc a b ha hD
  refine ⟨g,?_⟩
  intro v hv
  have hm : v ∈ (S.1.mapDomain (shift g)).support := by
    rw [translated_dimension] at hv
    exact hv
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
  exact hg u hu

end KroneckerWeistStableNormalization
end
end

/- Original module: KroneckerWeistStableDescent -/
section
/-! Descend the actual stable representation from the based component. This
recovers precisely the project Datum, including compatibility and stability. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistStableDescent
open KroneckerWeistCoverEmbedding KroneckerWeistDimensionTransport KroneckerWeistStablePush
open KroneckerManuscriptCoverParameters KroneckerManuscriptLocalizationIndex
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportStability
open KroneckerFullImageSupportedBridge KroneckerFullImagePushforward
open KroneckerEmbeddedFiniteDimensions KroneckerUniversalWordBaseProjection
attribute [local instance] Classical.decEq Classical.propDecidable

variable (S : SupportedRepresentation cover) (hi : InImage embedding.vertex S.1)

def descended := supportedEquiv embedding vertex_injective arrow_injective embedding_full ⟨S,hi⟩

theorem descended_dimension : KroneckerWeistDimensionTransport.push (descended S hi).1=S.1 := by
  exact (push_dimension embedding vertex_injective arrow_injective embedding_full (descended S hi)).symm.trans
    (congrArg Sigma.fst (push_descend embedding vertex_injective arrow_injective embedding_full ⟨S,hi⟩))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem descended_compatible (a b : ℕ) (hD : S.1.mapDomain Prod.fst=pairDimension a b) :
    (descended S hi).1.mapDomain baseVertex=pairDimension a b := by
  calc
    (descended S hi).1.mapDomain baseVertex =
        (KroneckerWeistDimensionTransport.push (descended S hi).1).mapDomain Prod.fst := by
      unfold KroneckerWeistDimensionTransport.push
      rw [←Finsupp.mapDomain_comp]
      rfl
    _ = pairDimension a b := (congrArg (fun d => d.mapDomain Prod.fst) (descended_dimension S hi)).trans hD

theorem descended_nonzero (hn : S.1≠0) : (descended S hi).1≠0 := by
  intro hz
  have he := descended_dimension S hi
  rw [hz] at he
  apply hn
  simp only [KroneckerWeistDimensionTransport.push] at he
  exact he.symm

def toDatum (a b : ℕ) (hn : S.1≠0) (hD : S.1.mapDomain Prod.fst=pairDimension a b)
    (hs : FiniteSupportStable S.1 (fun v => negativeWeight a b v.1) S.2) : Datum a b :=
  ⟨descended S hi,descended_nonzero S hi hn,descended_compatible S hi a b hD,
    (stability_sign_dictionary _ _ _ (descended_compatible S hi a b hD) _).mp
      ((supportedEquiv_stable embedding vertex_injective arrow_injective embedding_full
        ⟨S,hi⟩ (fun v => negativeWeight a b v.1)).mpr hs)⟩

end KroneckerWeistStableDescent
end
end

/- Original module: KroneckerWeistStableIndexEquivalence -/
section
/-! Exact equivalence of the full potentially nonempty stable localization index
in the connected model and Weist's full free-word model, for positive source total. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistStableIndexEquivalence
open KroneckerWeistCoverEmbedding KroneckerWeistStablePush KroneckerWeistClassInjection
open KroneckerWeistStableTranslation KroneckerWeistStableNormalization
open KroneckerWeistStableDescent KroneckerWeistDimensionTransport
open KroneckerManuscriptLocalizationIndex KroneckerManuscriptCoverParameters
open KroneckerQuiverPullbackComposition KroneckerFiniteSupportStability
attribute [local instance] Classical.decEq Classical.propDecidable

def SourceIndex (a b : ℕ) :=
  {q : Class // ∃ S : SupportedRepresentation cover, S.1≠0 ∧
    S.1.mapDomain Prod.fst=pairDimension a b ∧
    FiniteSupportStable S.1 (fun v => negativeWeight a b v.1) S.2 ∧
    Quotient.mk translationSetoid S.1=q}

def indexMap {a b : ℕ} (q : Index a b) : SourceIndex a b := by
  let S := (toIndex_surjective a b q).choose
  have hS := (toIndex_surjective a b q).choose_spec
  refine ⟨classMap q.val,liftDatum S,lift_nonzero S,lift_compatible S,lift_stable S,?_⟩
  have h := congrArg (fun i : Index a b => classMap i.val) hS
  exact (congrArg (Quotient.mk translationSetoid) (lift_dimension S)).trans h

theorem indexMap_value {a b : ℕ} (q : Index a b) : (indexMap q).val=classMap q.val := rfl

theorem indexMap_injective (a b : ℕ) : Function.Injective (@indexMap a b) := by
  intro q r h
  apply Subtype.ext
  apply classMap_injective
  simpa only [indexMap_value] using congrArg Subtype.val h

theorem indexMap_surjective (a b : ℕ) (ha : 0<a) : Function.Surjective (@indexMap a b) := by
  rintro ⟨q,S,hn,hD,hs,hq⟩
  obtain ⟨g,hi⟩ := stable_normalization S a b ha hn hD hs
  let T := translateRep g S
  have ht : T.1≠0 := (translated_nonzero g S).mpr hn
  have hd : T.1.mapDomain Prod.fst=pairDimension a b := (translated_original g S).trans hD
  have hst : FiniteSupportStable T.1 (fun v => negativeWeight a b v.1) T.2 :=
    (translated_stability g S (negativeWeight a b)).mpr hs
  let U := KroneckerWeistStableDescent.toDatum T hi a b ht hd hst
  refine ⟨toIndex U,Subtype.ext ?_⟩
  rw [indexMap_value]
  change Quotient.mk translationSetoid (KroneckerWeistDimensionTransport.push (descended T hi).1)=q
  exact (congrArg (Quotient.mk translationSetoid) (descended_dimension T hi)).trans
    ((translated_class g S).trans hq)

def indexEquiv (a b : ℕ) (ha : 0<a) : Index a b ≃ SourceIndex a b :=
  Equiv.ofBijective indexMap ⟨indexMap_injective a b,indexMap_surjective a b ha⟩

theorem sourceIndex_finite (a b : ℕ) (ha : 0<a) : Finite (SourceIndex a b) :=
  Finite.of_surjective indexMap (indexMap_surjective a b ha)

end KroneckerWeistStableIndexEquivalence
end
end

/- Original module: KroneckerWeistIndexedSpaces -/
section
/-! A concrete nonempty topological support-moduli space for every member of the
full source stable localization index; different choices have equal Euler. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistIndexedSpaces
attribute [local instance] Classical.decEq Classical.propDecidable
open KroneckerWeistCoverEmbedding KroneckerWeistOrbitTopology
open KroneckerWeistStableIndexEquivalence KroneckerWeistClassInjection
open KroneckerQuiverPullbackComposition KroneckerManuscriptCoverParameters
open KroneckerFiniteSupportStability KroneckerCanonicalSupportOrbit

variable (a b : ℕ)
def representative (q : SourceIndex a b) : SupportedRepresentation cover := q.property.choose

theorem representative_spec (q : SourceIndex a b) :
    (representative a b q).1≠0 ∧ (representative a b q).1.mapDomain Prod.fst=pairDimension a b ∧
    FiniteSupportStable (representative a b q).1 (fun v => negativeWeight a b v.1)
      (representative a b q).2 ∧ Quotient.mk translationSetoid (representative a b q).1=q.val :=
  q.property.choose_spec

def space (q : SourceIndex a b) : TopCat.{0} := coverSpace (representative a b q).1 a b

theorem space_nonempty (q : SourceIndex a b) : Nonempty (space a b q) :=
  (nonempty_iff cover (representative a b q).1 _).mpr
    ⟨(representative a b q).2,(representative_spec a b q).2.2.1⟩

end KroneckerWeistIndexedSpaces
end
end
end

section

/- Original module: KroneckerSourceWeightIndivisibility -/
section
/-! Primitive base dimensions give induced weight indivisibility on ANY lifted
vertex set over the two base vertices, including Weist's disconnected cover. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceWeightIndivisibility
open KroneckerManuscriptCoverParameters KroneckerPositiveFiberTotals
attribute [local instance] Classical.decEq Classical.propDecidable

variable {V : Type} (side : V → Fin 2)

theorem zero_weight_zero_or_full (d e : V →₀ ℕ) (a b : ℕ)
    (hc : a.Coprime b) (hd : d.mapDomain side=pairDimension a b) (hle : e≤d)
    (hw : b*(e.mapDomain side 0)=a*(e.mapDomain side 1)) : e=0 ∨ e=d := by
  have hbound := Finsupp.mapDomain_mono (f:=side) hle
  rw [hd] at hbound
  have hu : e.mapDomain side 0≤a := by simpa using hbound 0
  have hv : e.mapDomain side 1≤b := by simpa using hbound 1
  rcases KroneckerCoprimeKingNumerator.equality_zero_or_full hc hu hv hw with hz | hf
  · left
    apply (zero_iff side e).mp
    ext i
    fin_cases i <;> simp [hz.1,hz.2]
  · right
    apply comparable_equal side e d hle
    rw [hd]
    ext i
    fin_cases i <;> simp [hf.1,hf.2]

end KroneckerSourceWeightIndivisibility
end
end

/- Original module: KroneckerSourceWeightFormula -/
section
/-! The induced character on the source cover has exactly the negative
manuscript numerator. Weight indivisibility follows for every subdimension. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceWeightFormula
open KroneckerManuscriptCoverParameters KroneckerSourceWeightIndivisibility
attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators

variable {V : Type} (side : V → Fin 2)

theorem induced_weight_formula (e : V →₀ ℕ) (a b : ℕ) :
    e.sum (fun v n => negativeWeight a b (side v)*(n : ℤ)) =
      (b : ℤ)*(e.mapDomain side 0 : ℤ)-(a : ℤ)*(e.mapDomain side 1 : ℤ) := by
  have he : (e.mapDomain side).sum (fun i n => negativeWeight a b i*(n : ℤ)) =
      e.sum (fun v n => negativeWeight a b (side v)*(n : ℤ)) :=
    Finsupp.sum_mapDomain_index (by intro i;simp) (by intro i n m;simp [mul_add])
  rw [←he,Finsupp.sum_fintype _ _ (by intro i;simp)]
  simp [Fin.sum_univ_two,negativeWeight,sub_eq_add_neg]

theorem induced_weight_indivisible (d e : V →₀ ℕ) (a b : ℕ)
    (hc : a.Coprime b) (hd : d.mapDomain side=pairDimension a b) (hle : e≤d)
    (hw : e.sum (fun v n => negativeWeight a b (side v)*(n : ℤ))=0) : e=0 ∨ e=d := by
  apply zero_weight_zero_or_full side d e a b hc hd hle
  rw [induced_weight_formula,sub_eq_zero] at hw
  exact_mod_cast hw

end KroneckerSourceWeightFormula
end
end

/- Original module: KroneckerWeistSlopeDictionary -/
section
/-! Exact translation of Weist's source-fraction slope convention into the
manuscript's positive numerator, including the proper primitive boundary. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistSlopeDictionary




end KroneckerWeistSlopeDictionary
end
end

/- Original module: KroneckerWeistApplicationGates -/
section
/-! Source hypotheses for the actual three-arrow base and every compatible
finite-support word-cover dimension. No localization or positivity is assumed
in this module. Indivisibility quantifies over ALL bounded subdimensions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistApplicationGates
open KroneckerPublishedModuli KroneckerManuscriptCoverParameters
open KroneckerWeistCoverEmbedding KroneckerFiniteSupportInducedQuiver
open KroneckerSupportDimensionPushforward KroneckerSourceWeightFormula
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

@[reducible] def base (a b : ℕ) : Datum where
  V := Fin 2
  A := Fin 3
  vertices := inferInstance
  arrows := inferInstance
  source := KroneckerCanonicalKroneckerModuli.source 3
  target := KroneckerCanonicalKroneckerModuli.target 3
  dimension := KroneckerCanonicalKroneckerModuli.dimension a b
  weight := negativeWeight a b


theorem base_dimension (a b : ℕ) (v : Fin 2) :
    (base a b).dimension v = pairDimension a b v := by
  fin_cases v <;> simp [KroneckerCanonicalKroneckerModuli.dimension]

theorem base_acyclic (a b : ℕ) : Acyclic (base a b) :=
  ⟨Fin.val,fun _ => by change (0 : ℕ)<1; decide⟩

theorem base_connected (a b : ℕ) : Connected (base a b) := by
  intro u v
  change Fin 2 at u v
  fin_cases u <;> fin_cases v
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨(0 : Fin 3),Or.inl ⟨rfl,rfl⟩⟩
  · exact Relation.ReflTransGen.single ⟨(0 : Fin 3),Or.inr ⟨rfl,rfl⟩⟩
  · exact Relation.ReflTransGen.refl

theorem base_nonzero (a b : ℕ) (ha : 0<a) : Nonzero (base a b) := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  change a=0 at h0
  omega

theorem base_balanced (a b : ℕ) : Balanced (base a b) := by
  simp [KroneckerPublishedModuli.Balanced,base,negativeWeight,KroneckerCanonicalKroneckerModuli.dimension,
    Fin.sum_univ_two,mul_comm]

theorem word_cover_dictionary (a b : ℕ) : wordCover (base a b) = cover := rfl

theorem compatible_dictionary (a b : ℕ) (d : cover.V →₀ ℕ) :
    Compatible (base a b) d ↔ d.mapDomain Prod.fst = pairDimension a b := by
  constructor
  · intro h
    apply Finsupp.ext
    intro v
    exact (h v).trans (base_dimension a b v)
  · intro h v
    exact (congrArg (fun e : Fin 2 →₀ ℕ => e v) h).trans (base_dimension a b v).symm


theorem cover_acyclic (a b : ℕ) (d : cover.V →₀ ℕ) :
    Acyclic (coverDatum (base a b) d) :=
  ⟨fun v => v.val.1.val,fun _ => by change (0 : ℕ)<1; decide⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem compatible_nonzero (a b : ℕ) (ha : 0<a) (d : cover.V →₀ ℕ)
    (hd : d.mapDomain Prod.fst=pairDimension a b) : d≠0 := by
  intro hz
  have h := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hd
  simp [hz] at h
  omega

theorem cover_nonzero (a b : ℕ) (d : cover.V →₀ ℕ) (hd : d≠0) :
    Nonzero (coverDatum (base a b) d) := by
  intro h
  apply hd
  ext v
  by_cases hv : v∈d.support
  · exact congrFun h ⟨v,hv⟩
  · exact Finsupp.notMem_support_iff.mp hv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem cover_balanced (a b : ℕ) (d : cover.V →₀ ℕ)
    (hd : d.mapDomain Prod.fst=pairDimension a b) : Balanced (coverDatum (base a b) d) := by
  have hp : (vector d).mapDomain (fun v => v.val.1)=pairDimension a b :=
    (vector_push d Prod.fst).trans hd
  have h := induced_weight_formula (fun v : SupportVertex d => v.val.1) (vector d) a b
  rw [hp,pairDimension_zero,pairDimension_one] at h
  rw [Finsupp.sum_fintype _ _ (by intro v;simp)] at h
  change (∑ v : SupportVertex d,negativeWeight a b v.val.1*(d v.val : ℤ))=0
  simpa [vector,supportDimension,mul_comm] using h

theorem cover_indivisible (a b : ℕ) (hc : a.Coprime b) (d : cover.V →₀ ℕ)
    (hd : d.mapDomain Prod.fst=pairDimension a b) : Indivisible (coverDatum (base a b) d) := by
  intro e hle hw
  let E : SupportVertex d →₀ ℕ := Finsupp.equivFunOnFinite.symm e
  have hp : (vector d).mapDomain (fun v => v.val.1)=pairDimension a b :=
    (vector_push d Prod.fst).trans hd
  have hE : E≤vector d := hle
  have hz : E.sum (fun v n => negativeWeight a b v.val.1*(n : ℤ))=0 := by
    rw [Finsupp.sum_fintype _ _ (by intro v;simp)]
    exact hw
  rcases induced_weight_indivisible (fun v : SupportVertex d => v.val.1)
    (vector d) E a b hc hp hE hz with h0 | hfull
  · left; exact congrArg DFunLike.coe h0
  · right; exact congrArg DFunLike.coe hfull

end KroneckerWeistApplicationGates
end
end
end

section

/-! The manuscript's actual counted family gives distinct published-translation
classes, each realized by a genuine stable representation on Weist's cover. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistCountedRealization
open KroneckerWeistClassInjection KroneckerWeistStablePush
open KroneckerWeistDimensionTransport KroneckerWeistCoverEmbedding
open KroneckerManuscriptCountedIndex KroneckerManuscriptLocalizationIndex
open KroneckerManuscriptCoverParameters KroneckerEnumeratedCoverClasses
open KroneckerFiniteSupportStability KroneckerQuiverPullbackComposition
attribute [local instance] Classical.decEq Classical.propDecidable

variable {n a : ℕ} {x : ℝ} (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a)

def publishedClass (q : {q // q ∈ enumeratedCoverClasses hx ha}) : Class :=
  classMap (countedIndex hx ha q).val

theorem publishedClass_injective : Function.Injective (publishedClass hx ha) := by
  intro q r h
  apply countedIndex_injective hx ha
  apply Subtype.ext
  exact classMap_injective h


def publishedClasses : Finset Class :=
  (enumeratedCoverClasses hx ha).attach.image (publishedClass hx ha)

theorem published_card : (publishedClasses hx ha).card=(enumeratedCoverClasses hx ha).card := by
  rw [publishedClasses,Finset.card_image_of_injective _ (publishedClass_injective hx ha),Finset.card_attach]

/-- This is a bound for concrete published-cover dimension classes, not yet
an application of the localization theorem to analytic moduli spaces. -/
theorem uniform_published_count : ∃ A B : ℝ, 0<A ∧ 0<B ∧
    ∀ (n a : ℕ) (x : ℝ) (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a),
      KroneckerManuscriptSupportBound.manuscriptLower n a x A B ≤
        ((publishedClasses hx ha).card : ℝ) := by
  obtain ⟨A,B,hA,hB,H⟩ := KroneckerManuscriptCoverBound.uniform_manuscript_cover_bound
  exact ⟨A,B,hA,hB,fun n a x hx ha => by rw [published_card];exact H n a x hx ha⟩

end KroneckerWeistCountedRealization
end
end

