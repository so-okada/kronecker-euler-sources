import KroneckerManuscriptCoverParameters

/-! Fixed manuscript dimensions, actual stable representations, and weighted
unmarked support classes have exactly the same finite deck-dimension index.
Global permutations of the arrow colors are not included in the relation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptLocalizationIndex
open KroneckerManuscriptCoverParameters KroneckerDeckDimensionClasses
open KroneckerReducedColorWords KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerFiniteSupportStability
open KroneckerUniversalWordBaseProjection KroneckerUniversalFixedStableIndex
open KroneckerWeightedColoredSupportIso
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev Index (a b : ℕ) := FixedStableIndex (pairDimension a b) (negativeWeight a b)

instance indexFinite (a b : ℕ) : Finite (Index a b) :=
  KroneckerUniversalStableIndexBounds.fixedIndex_finite _ _

noncomputable instance indexFintype (a b : ℕ) : Fintype (Index a b) := Fintype.ofFinite _

/-- A genuine representation witness, with the manuscript's stability sign. -/
def Datum (a b : ℕ) :=
  {S : SupportedRepresentation coloredCoverQuiver // S.1 ≠ 0 ∧
    S.1.mapDomain baseVertex = pairDimension a b ∧ ManuscriptStable S.1 a b S.2}

def toIndex {a b : ℕ} (S : Datum a b) : Index a b :=
  ⟨Quotient.mk dimensionSetoid S.val.1,S.val,S.property.1,S.property.2.1,
    (stability_sign_dictionary _ _ _ S.property.2.1 _).mpr S.property.2.2,rfl⟩

theorem toIndex_surjective (a b : ℕ) : Function.Surjective (@toIndex a b) := by
  rintro ⟨q,S,hn,hD,hs,rfl⟩
  exact ⟨⟨S,hn,hD,(stability_sign_dictionary _ _ _ hD _).mp hs⟩,rfl⟩

theorem toIndex_eq_iff (a b : ℕ) (S T : Datum a b) :
    toIndex S = toIndex T ↔ Nonempty (ColoredIso coloring coloring S.val.1 T.val.1) := by
  have hc := KroneckerDirectSumStableSupportTree.stable_support_connected
    coloredCoverQuiver S.val.1 S.property.1 (negativeWeight a b ∘ baseVertex) S.val.2
    ((stability_sign_dictionary _ _ _ S.property.2.1 _).mpr S.property.2.2)
  constructor
  · intro h
    apply (KroneckerColoredSupportDeckRelations.word_relation_iff_colored _ _ hc).mp
    exact Quotient.exact (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact Quotient.sound ((KroneckerColoredSupportDeckRelations.word_relation_iff_colored _ _ hc).mpr h)

/-- Different stable representations with the same weighted support are one
index. This quotient counts support dimensions, not representation isomorphisms. -/
def unmarkedSetoid (a b : ℕ) : Setoid (Datum a b) :=
  Setoid.comap (fun S => S.val.1) (shapeSetoid coloring)

abbrev Unmarked (a b : ℕ) := Quotient (unmarkedSetoid a b)

def unmarkedToIndex (a b : ℕ) : Unmarked a b → Index a b :=
  Quotient.lift toIndex (fun S T h => (toIndex_eq_iff a b S T).mpr h)

theorem unmarkedToIndex_bijective (a b : ℕ) : Function.Bijective (unmarkedToIndex a b) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | h S =>
      induction y using Quotient.inductionOn with | h T =>
        intro h
        exact Quotient.sound ((toIndex_eq_iff a b S T).mp h)
  · intro q
    obtain ⟨S,hS⟩ := toIndex_surjective a b q
    exact ⟨Quotient.mk (unmarkedSetoid a b) S,hS⟩

def unmarkedEquiv (a b : ℕ) : Unmarked a b ≃ Index a b :=
  Equiv.ofBijective (unmarkedToIndex a b) (unmarkedToIndex_bijective a b)

instance unmarkedFinite (a b : ℕ) : Finite (Unmarked a b) :=
  Finite.of_injective (unmarkedEquiv a b) (unmarkedEquiv a b).injective



end KroneckerManuscriptLocalizationIndex
