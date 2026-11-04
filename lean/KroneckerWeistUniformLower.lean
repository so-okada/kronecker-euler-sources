import KroneckerEmptySingularEuler
import KroneckerWeistApplicationGates

section

/- Original module: KroneckerLocalizationApplication -/
section
/-!
Finite numerical step in manuscript lem:cover-localization.
The Euler invariant is actual rational singular-homology Euler characteristic.
The equality hLocalization and positivity hPositive are explicit APPLIED
inputs. Their geometric/source instantiation is NOT proved by this module.
For the intended application they follow from Weist (published 2013),
Corollaries 3.16 and 3.11, only after the recorded index, moduli, stability,
finiteness and Euler-convention obligations have been discharged.

The lower-bound route needs nonempty selected summands and positivity;
it does not need singleton moduli, Euler=1, or a homology decomposition.
-/
noncomputable section
set_option autoImplicit false
namespace KroneckerLocalizationApplication
open KroneckerOrdinarySingularEuler
open scoped BigOperators

theorem distinct_nonempty_localization_lower
    {I D : Type} [Fintype I] [Fintype D]
    (Y : TopCat.{0}) (X : I → TopCat.{0})
    (hY : Admissible Y) (hX : ∀ i, Admissible (X i))
    (hLocalization : ordinaryEuler Y hY = ∑ i, ordinaryEuler (X i) (hX i))
    (hPositive : ∀ i, Nonempty (X i) → 1 ≤ ordinaryEuler (X i) (hX i))
    (index : D → I) (hIndex : Function.Injective index)
    (hRealized : ∀ d, Nonempty (X (index d))) :
    (Fintype.card D : ℤ) ≤ ordinaryEuler Y hY := by
  classical
  have hnonneg : ∀ i, 0 ≤ ordinaryEuler (X i) (hX i) := by
    intro i
    by_cases hi : Nonempty (X i)
    · exact le_trans (by norm_num : (0 : ℤ) ≤ 1) (hPositive i hi)
    · let : IsEmpty (X i) := ⟨fun x => hi ⟨x⟩⟩
      have he : ordinaryEuler (X i) (hX i) = 0 := ordinaryEuler_empty (X i)
      exact he.ge
  rw [hLocalization]
  calc
    (Fintype.card D : ℤ) = ∑ _d : D, (1 : ℤ) := by simp
    _ ≤ ∑ d : D, ordinaryEuler (X (index d)) (hX (index d)) :=
      Finset.sum_le_sum (fun d _ => hPositive (index d) (hRealized d))
    _ = ∑ i ∈ Finset.univ.image index, ordinaryEuler (X i) (hX i) := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => hIndex h
    _ ≤ ∑ i : I, ordinaryEuler (X i) (hX i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact hnonneg i

end KroneckerLocalizationApplication
end
end

/- Original module: KroneckerManuscriptCountedEuler -/
section
/-! Quantitative lower bound from the actual counted family, conditional on the
explicit geometric application gates. No supplied Euler-valued sequence is used.
This does NOT discharge identification with the published moduli spaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptCountedEuler
open KroneckerManuscriptLocalizationIndex KroneckerManuscriptCountedIndex
open KroneckerOrdinarySingularEuler KroneckerManuscriptSupportBound
open KroneckerEnumeratedCoverClasses
open scoped BigOperators

/-- Application data, not a new literature axiom. The field `realizes` must be
proved by identifying genuine stable representations with points of cover moduli.
All fields remain explicit hypotheses of the numerical consequences below. -/
structure GeometricApplication (a b : ℕ) where
  base : TopCat.{0}
  cover : Index a b → TopCat.{0}
  base_admissible : Admissible base
  cover_admissible : ∀ q, Admissible (cover q)
  localizes : ordinaryEuler base base_admissible =
    ∑ q, ordinaryEuler (cover q) (cover_admissible q)
  positive : ∀ q, Nonempty (cover q) → 1 ≤ ordinaryEuler (cover q) (cover_admissible q)
  realizes : ∀ S : Datum a b, Nonempty (cover (toIndex S))

theorem all_index_realized {a b : ℕ} (G : GeometricApplication a b) (q : Index a b) :
    Nonempty (G.cover q) := by
  obtain ⟨S,rfl⟩ := toIndex_surjective a b q
  exact G.realizes S

theorem full_index_euler_lower {a b : ℕ} (G : GeometricApplication a b) :
    (Fintype.card (Index a b) : ℤ) ≤ ordinaryEuler G.base G.base_admissible := by
  exact KroneckerLocalizationApplication.distinct_nonempty_localization_lower
    G.base G.cover G.base_admissible G.cover_admissible G.localizes G.positive
    id Function.injective_id (all_index_realized G)


/-- Uniform constants come from the proved combinatorial count, not the
application data. The geometric premises remain universally quantified. -/
theorem uniform_conditional_euler_bound : ∃ A B : ℝ, 0<A ∧ 0<B ∧
    ∀ (n a : ℕ) (x : ℝ) (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a)
      (G : GeometricApplication a (a+n+2)),
      manuscriptLower n a x A B ≤ (ordinaryEuler G.base G.base_admissible : ℝ) := by
  obtain ⟨A,B,hA,hB,H⟩ := uniform_manuscript_index_bound
  refine ⟨A,B,hA,hB,fun n a x hx ha G => ?_⟩
  exact (H n a x hx ha).trans (by exact_mod_cast full_index_euler_lower G)

end KroneckerManuscriptCountedEuler
end
end

/- Original module: KroneckerManuscriptCoverOrbit -/
section
/-! Concrete nonempty quotient spaces for each finite cover index. Their topology
is induced from complex arrow matrices; no discrete or arbitrary topology is used.
King/Weist identification, finite homology and positivity remain external gates. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptCoverOrbit
open KroneckerManuscriptLocalizationIndex KroneckerManuscriptCoverParameters
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerUniversalWordBaseProjection

attribute [local instance] Classical.decEq Classical.propDecidable

variable (a b : ℕ)

def representative (q : Index a b) : Datum a b :=
  (toIndex_surjective a b q).choose

theorem representative_index (q : Index a b) : toIndex (representative a b q) = q :=
  (toIndex_surjective a b q).choose_spec

noncomputable instance supportVertices (q : Index a b) :
    Fintype (supportQuiver coloredCoverQuiver (representative a b q).val.1).V :=
  Fintype.ofFinset (representative a b q).val.1.support (by intro v; rfl)

noncomputable instance supportArrows (q : Index a b) :
    Fintype (supportQuiver coloredCoverQuiver (representative a b q).val.1).A :=
  Fintype.ofEquiv _ (KroneckerColoredCoverPairDictionary.supportArrowEquiv
    (representative a b q).val.1).symm

def space (q : Index a b) : TopCat.{0} :=
  KroneckerCanonicalStableOrbit.space
    (supportQuiver coloredCoverQuiver (representative a b q).val.1).source
    (supportQuiver coloredCoverQuiver (representative a b q).val.1).target
    (supportDimension (representative a b q).val.1)
    (supportCharacter (representative a b q).val.1 (negativeWeight a b ∘ baseVertex))

theorem space_nonempty (q : Index a b) : Nonempty (space a b q) := by
  let S := representative a b q
  apply (KroneckerCanonicalStableOrbit.space_nonempty_iff _ _ _ _).mpr
  refine ⟨restrictToSupport coloredCoverQuiver S.val.1 S.val.2, ?_⟩
  apply (finiteSupportStable_iff_restrict coloredCoverQuiver S.val.1 _ S.val.2).mp
  exact (stability_sign_dictionary S.val.1 a b S.property.2.1 S.val.2).mpr S.property.2.2

end KroneckerManuscriptCoverOrbit
end
end

/- Original module: KroneckerConcreteLocalizationLower -/
section
/-! The conditional numerical theorem now refers to fixed concrete matrix-orbit
quotient spaces on both sides. Only finite homology, localization, and positivity
remain premises. Their source application, including the King comparison and
Weist deck-index convention, must still be established/documented. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerConcreteLocalizationLower
open KroneckerOrdinarySingularEuler KroneckerManuscriptLocalizationIndex
open KroneckerManuscriptCountedEuler KroneckerManuscriptSupportBound
open scoped BigOperators

structure AppliedInput (a b : ℕ) where
  base_admissible : Admissible (KroneckerCanonicalKroneckerModuli.space 3 a b)
  cover_admissible : ∀ q, Admissible (KroneckerManuscriptCoverOrbit.space a b q)
  localizes : ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a b) base_admissible =
    ∑ q, ordinaryEuler (KroneckerManuscriptCoverOrbit.space a b q) (cover_admissible q)
  positive : ∀ q, 1 ≤ ordinaryEuler (KroneckerManuscriptCoverOrbit.space a b q) (cover_admissible q)

def application {a b : ℕ} (H : AppliedInput a b) : GeometricApplication a b where
  base := KroneckerCanonicalKroneckerModuli.space 3 a b
  cover := KroneckerManuscriptCoverOrbit.space a b
  base_admissible := H.base_admissible
  cover_admissible := H.cover_admissible
  localizes := H.localizes
  positive := fun q _ => H.positive q
  realizes := fun S => KroneckerManuscriptCoverOrbit.space_nonempty a b (toIndex S)

theorem uniform_concrete_lower : ∃ A B : ℝ, 0<A ∧ 0<B ∧
    ∀ (n a : ℕ) (x : ℝ) (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a)
      (H : AppliedInput a (a+n+2)),
      manuscriptLower n a x A B ≤
        (ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+n+2)) H.base_admissible : ℝ) := by
  obtain ⟨A,B,hA,hB,h⟩ := uniform_conditional_euler_bound
  exact ⟨A,B,hA,hB,fun n a x hx ha H => h n a x hx ha (application H)⟩

end KroneckerConcreteLocalizationLower
end
end

/- Original module: KroneckerWeistIndexedHomeomorphism -/
section
/-! The previously proved bijection of stable localization indices identifies
not only dimensions but the full canonical quotient-topological summands. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistIndexedHomeomorphism
open KroneckerWeistStableIndexEquivalence KroneckerWeistOrbitTopology
open KroneckerWeistClassInjection KroneckerWeistClassTopology
open KroneckerManuscriptLocalizationIndex KroneckerWeistDimensionTransport

def indexedHomeomorph {a b : ℕ} (q : Index a b) :
    KroneckerWeistIndexedSpaces.space a b (indexMap q) ≃ₜ
      KroneckerManuscriptCoverOrbit.space a b q := by
  let S := KroneckerManuscriptCoverOrbit.representative a b q
  have hs : Quotient.mk translationSetoid (push S.val.1)=classMap q.val :=
    congrArg (fun i : Index a b => classMap i.val)
      (KroneckerManuscriptCoverOrbit.representative_index a b q)
  have hr := (KroneckerWeistIndexedSpaces.representative_spec a b (indexMap q)).2.2.2
  have he := classHomeomorph a b (hr.trans hs.symm)
  exact he.trans (embeddingHomeomorph S.val.1 a b)

end KroneckerWeistIndexedHomeomorphism
end
end

/- Original module: KroneckerWeistLocalizationTransfer -/
section
/-! The geometric source application can be stated on the full free-word index.
The proved bijection and homeomorphisms transfer its actual singular Euler sum to
the connected model. Localization and positivity remain explicit hypotheses. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistLocalizationTransfer
open KroneckerWeistStableIndexEquivalence KroneckerWeistIndexedHomeomorphism
open KroneckerOrdinarySingularEuler KroneckerHomologyHomeomorphism
open KroneckerConcreteLocalizationLower
open scoped BigOperators

structure SourceInput (a b : ℕ) [Fintype (SourceIndex a b)] where
  base_admissible : Admissible (KroneckerCanonicalKroneckerModuli.space 3 a b)
  cover_admissible : ∀ q, Admissible (KroneckerWeistIndexedSpaces.space a b q)
  localizes : ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a b) base_admissible =
    ∑ q, ordinaryEuler (KroneckerWeistIndexedSpaces.space a b q) (cover_admissible q)
  positive : ∀ q, 1≤ordinaryEuler (KroneckerWeistIndexedSpaces.space a b q) (cover_admissible q)

variable {a b : ℕ} [Fintype (SourceIndex a b)]

def connectedInput (ha : 0<a) (H : SourceInput a b) : AppliedInput a b where
  base_admissible := H.base_admissible
  cover_admissible q := admissible_transfer (indexedHomeomorph q).symm (H.cover_admissible (indexMap q))
  localizes := by
    rw [H.localizes]
    rw [← (indexEquiv a b ha).sum_comp (fun q =>
      ordinaryEuler (KroneckerWeistIndexedSpaces.space a b q) (H.cover_admissible q))]
    apply Finset.sum_congr rfl
    intro q _
    exact euler_eq (indexedHomeomorph q) _ _
  positive q := by
    have he := euler_eq (indexedHomeomorph q) (H.cover_admissible (indexMap q))
      (admissible_transfer (indexedHomeomorph q).symm (H.cover_admissible (indexMap q)))
    rw [← he]
    exact H.positive (indexMap q)

end KroneckerWeistLocalizationTransfer
end
end
end

section

/-! The uniform counted-family lower bound on canonical base moduli, with the
remaining geometric input now stated exactly on free-word cover summands. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistUniformLower
open KroneckerWeistStableIndexEquivalence KroneckerWeistLocalizationTransfer
open KroneckerManuscriptSupportBound KroneckerOrdinarySingularEuler

theorem source_total_positive (n a : ℕ) (x : ℝ) (hx : 100000≤x)
    (ha : ((n : ℝ)+2)*x=a) : 0<a := by
  have hn : (0 : ℝ)≤n := Nat.cast_nonneg n
  have hp : (0 : ℝ)<a := by nlinarith
  exact_mod_cast hp

def sourceFintype (n a : ℕ) (x : ℝ) (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a) :
    Fintype (SourceIndex a (a+n+2)) := by
  letI := sourceIndex_finite a (a+n+2) (source_total_positive n a x hx ha)
  exact Fintype.ofFinite _

theorem uniform_source_lower : ∃ A B : ℝ,0<A ∧ 0<B ∧
    ∀ (n a : ℕ) (x : ℝ) (hx : 100000≤x) (ha : ((n : ℝ)+2)*x=a)
      (I : Fintype (SourceIndex a (a+n+2))) (H : @SourceInput a (a+n+2) I),
      manuscriptLower n a x A B ≤
        (ordinaryEuler (KroneckerCanonicalKroneckerModuli.space 3 a (a+n+2)) H.base_admissible : ℝ) := by
  obtain ⟨A,B,hA,hB,h⟩ := KroneckerConcreteLocalizationLower.uniform_concrete_lower
  refine ⟨A,B,hA,hB,?_⟩
  intro n a x hx ha I H
  let := I
  exact h n a x hx ha (connectedInput (source_total_positive n a x hx ha) H)

end KroneckerWeistUniformLower
end
end

