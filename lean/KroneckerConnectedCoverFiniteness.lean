import KroneckerConnectedDeckNormalization
import Mathlib.Basic.Finite.Prod

set_option autoImplicit false
noncomputable section
namespace KroneckerConnectedCoverFiniteness
open KroneckerReducedColorWords KroneckerCoverSupportRadius
open KroneckerConnectedDeckNormalization KroneckerDeckDimensionClasses
open KroneckerBoundedCoverDimensions

abbrev WordBall (N : ℕ) := {w : Word // w.val.length ≤ N}

def wordCode (N : ℕ) (w : WordBall N) : Fin (N+1) × (Fin N → Option Color) :=
  ⟨⟨w.val.val.length, by omega⟩, fun i => w.val.val[i.val]?⟩

theorem wordCode_injective (N : ℕ) : Function.Injective (wordCode N) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have hl : x.val.val.length = y.val.val.length := congrArg (fun z => z.1.val) h
  apply List.ext_getElem hl
  intro i hx hy
  have hi : i < N := lt_of_lt_of_le hx x.property
  have he := congrFun (congrArg Prod.snd h) ⟨i, hi⟩
  simpa [wordCode, List.getElem?_eq_getElem, hx, hy] using he

instance wordBallFinite (N : ℕ) : Finite (WordBall N) :=
  Finite.of_injective (wordCode N) (wordCode_injective N)

abbrev BoundedDimensions (N : ℕ) :=
  {d : Word →₀ ℕ // (∀ w ∈ d.support, w.val.length ≤ N) ∧ ∀ w, d w ≤ N}

def dimensionCode (N : ℕ) (d : BoundedDimensions N) : WordBall N → Fin (N+1) :=
  fun w => ⟨d.val w.val, Nat.lt_succ_of_le (d.property.2 w.val)⟩

theorem dimensionCode_injective (N : ℕ) : Function.Injective (dimensionCode N) := by
  intro d e h
  apply Subtype.ext
  ext w
  by_cases hw : w.val.length ≤ N
  · exact congrArg Fin.val (congrFun h ⟨w, hw⟩)
  · have hd : w ∉ d.val.support := fun hm => hw (d.property.1 w hm)
    have he : w ∉ e.val.support := fun hm => hw (e.property.1 w hm)
    rw [Finsupp.notMem_support_iff.mp hd, Finsupp.notMem_support_iff.mp he]

instance boundedDimensionsFinite (N : ℕ) : Finite (BoundedDimensions N) :=
  Finite.of_injective (dimensionCode N) (dimensionCode_injective N)

/-- Connected dimension vectors of fixed total dimension have only finitely
many classes modulo color- and bipartition-preserving deck transformations. -/
theorem connected_classes_finite (N : ℕ) :
    Set.Finite {q : DimensionClass | ∃ d : Word →₀ ℕ,
      Quotient.mk dimensionSetoid d = q ∧ d.support.Nonempty ∧
      (supportGraph d).Preconnected ∧ d.sum (fun _ n => n) = N} := by
  classical
  let B : Set (Word →₀ ℕ) := {d | (∀ w ∈ d.support, w.val.length ≤ N) ∧ ∀ w, d w ≤ N}
  have hB : B.Finite := by
    change Finite (BoundedDimensions N)
    infer_instance
  apply (hB.image (Quotient.mk dimensionSetoid)).subset
  rintro q ⟨d, rfl, hn, hc, ht⟩
  obtain ⟨e, he, htotal, hradius⟩ := normalize_connected_dimensions d hn hc
  refine ⟨e, ⟨?_, ?_⟩, (Quotient.sound he).symm⟩
  · simpa [ht] using hradius
  · intro w
    have h := coordinate_le_total e w
    simpa [htotal, ht] using h

end KroneckerConnectedCoverFiniteness
