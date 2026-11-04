import KroneckerStableCoverIndexFinite

/-! Exact dictionary from oriented color/source arrows on the infinite cover
to the earlier ordered-adjacent-pair finite-support cover. This transports actual
representations and all-subrepresentation stability, then applies the previously
proved finite deck-dimension index theorem to ambient representations. -/
set_option autoImplicit false
namespace KroneckerColoredCoverPairDictionary
open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerFiniteQuiverPullbackStability
open KroneckerReducedColorWords KroneckerColorWordAction KroneckerColorWordCover
open KroneckerStableCoverIndexFinite KroneckerDeckDimensionClasses

local instance : DecidableEq coloredCoverQuiver.V := inferInstanceAs (DecidableEq Word)

abbrev ColorArrow (d : Word →₀ ℕ) :=
  SupportArrow coloredCoverQuiver.source coloredCoverQuiver.target d

def toPairArrow (d : Word →₀ ℕ) (a : ColorArrow d) : CoverArrow d :=
  ⟨(⟨a.val.2.val, a.property.1⟩,
     ⟨toggle a.val.1 a.val.2.val, a.property.2⟩),
    a.val.2.property, ⟨a.val.1, rfl⟩⟩

theorem toPairArrow_injective (d : Word →₀ ℕ) : Function.Injective (toPairArrow d) := by
  intro a b h
  have hs := congrArg (fun p : CoverArrow d => p.val.1.val) h
  have ht := congrArg (fun p : CoverArrow d => p.val.2.val) h
  change a.val.2.val = b.val.2.val at hs
  change toggle a.val.1 a.val.2.val = toggle b.val.1 b.val.2.val at ht
  apply Subtype.ext
  apply Prod.ext
  · apply toggle_color_injective a.val.2.val
    rw [hs]
    simpa only [hs] using ht
  · exact Subtype.ext hs

theorem toPairArrow_surjective (d : Word →₀ ℕ) : Function.Surjective (toPairArrow d) := by
  intro p
  obtain ⟨c, hc⟩ := p.property.2
  refine ⟨⟨(c, ⟨p.val.1.val, p.property.1⟩), p.val.1.property, ?_⟩, ?_⟩
  · change toggle c p.val.1.val ∈ d.support
    rw [hc]
    exact p.val.2.property
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Subtype.ext hc

noncomputable def supportArrowEquiv (d : Word →₀ ℕ) : ColorArrow d ≃ CoverArrow d :=
  Equiv.ofBijective (toPairArrow d) ⟨toPairArrow_injective d, toPairArrow_surjective d⟩

def pairQuiver (d : Word →₀ ℕ) : TypedQuiver where
  V := SupportVertex d
  A := CoverArrow d
  source a := a.val.1
  target a := a.val.2

noncomputable def pairSupportIso (d : Word →₀ ℕ) :
    TypedQuiverIso (supportQuiver coloredCoverQuiver d) (pairQuiver d) where
  vertexEquiv := Equiv.refl _
  arrowEquiv := supportArrowEquiv d
  map_source _ := rfl
  map_target _ := rfl

noncomputable def coordinateDimension (d : Word →₀ ℕ) : SupportVertex d →₀ ℕ := by
  classical
  exact Finsupp.onFinset Finset.univ (fun v => d v.val) (by intros; exact Finset.mem_univ _)

/-- Equivalence between the two already defined representation presentations. -/
noncomputable def pairRepresentationEquiv (d : Word →₀ ℕ) :
    CoverRepresentation d ≃
      Representation (supportQuiver coloredCoverQuiver d).source
        (supportQuiver coloredCoverQuiver d).target (supportDimension d) :=
  pullRepresentationEquiv (pairSupportIso d) (coordinateDimension d)

noncomputable local instance supportFintype (d : Word →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)
noncomputable local instance supportQuiverFintype (d : Word →₀ ℕ) :
    Fintype (supportQuiver coloredCoverQuiver d).V := supportFintype d
noncomputable local instance pairQuiverFintype (d : Word →₀ ℕ) :
    Fintype (pairQuiver d).V := supportFintype d

theorem pair_stable_iff (d : Word →₀ ℕ) (θ : SupportVertex d → ℤ)
    (P : CoverRepresentation d) :
    Stable θ (pairRepresentationEquiv d P) ↔ Stable θ P := by
  exact finite_pull_stable_iff (pairSupportIso d) (coordinateDimension d) θ P

noncomputable def toPairRepresentation (d : Word →₀ ℕ)
    (S : Representation coloredCoverQuiver.source coloredCoverQuiver.target (fun w => d w)) :
    CoverRepresentation d := (pairRepresentationEquiv d).symm (restrictToSupport coloredCoverQuiver d S)

/-- Extend the earlier finite-support two-vertex character to every word. -/
def ambientKingWeight (d : Word →₀ ℕ) (w : Word) : ℤ :=
  if KroneckerWordParity.parity w = 0 then
    (d.sum (fun w n => if KroneckerWordParity.parity w = 1 then n else 0) : ℤ)
  else -(d.sum (fun w n => if KroneckerWordParity.parity w = 0 then n else 0) : ℤ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem ambient_stable_iff_pair (d : Word →₀ ℕ)
    (S : Representation coloredCoverQuiver.source coloredCoverQuiver.target (fun w => d w)) :
    FiniteSupportStable d (ambientKingWeight d) S ↔
      Stable (coverKingWeight d) (toPairRepresentation d S) := by
  rw [finiteSupportStable_iff_restrict coloredCoverQuiver d (ambientKingWeight d) S]
  have h := pair_stable_iff d (coverKingWeight d) (toPairRepresentation d S)
  have he : pairRepresentationEquiv d (toPairRepresentation d S) =
      restrictToSupport coloredCoverQuiver d S := (pairRepresentationEquiv d).apply_symm_apply _
  rw [he] at h
  exact h


theorem ambient_stable_support_preconnected_any (d : Word →₀ ℕ) (θ : Word → ℤ)
    (S : Representation coloredCoverQuiver.source coloredCoverQuiver.target (fun w => d w))
    (hS : FiniteSupportStable d θ S) :
    (KroneckerCoverSupportRadius.supportGraph d).Preconnected := by
  have hr := (finiteSupportStable_iff_restrict coloredCoverQuiver d θ S).mp hS
  have he : pairRepresentationEquiv d (toPairRepresentation d S) =
      restrictToSupport coloredCoverQuiver d S := (pairRepresentationEquiv d).apply_symm_apply _
  have hp : Stable (fun v : SupportVertex d => θ v.val) (toPairRepresentation d S) := by
    apply (pair_stable_iff d (fun v => θ v.val) (toPairRepresentation d S)).mp
    rw [he]
    exact hr
  exact stable_cover_support_preconnected d (toPairRepresentation d S) _ hp



end KroneckerColoredCoverPairDictionary
