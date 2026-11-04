import KroneckerFiniteSupportInducedQuiver
import KroneckerDeckDimensionClasses

/-!
# Actual deck pullback of finite-support coordinate representations

The reduced-color-word deck transformations act on the actual colored directed
cover quiver: vertices are words and an arrow is a color together with its
source word.  This module first records the needed notion of typed-quiver
isomorphism, then pulls `Finsupp` dimension vectors and actual coordinate arrow
maps back along such an isomorphism.  Pullback is invertible by reindexing with
the inverse vertex and arrow equivalences.  The final specialization uses the
project's concrete `Deck`, including its proved toggle-commutation law; it is not
an assumed preservation-of-stability interface.
-/

set_option autoImplicit false

namespace KroneckerFiniteSupportDeckRepresentationTransport

open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver
open KroneckerReducedColorWords KroneckerColorWordAction
open KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses

/-- An isomorphism of typed quivers, preserving the source and target of every
actual arrow. -/
structure TypedQuiverIso (Q R : TypedQuiver) where
  vertexEquiv : Q.V ≃ R.V
  arrowEquiv : Q.A ≃ R.A
  map_source : ∀ a, R.source (arrowEquiv a) = vertexEquiv (Q.source a)
  map_target : ∀ a, R.target (arrowEquiv a) = vertexEquiv (Q.target a)

/-- The inverse is an actual typed-quiver map, not merely inverse vertex and
arrow bijections. -/
def TypedQuiverIso.symm {Q R : TypedQuiver} (f : TypedQuiverIso Q R) :
    TypedQuiverIso R Q where
  vertexEquiv := f.vertexEquiv.symm
  arrowEquiv := f.arrowEquiv.symm
  map_source a := by
    apply f.vertexEquiv.injective
    rw [f.vertexEquiv.apply_symm_apply]
    simpa using (f.map_source (f.arrowEquiv.symm a)).symm
  map_target a := by
    apply f.vertexEquiv.injective
    rw [f.vertexEquiv.apply_symm_apply]
    simpa using (f.map_target (f.arrowEquiv.symm a)).symm

/-- Pull a finitely supported dimension vector back along the vertex map. -/
def pullDimension {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) : Q.V →₀ ℕ :=
  Finsupp.equivCongrLeft f.vertexEquiv.symm d

@[simp] theorem pullDimension_apply {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (v : Q.V) :
    pullDimension f d v = d (f.vertexEquiv v) := by
  simp [pullDimension, Finsupp.equivCongrLeft_apply]

/-- Pull every actual arrow matrix back along a typed-quiver isomorphism. -/
noncomputable def pullRepresentation {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ)
    (S : Representation R.source R.target (fun v => d v)) :
    Representation Q.source Q.target (fun v => d (f.vertexEquiv v)) where
  arrow a := by
    rw [← f.map_source a, ← f.map_target a]
    exact S.arrow (f.arrowEquiv a)

/-- Reindex a pulled-back representation with the inverse actual quiver map. -/
noncomputable def unpullRepresentation {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ)
    (T : Representation Q.source Q.target (fun v => d (f.vertexEquiv v))) :
    Representation R.source R.target (fun v => d v) where
  arrow a := by
    rw [← f.arrowEquiv.apply_symm_apply a]
    rw [f.map_source, f.map_target]
    exact T.arrow (f.arrowEquiv.symm a)

/-- Applying a dependent family to propositionally equal indices gives
heterogeneously equal values.  This is the form needed below because an arrow
matrix's type remembers the endpoints of its arrow. -/
theorem dependent_apply_heq {α : Type} {β : α → Sort _}
    (F : (a : α) → β a) {a b : α} (h : a = b) : F a ≍ F b := by
  cases h
  rfl

theorem unpull_pull {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S : Representation R.source R.target (fun v => d v)) :
    unpullRepresentation f d (pullRepresentation f d S) = S := by
  apply representation_ext
  funext a
  simp only [unpullRepresentation, pullRepresentation]
  apply eq_of_heq
  iterate 5
    apply (cast_heq _ _).trans
  exact dependent_apply_heq S.arrow (f.arrowEquiv.apply_symm_apply a)

theorem pull_unpull {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ)
    (T : Representation Q.source Q.target (fun v => d (f.vertexEquiv v))) :
    pullRepresentation f d (unpullRepresentation f d T) = T := by
  apply representation_ext
  funext a
  simp only [unpullRepresentation, pullRepresentation]
  apply eq_of_heq
  iterate 5
    apply (cast_heq _ _).trans
  exact dependent_apply_heq T.arrow (f.arrowEquiv.symm_apply_apply a)

/-- Pullback is an equivalence on actual coordinate representations, with the
inverse defined by the inverse actual quiver map. -/
noncomputable def pullRepresentationEquiv {Q R : TypedQuiver}
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) :
    Representation R.source R.target (fun v => d v) ≃
      Representation Q.source Q.target (fun v => d (f.vertexEquiv v)) where
  toFun := pullRepresentation f d
  invFun := unpullRepresentation f d
  left_inv := unpull_pull f d
  right_inv := pull_unpull f d

/-- The even part of the bipartition of the reduced-word cover. -/
abbrev EvenWord := {w : Word // KroneckerWordParity.parity w = 0}

/-- The actual oriented three-arrow Kronecker cover.  Its arrows are colors
based at even words, so every arrow is directed from the even to the odd part
of the reduced-word tree. -/
def coloredCoverQuiver : TypedQuiver where
  V := Word
  A := Color × EvenWord
  source a := a.2.1
  target a := toggle a.1 a.2.1

/-- A concrete deck transformation transports actual colored arrows, retaining
their color and moving their source word. -/
def deckArrowEquiv (g : Deck) : (Color × EvenWord) ≃ (Color × EvenWord) where
  toFun a :=
    (a.1, ⟨g a.2.1, (g.preserves_parity a.2.1).trans a.2.2⟩)
  invFun a :=
    (a.1, ⟨g.equiv.symm a.2.1,
      ((Deck.symm g).preserves_parity a.2.1).trans a.2.2⟩)
  left_inv a := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact g.equiv.symm_apply_apply a.2.1
  right_inv a := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact g.equiv.apply_symm_apply a.2.1

/-- Every project deck transformation is an actual typed-quiver automorphism of
the colored directed cover. -/
def deckQuiverAuto (g : Deck) : TypedQuiverIso coloredCoverQuiver coloredCoverQuiver where
  vertexEquiv := g.equiv
  arrowEquiv := deckArrowEquiv g
  map_source _ := rfl
  map_target a := (g.commutes a.1 a.2).symm

/-- Actual finite-support dimension pullback by a deck transformation. -/
def deckPullDimension (g : Deck) (d : Word →₀ ℕ) : Word →₀ ℕ :=
  pullDimension (deckQuiverAuto g) d

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem deckPullDimension_apply (g : Deck) (d : Word →₀ ℕ) (w : Word) :
    deckPullDimension g d w = d (g w) := by
  change pullDimension (deckQuiverAuto g) d w = d (g.equiv w)
  rw [pullDimension_apply]
  rfl

/-- Actual deck pullback equivalence on finite-support coordinate
representations of the colored cover. -/
noncomputable def deckPullRepresentationEquiv (g : Deck) (d : Word →₀ ℕ) :
    Representation coloredCoverQuiver.source coloredCoverQuiver.target (fun w => d w) ≃
      Representation coloredCoverQuiver.source coloredCoverQuiver.target
        (fun w => d (g w)) :=
  pullRepresentationEquiv (deckQuiverAuto g) d

end KroneckerFiniteSupportDeckRepresentationTransport
