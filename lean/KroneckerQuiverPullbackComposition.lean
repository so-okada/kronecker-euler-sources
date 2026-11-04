import KroneckerQuiverPullbackStability

/-! Identity and composition laws for actual quiver pullbacks. -/
set_option autoImplicit false
namespace KroneckerQuiverPullbackComposition
open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackSubrepresentations

def TypedQuiverIso.refl (Q : TypedQuiver) : TypedQuiverIso Q Q where
  vertexEquiv := Equiv.refl _
  arrowEquiv := Equiv.refl _
  map_source _ := rfl
  map_target _ := rfl

def TypedQuiverIso.trans {Q R T : TypedQuiver}
    (f : TypedQuiverIso Q R) (g : TypedQuiverIso R T) : TypedQuiverIso Q T where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  arrowEquiv := f.arrowEquiv.trans g.arrowEquiv
  map_source a := (g.map_source (f.arrowEquiv a)).trans (congrArg g.vertexEquiv (f.map_source a))
  map_target a := (g.map_target (f.arrowEquiv a)).trans (congrArg g.vertexEquiv (f.map_target a))

theorem pullDimension_refl (Q : TypedQuiver) (d : Q.V →₀ ℕ) :
    pullDimension (TypedQuiverIso.refl Q) d = d := by
  ext v
  simp [TypedQuiverIso.refl]

theorem pullDimension_trans {Q R T : TypedQuiver}
    (f : TypedQuiverIso Q R) (g : TypedQuiverIso R T) (d : T.V →₀ ℕ) :
    pullDimension (TypedQuiverIso.trans f g) d = pullDimension f (pullDimension g d) := by
  ext v
  simp [TypedQuiverIso.trans]

theorem pullRepresentation_refl (Q : TypedQuiver) (d : Q.V →₀ ℕ)
    (S : Representation Q.source Q.target (fun v => d v)) :
    pullRepresentation (TypedQuiverIso.refl Q) d S = S := by
  apply representation_ext
  funext a
  rfl

theorem pull_arrow_heq {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (d : R.V →₀ ℕ) (S : Representation R.source R.target (fun v => d v)) (a : Q.A) :
    (pullRepresentation f d S).arrow a ≍ S.arrow (f.arrowEquiv a) := by
  simp only [pullRepresentation]
  exact (cast_heq _ _).trans (cast_heq _ _)

theorem pullRepresentation_trans {Q R T : TypedQuiver}
    (f : TypedQuiverIso Q R) (g : TypedQuiverIso R T) (d : T.V →₀ ℕ)
    (S : Representation T.source T.target (fun v => d v)) :
    pullRepresentation (TypedQuiverIso.trans f g) d S =
      pullRepresentation f (pullDimension g d) (pullRepresentation g d S) := by
  apply representation_ext
  funext a
  apply eq_of_heq
  exact (pull_arrow_heq (TypedQuiverIso.trans f g) d S a).trans
    ((pull_arrow_heq f (pullDimension g d) (pullRepresentation g d S) a).trans
      (pull_arrow_heq g d S (f.arrowEquiv a))).symm

/-- Keep the dimension vector and its actual representation together; the
action need not preserve an individual dimension vector. -/
abbrev SupportedRepresentation (Q : TypedQuiver) :=
  (d : Q.V →₀ ℕ) × Representation Q.source Q.target (fun v => d v)

noncomputable def pullSupported {Q R : TypedQuiver} (f : TypedQuiverIso Q R)
    (S : SupportedRepresentation R) : SupportedRepresentation Q :=
  ⟨pullDimension f S.1, pullRepresentation f S.1 S.2⟩

theorem pullSupported_refl (Q : TypedQuiver) (S : SupportedRepresentation Q) :
    pullSupported (TypedQuiverIso.refl Q) S = S := by
  apply Sigma.ext (pullDimension_refl Q S.1)
  exact heq_of_eq (pullRepresentation_refl Q S.1 S.2)

/-- Contravariant composition is checked on actual dimensioned representations,
not merely on support labels or dimensions. -/
theorem pullSupported_trans {Q R T : TypedQuiver}
    (f : TypedQuiverIso Q R) (g : TypedQuiverIso R T)
    (S : SupportedRepresentation T) :
    pullSupported (TypedQuiverIso.trans f g) S = pullSupported f (pullSupported g S) := by
  apply Sigma.ext (pullDimension_trans f g S.1)
  exact heq_of_eq (pullRepresentation_trans f g S.1 S.2)

theorem quiverIso_ext {Q R : TypedQuiver} {f g : TypedQuiverIso Q R}
    (hv : f.vertexEquiv = g.vertexEquiv) (ha : f.arrowEquiv = g.arrowEquiv) : f = g := by
  cases f
  cases g
  cases hv
  cases ha
  rfl

theorem quiverIso_symm_trans {Q R : TypedQuiver} (f : TypedQuiverIso Q R) :
    TypedQuiverIso.trans f.symm f = TypedQuiverIso.refl R := by
  apply quiverIso_ext <;> ext x <;>
    simp [TypedQuiverIso.trans, TypedQuiverIso.refl, TypedQuiverIso.symm]

theorem quiverIso_trans_symm {Q R : TypedQuiver} (f : TypedQuiverIso Q R) :
    TypedQuiverIso.trans f f.symm = TypedQuiverIso.refl Q := by
  apply quiverIso_ext <;> ext x <;>
    simp [TypedQuiverIso.trans, TypedQuiverIso.refl, TypedQuiverIso.symm]

noncomputable def pullSupportedEquiv {Q R : TypedQuiver} (f : TypedQuiverIso Q R) :
    SupportedRepresentation R ≃ SupportedRepresentation Q where
  toFun := pullSupported f
  invFun := pullSupported f.symm
  left_inv S := by
    rw [← pullSupported_trans, quiverIso_symm_trans, pullSupported_refl]
  right_inv S := by
    rw [← pullSupported_trans, quiverIso_trans_symm, pullSupported_refl]

open KroneckerCoverDeckTranslations KroneckerDeckDimensionClasses

theorem deckQuiverAuto_refl : deckQuiverAuto Deck.refl = TypedQuiverIso.refl coloredCoverQuiver := by
  apply quiverIso_ext
  · rfl
  · apply Equiv.ext
    intro a
    rfl

theorem deckQuiverAuto_trans (g h : Deck) :
    deckQuiverAuto (Deck.trans g h) = TypedQuiverIso.trans (deckQuiverAuto g) (deckQuiverAuto h) := by
  apply quiverIso_ext
  · rfl
  · apply Equiv.ext
    intro a
    rfl

noncomputable def deckPull (g : Deck) : SupportedRepresentation coloredCoverQuiver →
    SupportedRepresentation coloredCoverQuiver := pullSupported (deckQuiverAuto g)

theorem deckPull_refl (S : SupportedRepresentation coloredCoverQuiver) :
    deckPull Deck.refl S = S := by
  unfold deckPull
  rw [deckQuiverAuto_refl]
  exact pullSupported_refl _ _

theorem deckPull_trans (g h : Deck) (S : SupportedRepresentation coloredCoverQuiver) :
    deckPull (Deck.trans g h) S = deckPull g (deckPull h S) := by
  unfold deckPull
  rw [deckQuiverAuto_trans]
  exact pullSupported_trans _ _ _

open KroneckerFiniteSupportStability KroneckerQuiverPullbackStability

local instance : DecidableEq coloredCoverQuiver.V :=
  inferInstanceAs (DecidableEq KroneckerReducedColorWords.Word)

theorem deckPull_stable_iff (g : Deck) (a b : ℤ)
    (S : SupportedRepresentation coloredCoverQuiver) :
    FiniteSupportStable (deckPull g S).1 (parityCharacter a b) (deckPull g S).2 ↔
      FiniteSupportStable S.1 (parityCharacter a b) S.2 := by
  exact deck_stable_iff g S.1 a b S.2

end KroneckerQuiverPullbackComposition
