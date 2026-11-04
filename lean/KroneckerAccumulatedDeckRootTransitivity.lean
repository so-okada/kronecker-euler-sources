import KroneckerAccumulatedDeckBaseLabels

/-! Any two lifted vertices over the same original vertex are related by an
accumulated deck transformation, constructed recursively with the exact
character translation. This supplies canonical-root normalization. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDeckRootTransitivity
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerQuiverPullbackComposition
open KroneckerAccumulatedCoverDeckActions KroneckerAccumulatedDeckBaseLabels
open KroneckerAbelianCharacterReindex KroneckerAbelianAffineQuiverLift
attribute [local instance] Classical.decEq Classical.propDecidable

theorem exists_deck_to_root (Q : TypedQuiver) (n : ℕ) (u v : (Q.iterate n).V)
    (h : baseVertex Q n u = baseVertex Q n v) :
    ∃ f : Deck Q n, f.val.vertexEquiv u = v := by
  induction n with
  | zero =>
    refine ⟨identity Q 0,?_⟩
    exact h
  | succ n ih =>
    obtain ⟨g,hg⟩ := ih u.1 v.1 h
    let ξ := v.2 - reindex g.val.arrowEquiv u.2
    refine ⟨⟨affineLift g.val ξ,⟨g.val,ξ,g.property,rfl⟩⟩,?_⟩
    change (g.val.vertexEquiv u.1,reindex g.val.arrowEquiv u.2 + ξ) = v
    apply Prod.ext hg
    dsimp [ξ]
    abel


def zeroRoot (Q : TypedQuiver) : (n : ℕ) → Q.V → (Q.iterate n).V
  | 0,v => v
  | n+1,v => (zeroRoot Q n v,0)

theorem zeroRoot_base (Q : TypedQuiver) (n : ℕ) (v : Q.V) : baseVertex Q n (zeroRoot Q n v) = v := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem exists_normalizing_deck (Q : TypedQuiver) (n : ℕ) (u : (Q.iterate n).V) :
    ∃ f : Deck Q n, f.val.vertexEquiv u = zeroRoot Q n (baseVertex Q n u) :=
  exists_deck_to_root Q n u _ (zeroRoot_base Q n _).symm

end KroneckerAccumulatedDeckRootTransitivity
