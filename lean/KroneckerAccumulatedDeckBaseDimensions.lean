import KroneckerAccumulatedDeckBaseLabels

/-! Pushforward of a finite dimension vector to the original vertices sums all
lifted multiplicities. It is invariant under every accumulated deck map, not
only the translations in the final abelian layer. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDeckBaseDimensions
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerAccumulatedCoverDeckActions
open KroneckerAccumulatedDeckBaseLabels
attribute [local instance] Classical.decEq Classical.propDecidable

def baseDimension (Q : TypedQuiver) (n : ℕ) (d : (Q.iterate n).V →₀ ℕ) : Q.V →₀ ℕ :=
  d.mapDomain (baseVertex Q n)

theorem pullDimension_eq_mapDomain {Q R : TypedQuiver} (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) :
    pullDimension f d = d.mapDomain f.vertexEquiv.symm := by
  ext v
  rw [pullDimension_apply,Finsupp.mapDomain_equiv_apply]
  rfl

theorem baseDimension_pull (Q : TypedQuiver) (n : ℕ) (f : Deck Q n) (d : (Q.iterate n).V →₀ ℕ) :
    baseDimension Q n (pullDimension f.val d) = baseDimension Q n d := by
  unfold baseDimension
  rw [pullDimension_eq_mapDomain,← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro x _
  exact vertex_base_invariant Q n f.val.symm (inverse f).property x



end KroneckerAccumulatedDeckBaseDimensions
