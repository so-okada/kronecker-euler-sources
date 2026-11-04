import KroneckerAccumulatedDeckBaseDimensions

/-! Dimension classes for the full accumulated action, with well-defined
pushforward to the original quiver. The inverse and composition witnesses are
actual accumulated quiver maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDimensionClasses
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerAccumulatedCoverDeckActions
open KroneckerAccumulatedDeckBaseDimensions
attribute [local instance] Classical.decEq Classical.propDecidable

def Related (Q : TypedQuiver) (n : ℕ) (d e : (Q.iterate n).V →₀ ℕ) : Prop :=
  ∃ f : Deck Q n, pullDimension f.val d = e

def dimensionSetoid (Q : TypedQuiver) (n : ℕ) : Setoid ((Q.iterate n).V →₀ ℕ) where
  r := Related Q n
  iseqv := ⟨fun d => ⟨identity Q n,pullDimension_refl _ d⟩,by
    rintro d e ⟨f,rfl⟩
    refine ⟨inverse f,?_⟩
    change pullDimension f.val.symm (pullDimension f.val d) = d
    rw [← pullDimension_trans,quiverIso_symm_trans,pullDimension_refl],by
    rintro d e k ⟨f,rfl⟩ ⟨g,rfl⟩
    exact ⟨compose g f,pullDimension_trans g.val f.val d⟩⟩

abbrev DimensionClass (Q : TypedQuiver) (n : ℕ) := Quotient (dimensionSetoid Q n)

def classBaseDimension (Q : TypedQuiver) (n : ℕ) : DimensionClass Q n → Q.V →₀ ℕ :=
  Quotient.lift (baseDimension Q n) (by
    rintro d e ⟨f,rfl⟩
    exact (baseDimension_pull Q n f d).symm)

theorem same_class_iff (Q : TypedQuiver) (n : ℕ) (d e : (Q.iterate n).V →₀ ℕ) :
    Quotient.mk (dimensionSetoid Q n) d = Quotient.mk (dimensionSetoid Q n) e ↔
      ∃ f : Deck Q n, pullDimension f.val d = e := Quotient.eq


end KroneckerAccumulatedDimensionClasses
