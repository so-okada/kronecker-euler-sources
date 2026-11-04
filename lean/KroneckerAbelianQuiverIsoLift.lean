import KroneckerAbelianCharacterReindex

/-! Every actual typed-quiver isomorphism lifts to the actual abelian cover.
The construction transports arrow-indexed characters and preserves both ends. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbelianQuiverIsoLift
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackComposition KroneckerAbelianCharacterReindex
variable {Q R T : TypedQuiver}
attribute [local instance] Classical.decEq Classical.propDecidable

def lift (f : TypedQuiverIso Q R) : TypedQuiverIso Q.abelian R.abelian where
  vertexEquiv := Equiv.prodCongr f.vertexEquiv (reindex f.arrowEquiv).toEquiv
  arrowEquiv := Equiv.prodCongr f.arrowEquiv (reindex f.arrowEquiv).toEquiv
  map_source a := by
    apply Prod.ext
    · exact f.map_source a.1
    · rfl
  map_target a := by
    apply Prod.ext
    · exact f.map_target a.1
    · change reindex f.arrowEquiv a.2 + unit (f.arrowEquiv a.1) =
        reindex f.arrowEquiv (a.2 + unit a.1)
      rw [map_add,reindex_unit]

theorem lift_vertex (f : TypedQuiverIso Q R) (v : Q.V) (χ : Character Q.A) :
    (lift f).vertexEquiv (v,χ) = (f.vertexEquiv v,reindex f.arrowEquiv χ) := rfl


theorem lift_refl (Q : TypedQuiver) : lift (TypedQuiverIso.refl Q) = TypedQuiverIso.refl Q.abelian := by
  apply quiverIso_ext <;> ext x <;> rfl

theorem lift_trans (f : TypedQuiverIso Q R) (g : TypedQuiverIso R T) :
    lift (TypedQuiverIso.trans f g) = TypedQuiverIso.trans (lift f) (lift g) := by
  apply quiverIso_ext <;> ext x <;> rfl

theorem lift_symm (f : TypedQuiverIso Q R) : lift f.symm = (lift f).symm := by
  apply quiverIso_ext <;> ext x <;> rfl

end KroneckerAbelianQuiverIsoLift
