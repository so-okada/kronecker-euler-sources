import KroneckerFullImageNumericalTransport

/-! The inclusion of a COMPLETE finite dimension support is a full quiver
embedding. Dimensioned restriction through it pushes back to the exact
original representation, and every positive vertex multiplicity is retained.
This connects ambient stable objects to finite trees without discarding arrows. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFiniteSupportFullInclusion
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFullImagePushforward KroneckerFullImageSupportedBridge
open KroneckerEmbeddedFiniteDimensions KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportInducedQuiver
attribute [local instance] Classical.decEq Classical.propDecidable

def inclusion (Q : TypedQuiver) (d : Q.V →₀ ℕ) : QuiverMap (supportQuiver Q d) Q :=
  ⟨Subtype.val,Subtype.val,fun _ => rfl,fun _ => rfl⟩

theorem inclusion_full (Q : TypedQuiver) (d : Q.V →₀ ℕ) : FullOnImage (inclusion Q d) := by
  intro a u v hs ht
  exact ⟨⟨a,hs.symm ▸ u.property,ht.symm ▸ v.property⟩,rfl⟩

theorem dimension_image (Q : TypedQuiver) (d : Q.V →₀ ℕ) : InImage (inclusion Q d).vertex d := by
  intro v hv
  exact ⟨⟨v,hv⟩,rfl⟩

def restricted (Q : TypedQuiver) (S : SupportedRepresentation Q) : SupportedRepresentation (supportQuiver Q S.1) :=
  supportedEquiv (inclusion Q S.1) Subtype.val_injective Subtype.val_injective (inclusion_full Q S.1)
    ⟨S,dimension_image Q S.1⟩



theorem push_restricted (Q : TypedQuiver) (S : SupportedRepresentation Q) :
    push (inclusion Q S.1) Subtype.val_injective Subtype.val_injective (inclusion_full Q S.1) (restricted Q S) = S :=
  push_descend _ _ _ _ _

end KroneckerFiniteSupportFullInclusion
