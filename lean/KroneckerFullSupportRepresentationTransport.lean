import KroneckerFiniteSupportFullInclusion

/-! A full embedding of an actual representation's COMPLETE support transports
that very representation to the target quiver. Every support arrow matrix and
positive vertex dimension is retained; total dimension, original pushforward
multiplicities, nonvanishing and all-subrepresentation stability are preserved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFullSupportRepresentationTransport
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerFullImageQuiverEmbedding
open KroneckerFullImagePushforward KroneckerFullImageNumericalTransport
open KroneckerFiniteSupportFullInclusion KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportStability
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q W : TypedQuiver} (S : SupportedRepresentation Q)
  (f : QuiverMap (supportQuiver Q S.1) W) (hv : Function.Injective f.vertex)
  (ha : Function.Injective f.arrow) (hf : FullOnImage f)

def transport : SupportedRepresentation W := push f hv ha hf (restricted Q S)

theorem transport_dimension (v : SupportVertex S.1) :
    (transport S f hv ha hf).1 (f.vertex v) = S.1 v.val := by
  rw [transport,push_dimension,Finsupp.mapDomain_apply_of_injective hv]
  rfl

theorem transport_arrow (a : (supportQuiver Q S.1).A) :
    (transport S f hv ha hf).2.arrow (f.arrow a) ≍ S.2.arrow a.val := by
  have h := push_arrow_heq f hv ha hf (restricted Q S) a
  exact h.trans (KroneckerFullImageRepresentationEquivalence.representation_arrow_heq
    (inclusion Q S.1) Subtype.val_injective Subtype.val_injective (inclusion_full Q S.1)
    S.1 (dimension_image Q S.1) S.2 a)

theorem transport_zero_iff : (transport S f hv ha hf).1 = 0 ↔ S.1 = 0 := by
  rw [transport,push_zero_iff]
  have h := push_zero_iff (inclusion Q S.1) Subtype.val_injective Subtype.val_injective
    (inclusion_full Q S.1) (restricted Q S)
  rw [push_restricted] at h
  exact h.symm

theorem transport_sum : (transport S f hv ha hf).1.sum (fun _ k => k) = S.1.sum (fun _ k => k) := by
  rw [transport,push_sum]
  have h := push_sum (inclusion Q S.1) Subtype.val_injective Subtype.val_injective
    (inclusion_full Q S.1) (restricted Q S)
  rw [push_restricted] at h
  exact h.symm

theorem transport_original_dimension {Z : Type} (g : Q.V → Z) (h : W.V → Z)
    (he : ∀ v, h (f.vertex v) = g v.val) :
    (transport S f hv ha hf).1.mapDomain h = S.1.mapDomain g := by
  rw [transport,push_original_dimension]
  have hh : h ∘ f.vertex = g ∘ (inclusion Q S.1).vertex := funext he
  rw [hh]
  have hk := push_original_dimension (inclusion Q S.1) Subtype.val_injective Subtype.val_injective
    (inclusion_full Q S.1) (restricted Q S) g
  rw [push_restricted] at hk
  exact hk.symm

theorem transport_stable_iff (θ : Q.V → ℤ) (η : W.V → ℤ)
    (hθ : ∀ v, η (f.vertex v) = θ v.val) :
    FiniteSupportStable (transport S f hv ha hf).1 η (transport S f hv ha hf).2 ↔ FiniteSupportStable S.1 θ S.2 := by
  unfold transport
  rw [push_stable_iff]
  have hh : η ∘ f.vertex = θ ∘ (inclusion Q S.1).vertex := funext hθ
  rw [hh]
  have h := push_stable_iff (inclusion Q S.1) Subtype.val_injective Subtype.val_injective
    (inclusion_full Q S.1) (restricted Q S) θ
  rw [push_restricted] at h
  exact h.symm

end KroneckerFullSupportRepresentationTransport
