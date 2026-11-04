import KroneckerEmbeddedFiniteDimensions
import KroneckerQuiverImageWalkLifting

/-! A locally surjective embedding identifies the full quiver induced on any
finite ambient support lying in its image. Parallel arrows are retained, and
the arrow equivalence is proved from actual outgoing-arrow lifting. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedSupportQuiverIso
open KroneckerAbelianCover KroneckerTypedQuiverMaps
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerDirectSumEmbeddingLocalLifts
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

def supportArrowMap (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (d : Q.V →₀ ℕ) :
    SupportArrow P.source P.target (descend f.vertex hv d) → SupportArrow Q.source Q.target d :=
  fun a => ⟨f.arrow a.val,by
    constructor
    · rw [f.source]
      simpa only [Finsupp.mem_support_iff,descend_apply] using a.property.1
    · rw [f.target]
      simpa only [Finsupp.mem_support_iff,descend_apply] using a.property.2⟩

theorem supportArrowMap_bijective (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d) :
    Function.Bijective (supportArrowMap f hv d) := by
  constructor
  · intro a b h
    exact Subtype.ext (ha (congrArg Subtype.val h))
  · intro a
    obtain ⟨x,hx⟩ := hd a.property.1
    obtain ⟨b,hs,hb⟩ := hf.1 x a.val hx.symm
    refine ⟨⟨b,?_,?_⟩,Subtype.ext hb⟩
    · change P.source b ∈ (descend f.vertex hv d).support
      rw [Finsupp.mem_support_iff,descend_apply,hs,hx]
      exact Finsupp.mem_support_iff.mp a.property.1
    · rw [Finsupp.mem_support_iff,descend_apply,← f.target,hb]
      exact Finsupp.mem_support_iff.mp a.property.2

def supportIso (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d) :
    TypedQuiverIso (supportQuiver P (descend f.vertex hv d)) (supportQuiver Q d) where
  vertexEquiv := supportEquiv f.vertex hv d hd
  arrowEquiv := Equiv.ofBijective (supportArrowMap f hv d) (supportArrowMap_bijective f hv ha hf d hd)
  map_source a := Subtype.ext (f.source a.val)
  map_target a := Subtype.ext (f.target a.val)


end KroneckerEmbeddedSupportQuiverIso
