import KroneckerTypedQuiverMaps

/-! Finite dimension vectors on an embedded vertex set are exactly finite
ambient dimension vectors supported in its image. The equivalence preserves
the actual positive support and arbitrary pushforward of vertex dimensions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedFiniteDimensions
open KroneckerFiniteSupportInducedQuiver
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V W Z : Type}

def InImage (f : V → W) (d : W →₀ ℕ) : Prop := (d.support : Set W) ⊆ Set.range f

def descend (f : V → W) (hf : Function.Injective f) (d : W →₀ ℕ) : V →₀ ℕ :=
  Finsupp.comapDomain f d hf.injOn

theorem descend_apply (f : V → W) (hf : Function.Injective f) (d : W →₀ ℕ) (v : V) :
    descend f hf d v = d (f v) := rfl

def dimensionEquiv (f : V → W) (hf : Function.Injective f) :
    (V →₀ ℕ) ≃ {d : W →₀ ℕ // InImage f d} where
  toFun d := ⟨d.mapDomain f,by
    intro w hw
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
    exact ⟨v,rfl⟩⟩
  invFun d := descend f hf d.val
  left_inv d := Finsupp.comapDomain_mapDomain f hf d
  right_inv d := Subtype.ext (Finsupp.mapDomain_comapDomain f hf d.val d.property)

def supportEquiv (f : V → W) (hf : Function.Injective f) (d : W →₀ ℕ) (hd : InImage f d) :
    SupportVertex (descend f hf d) ≃ SupportVertex d :=
  Equiv.ofBijective (fun v => ⟨f v.val,by simpa only [Finsupp.mem_support_iff,descend_apply] using v.property⟩)
    ⟨by
      intro v w h
      exact Subtype.ext (hf (congrArg Subtype.val h)),by
      intro w
      obtain ⟨v,hv⟩ := hd w.property
      refine ⟨⟨v,?_⟩,Subtype.ext hv⟩
      simpa only [Finsupp.mem_support_iff,descend_apply,hv] using w.property⟩


end KroneckerEmbeddedFiniteDimensions
