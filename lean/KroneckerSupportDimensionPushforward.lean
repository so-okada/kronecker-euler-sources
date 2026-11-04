import KroneckerFiniteSupportStability

/-! Restriction to the finite positive support retains the exact pushed base
dimension vector and every induced character, for any ambient vertex set. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSupportDimensionPushforward
open KroneckerFiniteSupportInducedQuiver
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V W : Type} (d : V →₀ ℕ)

def vector : SupportVertex d →₀ ℕ := Finsupp.equivFunOnFinite.symm (supportDimension d)

theorem extend_vector : (vector d).mapDomain Subtype.val=d := by
  have hv : vector d=Finsupp.comapDomain Subtype.val d Subtype.val_injective.injOn := by ext v;rfl
  rw [hv]
  apply Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective
  intro v hv
  exact ⟨⟨v,hv⟩,rfl⟩

theorem vector_push (side : V → W) :
    (vector d).mapDomain (fun v => side v.val)=d.mapDomain side := by
  have H := congrArg (Finsupp.mapDomain side) (extend_vector d)
  simpa only [← Finsupp.mapDomain_comp, Function.comp_def] using H

end KroneckerSupportDimensionPushforward
