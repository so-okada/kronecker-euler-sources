import KroneckerAbstractPairHom

/-! Coordinate-free representation isomorphisms, with explicit inverses and
composition on the actual source and sink vector spaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractPairIso
open KroneckerAbstractPairHom
variable {m : ℕ}
variable {V W V' W' V'' W'' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
  [AddCommGroup V''] [Module ℂ V''] [AddCommGroup W''] [Module ℂ W'']

structure Iso (R : Rep m V W) (S : Rep m V' W') where
  source : V ≃ₗ[ℂ] V'
  sink : W ≃ₗ[ℂ] W'
  commutes : ∀ i x,sink (R i x)=S i (source x)

def toHom {R : Rep m V W} {S : Rep m V' W'} (e : Iso R S) : Hom R S :=
  ⟨e.source.toLinearMap,e.sink.toLinearMap,e.commutes⟩

def refl (R : Rep m V W) : Iso R R := ⟨LinearEquiv.refl ℂ V,LinearEquiv.refl ℂ W,fun _ _ => rfl⟩

def symm {R : Rep m V W} {S : Rep m V' W'} (e : Iso R S) : Iso S R where
  source := e.source.symm
  sink := e.sink.symm
  commutes i x := by
    apply e.sink.injective
    simp only [LinearEquiv.apply_symm_apply,e.commutes]

def trans {R : Rep m V W} {S : Rep m V' W'} {T : Rep m V'' W''}
    (e : Iso R S) (f : Iso S T) : Iso R T where
  source := e.source.trans f.source
  sink := e.sink.trans f.sink
  commutes i x := by simp only [LinearEquiv.trans_apply,e.commutes,f.commutes]

theorem hom_symm_left {R : Rep m V W} {S : Rep m V' W'} (e : Iso R S) :
    comp (toHom (symm e)) (toHom e)=identity R := by
  apply hom_ext <;> ext x <;> simp [comp,toHom,symm,identity]

theorem hom_symm_right {R : Rep m V W} {S : Rep m V' W'} (e : Iso R S) :
    comp (toHom e) (toHom (symm e))=identity S := by
  apply hom_ext <;> ext x <;> simp [comp,toHom,symm,identity]
end KroneckerAbstractPairIso
