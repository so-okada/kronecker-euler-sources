import KroneckerReflectionCoordinateStability

/-! Actual morphisms of two-vertex representations on arbitrary complex
vector spaces. This supports functorial reflection without arbitrary coordinate choices. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAbstractPairHom
variable {m : ℕ}
variable {V W V' W' V'' W'' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
  [AddCommGroup V''] [Module ℂ V''] [AddCommGroup W''] [Module ℂ W'']

abbrev Rep (m : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :=
  Fin m → V →ₗ[ℂ] W

structure Hom (R : Rep m V W) (S : Rep m V' W') where
  source : V →ₗ[ℂ] V'
  sink : W →ₗ[ℂ] W'
  commutes : ∀ i x,sink (R i x)=S i (source x)

@[ext] theorem hom_ext {R : Rep m V W} {S : Rep m V' W'} {f g : Hom R S}
    (hs : f.source=g.source) (ht : f.sink=g.sink) : f=g := by
  cases f
  cases g
  cases hs
  cases ht
  rfl

def identity (R : Rep m V W) : Hom R R := ⟨LinearMap.id,LinearMap.id,fun _ _ => rfl⟩

def comp {R : Rep m V W} {S : Rep m V' W'} {T : Rep m V'' W''}
    (g : Hom S T) (f : Hom R S) : Hom R T where
  source := g.source.comp f.source
  sink := g.sink.comp f.sink
  commutes i x := by simp only [LinearMap.comp_apply,f.commutes,g.commutes]

theorem comp_identity {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) : comp f (identity R)=f := by
  apply hom_ext <;> rfl

end KroneckerAbstractPairHom
