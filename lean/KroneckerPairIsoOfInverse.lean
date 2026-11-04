import KroneckerAbstractPairIso

/-! Mutually inverse actual representation morphisms give a representation
isomorphism, with the same source and sink linear maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairIsoOfInverse
open KroneckerAbstractPairHom KroneckerAbstractPairIso
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

def ofInverse {R : Rep m V W} {S : Rep m V' W'} (f : Hom R S) (g : Hom S R)
    (hl : comp g f=identity R) (hr : comp f g=identity S) : Iso R S where
  source := LinearEquiv.ofLinearMap f.source g.source
    (congrArg (fun k : Hom S S => k.source) hr) (congrArg (fun k : Hom R R => k.source) hl)
  sink := LinearEquiv.ofLinearMap f.sink g.sink
    (congrArg (fun k : Hom S S => k.sink) hr) (congrArg (fun k : Hom R R => k.sink) hl)
  commutes := f.commutes

end KroneckerPairIsoOfInverse
