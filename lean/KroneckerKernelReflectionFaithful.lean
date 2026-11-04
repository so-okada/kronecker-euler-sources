import KroneckerAbstractKernelReflection

/-! Reflection loses no morphism information when the original incoming map
is surjective: the sink map is uniquely determined by its commuting source map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerKernelReflectionFaithful
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality KroneckerAbstractKernelReflection
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

theorem source_determines {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Surjective (incoming R)) {f g : Hom R S} (hs : f.source=g.source) : f=g := by
  apply hom_ext hs
  ext y
  obtain ⟨x,rfl⟩ := hR y
  rw [naturality,naturality,hs]

theorem faithful {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Surjective (incoming R)) : Function.Injective (map (R:=R) (S:=S)) := by
  intro f g h
  apply source_determines hR
  exact congrArg (fun k : Hom (reflection R) (reflection S) => k.sink) h
end KroneckerKernelReflectionFaithful
