import KroneckerReflectionKernelDescent
import KroneckerKernelReflectionFaithful
import KroneckerKernelReflectionIso
import KroneckerPairIsoOfInverse

/- Original module: KroneckerKernelReflectionFullness -/
section
/-! Every morphism between reflected representations uniquely descends to
an original morphism when the original incoming map is surjective. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerKernelReflectionFullness
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality KroneckerAbstractKernelReflection
open KroneckerReflectionKernelDescent KroneckerSurjectiveLinearDescent
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

def lift {R : Rep m V W} {S : Rep m V' W'} (hR : Function.Surjective (incoming R))
    (g : Hom (reflection R) (reflection S)) : Hom R S where
  source := g.sink
  sink := descend (incoming R) hR ((incoming S).comp (diagonal g.sink)) (kernel_preserved g)
  commutes i x := by
    rw [←single R i x,evaluate]
    simp only [LinearMap.comp_apply,diagonal_single,single]

theorem lift_map {R : Rep m V W} {S : Rep m V' W'} (hR : Function.Surjective (incoming R))
    (f : Hom R S) : lift hR (map f)=f :=
  KroneckerKernelReflectionFaithful.source_determines hR rfl

theorem map_lift {R : Rep m V W} {S : Rep m V' W'} (hR : Function.Surjective (incoming R))
    (g : Hom (reflection R) (reflection S)) : map (lift hR g)=g := by
  apply hom_ext
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact coordinates g x
  · rfl

def homEquiv {R : Rep m V W} {S : Rep m V' W'} (hR : Function.Surjective (incoming R)) :
    Hom R S ≃ Hom (reflection R) (reflection S) := ⟨map,lift hR,lift_map hR,map_lift hR⟩
end KroneckerKernelReflectionFullness
end
end

/- Original module: KroneckerKernelReflectionReflectsIso -/
section
/-! Reflection is conservative on incoming-surjective representations:
an isomorphism of the reflected representations uniquely lifts to an original isomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerKernelReflectionReflectsIso
open KroneckerAbstractPairHom KroneckerAbstractPairIso
open KroneckerAbstractIncomingNaturality KroneckerAbstractKernelReflection
open KroneckerKernelReflectionFullness KroneckerKernelReflectionFunctorLaws
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

def liftIso {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Surjective (incoming R)) (hS : Function.Surjective (incoming S))
    (e : Iso (reflection R) (reflection S)) : Iso R S := by
  let f := lift hR (toHom e)
  let g := lift hS (toHom (symm e))
  have hl : comp g f=identity R := by
    apply KroneckerKernelReflectionFaithful.faithful hR
    rw [composition_map,identity_map]
    change comp (map (lift hS (toHom (symm e)))) (map (lift hR (toHom e)))=identity (reflection R)
    rw [map_lift,map_lift,hom_symm_left]
  have hr : comp f g=identity S := by
    apply KroneckerKernelReflectionFaithful.faithful hS
    rw [composition_map,identity_map]
    change comp (map (lift hR (toHom e))) (map (lift hS (toHom (symm e))))=identity (reflection S)
    rw [map_lift,map_lift,hom_symm_right]
  exact KroneckerPairIsoOfInverse.ofInverse f g hl hr

theorem isomorphic_iff {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Surjective (incoming R)) (hS : Function.Surjective (incoming S)) :
    Nonempty (Iso R S) ↔ Nonempty (Iso (reflection R) (reflection S)) :=
  ⟨fun ⟨e⟩ => ⟨KroneckerKernelReflectionIso.reflectedIso e⟩,fun ⟨e⟩ => ⟨liftIso hR hS e⟩⟩
end KroneckerKernelReflectionReflectsIso
end
end

/- Original module: KroneckerCoordinateKernelReflectionIso -/
section
/-! The canonical coordinate reflection is isomorphic to the coordinate-free
kernel reflection on the actual incoming kernel, with every arrow identified. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCoordinateKernelReflectionIso
open KroneckerReflectionPairModel
variable {m a b : ℕ} (R : PairRep m a b)
  (h : Function.Surjective (KroneckerReflectionIncomingMap.incoming R))

def coordinateIso : KroneckerAbstractPairIso.Iso
    (KroneckerAbstractKernelReflection.reflection R) (KroneckerReflectionKernelCoordinates.reflected R h) where
  source := KroneckerReflectionKernelCoordinates.coordinates R h
  sink := LinearEquiv.refl ℂ _
  commutes i x := (KroneckerReflectionKernelCoordinates.reflected_arrow R h i x).symm
end KroneckerCoordinateKernelReflectionIso
end
end
