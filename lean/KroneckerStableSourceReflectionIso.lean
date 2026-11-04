import KroneckerKernelCokernelReconstruction
import KroneckerStablePairSourceReflection

/- Original module: KroneckerCokernelReflectionFaithful -/
section
/-! Source-cokernel reflection is faithful when the target outgoing map is
injective: commutation and the sink map determine the original source map. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCokernelReflectionFaithful
open KroneckerAbstractPairHom KroneckerAbstractIncomingNaturality KroneckerAbstractOutgoingNaturality
open KroneckerAbstractCokernelReflection
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

theorem sink_determines {R : Rep m V W} {S : Rep m V' W'}
    (hS : Function.Injective (outgoing S)) {f g : Hom R S} (hs : f.sink=g.sink) : f=g := by
  apply hom_ext _ hs
  ext x
  apply hS
  rw [←KroneckerAbstractOutgoingNaturality.naturality f,←KroneckerAbstractOutgoingNaturality.naturality g,hs]

theorem faithful {R : Rep m V W} {S : Rep m V' W'}
    (hS : Function.Injective (outgoing S)) : Function.Injective (map (R:=R) (S:=S)) := by
  intro f g h
  apply sink_determines hS
  exact congrArg (fun k : Hom (reflection R) (reflection S) => k.source) h
end KroneckerCokernelReflectionFaithful
end
end

/- Original module: KroneckerCokernelReflectionFullness -/
section
/-! Source-cokernel reflection is fully faithful on outgoing-injective
representations, with an explicit lift through the reconstructed kernels. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCokernelReflectionFullness
open KroneckerAbstractPairHom KroneckerAbstractPairIso
open KroneckerAbstractIncomingNaturality KroneckerAbstractOutgoingNaturality
open KroneckerAbstractCokernelReflection KroneckerKernelCokernelReconstruction
variable {m : ℕ} {V W V' W' : Type}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

def lift {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Injective (outgoing R)) (hS : Function.Injective (outgoing S))
    (g : Hom (reflection R) (reflection S)) : Hom R S :=
  comp (toHom (symm (reconstruction S hS)))
    (comp (KroneckerAbstractKernelReflection.map g) (toHom (reconstruction R hR)))

theorem lift_map {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Injective (outgoing R)) (hS : Function.Injective (outgoing S)) (f : Hom R S) :
    lift hR hS (map f)=f := KroneckerCokernelReflectionFaithful.sink_determines hS rfl

theorem map_lift {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Injective (outgoing R)) (hS : Function.Injective (outgoing S))
    (g : Hom (reflection R) (reflection S)) : map (lift hR hS g)=g :=
  KroneckerKernelReflectionFaithful.source_determines
    (KroneckerReflectionExactImage.cokernel_incoming_surjective R) rfl

def homEquiv {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Injective (outgoing R)) (hS : Function.Injective (outgoing S)) :
    Hom R S ≃ Hom (reflection R) (reflection S) := ⟨map,lift hR hS,lift_map hR hS,map_lift hR hS⟩

def liftIso {R : Rep m V W} {S : Rep m V' W'}
    (hR : Function.Injective (outgoing R)) (hS : Function.Injective (outgoing S))
    (e : Iso (reflection R) (reflection S)) : Iso R S :=
  trans (reconstruction R hR) (trans (KroneckerKernelReflectionIso.reflectedIso e) (symm (reconstruction S hS)))
end KroneckerCokernelReflectionFullness
end
end

/- Original module: KroneckerSourceCoordinateIsomorphism -/
section
/-! The coordinated source reflection preserves and reflects actual pair
isomorphisms on outgoing-injective representations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceCoordinateIsomorphism
open KroneckerReflectionPairModel KroneckerAbstractPairIso KroneckerSourceReflectionCoordinates
variable {m a b : ℕ} (R S : PairRep m a b)
  (hR : Function.Injective (KroneckerAbstractOutgoingNaturality.outgoing R))
  (hS : Function.Injective (KroneckerAbstractOutgoingNaturality.outgoing S))
def forward (e : Iso R S) : Iso (reflected R hR) (reflected S hS) :=
  trans (trans (symm (coordinateIso R hR)) (KroneckerCokernelReflectionIso.reflectedIso e))
    (coordinateIso S hS)
def backward (e : Iso (reflected R hR) (reflected S hS)) : Iso R S :=
  KroneckerCokernelReflectionFullness.liftIso hR hS
    (trans (trans (coordinateIso R hR) e) (symm (coordinateIso S hS)))
theorem isomorphic_iff : Nonempty (Iso R S) ↔ Nonempty (Iso (reflected R hR) (reflected S hS)) :=
  ⟨fun ⟨e⟩ => ⟨forward R S hR hS e⟩,fun ⟨e⟩ => ⟨backward R S hR hS e⟩⟩
end KroneckerSourceCoordinateIsomorphism
end
end

/- Original module: KroneckerStableSourceReflectionIso -/
section
/-! Stable source reflection has precisely the original pair-isomorphism
fibers, so it descends to canonical stable moduli points. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableSourceReflectionIso
open KroneckerStablePairFamilyEquivalence KroneckerStablePairSourceReflection
theorem isomorphic_iff (m a b : ℕ) (hb : 0<b) (R S : StablePair m a b) :
    Nonempty (KroneckerAbstractPairIso.Iso R.val S.val) ↔
      Nonempty (KroneckerAbstractPairIso.Iso (reflect m a b hb R).val (reflect m a b hb S).val) :=
  KroneckerSourceCoordinateIsomorphism.isomorphic_iff R.val S.val
    (outgoing_injective m a b hb R) (outgoing_injective m a b hb S)
end KroneckerStableSourceReflectionIso
end
end
