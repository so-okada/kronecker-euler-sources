import KroneckerSourceCoordinateStability
import KroneckerStablePairReflection

/-! Actual stable families admit the inverse source-cokernel reflection,
including the dimension transport needed to invert a given sink reflection. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStablePairSourceReflection
open KroneckerStablePairFamilyEquivalence

def outgoing_injective (m a b : ℕ) (hb : 0<b) (R : StablePair m a b) :=
  KroneckerReflectionOutgoingMap.outgoing_injective R.val hb R.property

def reflect (m a b : ℕ) (hb : 0<b) (R : StablePair m a b) : StablePair m b (m*b-a) :=
  ⟨KroneckerSourceReflectionCoordinates.reflected R.val (outgoing_injective m a b hb R),
    KroneckerSourceCoordinateStability.stable R.val hb R.property (outgoing_injective m a b hb R)⟩

def inverse (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) (S : StablePair m (m*a-b) a) : StablePair m a b :=
  ⟨KroneckerPairDimensionTransport.transport rfl (Nat.sub_sub_self hb) (reflect m (m*a-b) a ha S).val,
    (KroneckerPairDimensionTransport.stable_iff rfl (Nat.sub_sub_self hb) _).mpr (reflect m (m*a-b) a ha S).property⟩

def inverseIso (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) (S : StablePair m (m*a-b) a) :
    KroneckerAbstractPairIso.Iso (KroneckerAbstractCokernelReflection.reflection S.val) (inverse m a b ha hb S).val :=
  KroneckerAbstractPairIso.trans
    (KroneckerSourceReflectionCoordinates.coordinateIso S.val (outgoing_injective m (m*a-b) a ha S))
    (KroneckerPairDimensionTransport.iso rfl (Nat.sub_sub_self hb) (reflect m (m*a-b) a ha S).val)
end KroneckerStablePairSourceReflection
