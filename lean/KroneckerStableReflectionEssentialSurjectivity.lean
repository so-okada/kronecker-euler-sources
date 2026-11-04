import KroneckerStablePairSourceReflection
import KroneckerKernelCokernelReconstruction

/-! Every stable reflected representation is isomorphic to the reflection
of an explicitly reconstructed stable original representation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableReflectionEssentialSurjectivity
open KroneckerStablePairFamilyEquivalence KroneckerAbstractPairIso

def reconstructionIso (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) (S : StablePair m (m*a-b) a) :
    Iso S.val (KroneckerStablePairReflection.reflect m a b ha
      (KroneckerStablePairSourceReflection.inverse m a b ha hb S)).val :=
  trans (KroneckerKernelCokernelReconstruction.reconstruction S.val
    (KroneckerStablePairSourceReflection.outgoing_injective m (m*a-b) a ha S))
    (trans (KroneckerKernelReflectionIso.reflectedIso
      (KroneckerStablePairSourceReflection.inverseIso m a b ha hb S))
      (KroneckerCoordinateKernelReflectionIso.coordinateIso _
        (KroneckerStablePairReflection.incoming_surjective m a b ha _)))

theorem exists_preimage (m a b : ℕ) (ha : 0<a) (hb : b≤m*a) (S : StablePair m (m*a-b) a) :
    ∃ R : StablePair m a b,Nonempty (Iso (KroneckerStablePairReflection.reflect m a b ha R).val S.val) :=
  ⟨KroneckerStablePairSourceReflection.inverse m a b ha hb S,⟨symm (reconstructionIso m a b ha hb S)⟩⟩
end KroneckerStableReflectionEssentialSurjectivity
