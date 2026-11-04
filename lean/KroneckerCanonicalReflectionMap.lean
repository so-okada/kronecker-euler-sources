import KroneckerStablePairReflection

/-! A well-defined global sink-reflection map on the actual canonical stable
matrix orbit quotient, built from stable representatives and their exact gauge relation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionMap
open KroneckerCanonicalKroneckerModuli KroneckerStablePairFamilyEquivalence

def map (m a b : ℕ) (ha : 0<a) : space m a b → space m (m*a-b) a :=
  Quotient.lift (fun M : StableMatrix m a b =>
    KroneckerStablePairProjection.project m (m*a-b) a
      (KroneckerStablePairReflection.reflect m a b ha (fromMatrix m a b M))) (by
    intro M N hMN
    apply (KroneckerStablePairProjection.eq_iff _ _ _ _ _).mpr
    apply (KroneckerStablePairReflection.isomorphic_iff m a b ha _ _).mp
    apply (KroneckerStablePairProjection.eq_iff _ _ _ _ _).mp
    rw [KroneckerStablePairProjection.fromMatrix_project,KroneckerStablePairProjection.fromMatrix_project]
    exact Quotient.sound hMN)

theorem on_representatives (m a b : ℕ) (ha : 0<a) (R : StablePair m a b) :
    map m a b ha (KroneckerStablePairProjection.project m a b R)=
      KroneckerStablePairProjection.project m (m*a-b) a (KroneckerStablePairReflection.reflect m a b ha R) := by
  change KroneckerStablePairProjection.project m (m*a-b) a
    (KroneckerStablePairReflection.reflect m a b ha (fromMatrix m a b (toMatrix m a b R)))=_
  rw [show fromMatrix m a b (toMatrix m a b R)=R from (equiv m a b).symm_apply_apply R]
end KroneckerCanonicalReflectionMap
