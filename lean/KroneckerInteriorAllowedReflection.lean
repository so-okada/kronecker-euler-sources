import KroneckerCanonicalClosedApproximableFromFundamental

/- Original module: KroneckerCanonicalDimensionBounds -/
section
/-! Both elementary root-region dimension inequalities are consequences of
actual canonical moduli nonemptiness, not arithmetic assumptions in a model. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalDimensionBounds
open KroneckerCanonicalKroneckerModuli KroneckerReflectionPairModel

theorem dimension_bounds (m a b : ℕ) (ha : 0<a) (hb : 0<b) (hn : Nonempty (space m a b)) :
    b≤m*a ∧ a≤m*b := by
  obtain ⟨R,hR⟩ := (space_nonempty_iff m a b).mp hn
  let P := fromRepresentation R
  have hs : PairStable P := (KroneckerReflectionPairStability.stable_iff P).mp hR
  exact ⟨KroneckerReflectionKernelDimension.sink_bound P ha hs,
    KroneckerReflectionKernelDimension.source_bound P hb hs⟩
end KroneckerCanonicalDimensionBounds
end
end

/- Original module: KroneckerInteriorAllowedReflection -/
section
/-! Global reflection and exchange act on the actual interior manuscript
domain, retaining positivity, primitivity and geometric nonemptiness. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorAllowedReflection
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))

def Interior (m : ℕ) := {p : Dimension (family H) m // slope p∈interior m}

def exchange (m : ℕ) (hm : 3≤m) (p : Interior H m) : Interior H m :=
  ⟨KroneckerExchangeAllowedDimensions.exchange H p.val,by
    rw [KroneckerExchangeObservables.slope_exchange]
    simpa [KroneckerSlopeSymmetry.exchange,KroneckerManuscriptTarget.interior] using
      KroneckerSlopeSymmetry.exchange_mem_interior
        (by exact_mod_cast (show 2<m by omega)) p.property⟩

def reflect (m : ℕ) (hm : 3≤m) (p : Interior H m) : Interior H m := by
  let a := p.val.val.1
  let b := p.val.val.2
  have hc := KroneckerReflectionInteriorDimensions.interior m hm a b p.val.property.1 p.property
  have hb : b≤m*a := (KroneckerCanonicalDimensionBounds.dimension_bounds m a b
    p.val.property.1 p.val.property.2.1 p.val.property.2.2.2).1
  exact ⟨⟨(m*a-b,a),hc.1,p.val.property.1,
    (KroneckerReflectionPrimitive.coprime_iff m a b hb).mpr p.val.property.2.2.1,
    KroneckerReflectionNonemptyTransfer.reflected_nonempty m a b p.val.property.1 p.val.property.2.2.2⟩,hc.2⟩


end KroneckerInteriorAllowedReflection
end
end
