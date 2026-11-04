import KroneckerColoredAmbientPullSupport
import KroneckerUniversalSupportEuler
import KroneckerUniversalWeightedSupportCriterion

/- Original module: KroneckerColoredSupportStatistics -/
section
/-! Weighted colored full-support isomorphisms preserve totals, every
compatible original-vertex pushforward, and the actual self-Euler form. The
finite sums run over the entire positive support and all actual support
arrows; multiplicities over one original vertex are summed explicitly. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerColoredSupportStatistics
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerWeightedColoredSupportIso
open KroneckerFiniteSupportInducedQuiver KroneckerFiniteSupportEulerTransport
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver} {C : Coloring P} {D : Coloring Q}
  {d : P.V →₀ ℕ} {e : Q.V →₀ ℕ}

local instance supportFintype {V : Type} (d : V →₀ ℕ) : Fintype (SupportVertex d) :=
  Fintype.ofFinset d.support (by intro v; rfl)

local instance supportQuiverFintype (Q : TypedQuiver) (d : Q.V →₀ ℕ) : Fintype (supportQuiver Q d).V :=
  supportFintype d

theorem sum_support {V M : Type} [AddCommMonoid M] (d : V →₀ ℕ) (F : V → ℕ → M) :
    (∑ v : SupportVertex d, F v.val (d v.val)) = d.sum F :=
  Finset.sum_coe_sort d.support (fun v => F v (d v))

theorem total_eq (j : ColoredIso C D d e) : d.sum (fun _ k => k) = e.sum (fun _ k => k) := by
  rw [← sum_support,← sum_support]
  have h := j.iso.vertexEquiv.sum_comp (fun w => e w.val)
  simpa only [j.weight] using h

theorem mapDomain_eq (j : ColoredIso C D d e) {Z : Type} (f : P.V → Z) (g : Q.V → Z)
    (hlabel : ∀ v, g (j.iso.vertexEquiv v).val = f v.val) : d.mapDomain f = e.mapDomain g := by
  change d.sum (fun v k => Finsupp.single (f v) k) = e.sum (fun w k => Finsupp.single (g w) k)
  rw [← sum_support,← sum_support]
  have h := j.iso.vertexEquiv.sum_comp (fun w => Finsupp.single (g w.val) (e w.val))
  simpa only [j.weight,hlabel] using h

theorem zero_iff (j : ColoredIso C D d e) : d = 0 ↔ e = 0 := by
  constructor
  · intro hd
    by_contra he
    obtain ⟨v,hv⟩ := Finsupp.support_nonempty_iff.mpr he
    have h := (j.iso.vertexEquiv.symm ⟨v,hv⟩).property
    simpa only [hd,Finsupp.support_zero,Finset.notMem_empty] using h
  · intro he
    by_contra hd
    obtain ⟨v,hv⟩ := Finsupp.support_nonempty_iff.mpr hd
    have h := (j.iso.vertexEquiv ⟨v,hv⟩).property
    simpa only [he,Finsupp.support_zero,Finset.notMem_empty] using h

theorem selfEuler_eq (j : ColoredIso C D d e)
    [Finite (SupportArrow P.source P.target d)] [Finite (SupportArrow Q.source Q.target e)] :
    supportEuler P d = supportEuler Q e := supportEuler_iso d e j.iso j.weight

end KroneckerColoredSupportStatistics
end
end

/- Original module: KroneckerUniversalDimensionClassStatistics -/
section
/-! Original two-vertex dimensions, total dimension and self-Euler descend
to ALL universal word dimension-deck classes, including the zero class.
The invariance proof uses exact weighted full-support isomorphisms of related
dimensions, so each later index restriction has a well-defined invariant. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalDimensionClassStatistics
open KroneckerReducedColorWords KroneckerDeckDimensionClasses KroneckerUniversalWordBaseProjection
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerFiniteSupportEulerTransport
open KroneckerWeightedColoredSupportIso KroneckerColoredSupportStatistics
attribute [local instance] Classical.decEq Classical.propDecidable

def relationIso {d e : Word →₀ ℕ} (h : dimensionSetoid d e) : ColoredIso coloring coloring d e := by
  let f := Classical.choice (KroneckerUniversalWeightedSupportCriterion.dimension_relation_weightedIso h)
  exact ⟨f.iso,f.weight,f.parity_label,f.color_label⟩

theorem related_base {d e : Word →₀ ℕ} (h : dimensionSetoid d e) : d.mapDomain baseVertex = e.mapDomain baseVertex :=
  mapDomain_eq (relationIso h) baseVertex baseVertex (fun v => Fin.ext ((relationIso h).side v))

theorem related_total {d e : Word →₀ ℕ} (h : dimensionSetoid d e) : d.sum (fun _ k => k) = e.sum (fun _ k => k) :=
  total_eq (relationIso h)

theorem related_euler {d e : Word →₀ ℕ} (h : dimensionSetoid d e) :
    supportEuler coloredCoverQuiver d = supportEuler coloredCoverQuiver e := selfEuler_eq (relationIso h)

def classBase : DimensionClass → (Fin 2 →₀ ℕ) :=
  Quotient.lift (fun d => d.mapDomain baseVertex) (fun _ _ h => related_base h)

def classTotal : DimensionClass → ℕ := Quotient.lift (fun d => d.sum (fun _ k => k)) (fun _ _ h => related_total h)

def classEuler : DimensionClass → ℤ := Quotient.lift (fun d => supportEuler coloredCoverQuiver d) (fun _ _ h => related_euler h)

end KroneckerUniversalDimensionClassStatistics
end
end
