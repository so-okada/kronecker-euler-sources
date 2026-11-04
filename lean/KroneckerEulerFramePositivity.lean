import KroneckerParameterDimensionBounds
import KroneckerRationalEntropy

section

/- Original module: KroneckerCanonicalEulerLower -/
section
/-! Remove the phase-classification assumption from the rational Euler lower bound. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerCanonicalEulerLower
open KroneckerWordCounts KroneckerPeriodicTail KroneckerFrameBadDensity
open KroneckerRationalWordRotation KroneckerRationalPeriodAlphabet
open KroneckerEventualFramePhase KroneckerConditionalEulerLower


end KroneckerCanonicalEulerLower
end

/- Original module: KroneckerCanonicalLiteratureLower -/
section
/-! Rational lower limits relative to the named literature interface no longer assume phase classification. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerCanonicalLiteratureLower
open KroneckerPeriodicTail KroneckerFrameBadDensity KroneckerDyck KroneckerFrameIdentity
open KroneckerRationalWordRotation KroneckerRationalPeriodAlphabet
open KroneckerEventualFramePhase KroneckerConditionalEulerLower


end KroneckerCanonicalLiteratureLower
end

/- Original module: KroneckerFullLiteratureUpper -/
section
/-! Transfer the proved rational upper comparison through the named Literature identity. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFullLiteratureUpper
open KroneckerFullActualUpper KroneckerFrameIdentity KroneckerPeriodicTail
open KroneckerRationalWordRotation KroneckerParameterDimensionBounds KroneckerLiteratureCountNatural


end KroneckerFullLiteratureUpper
end

/- Original module: KroneckerInteriorLiteratureLower -/
section
/-! The interior rational lower bound follows from the named literature data and dimension limits. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerInteriorLiteratureLower
open KroneckerPeriodicTail KroneckerDyck KroneckerFrameIdentity KroneckerRationalWordRotation
open KroneckerCanonicalLiteratureLower KroneckerEventualFrameAlphabet


end KroneckerInteriorLiteratureLower
end

/- Original module: KroneckerFullLiteratureLimit -/
section
/-! The full rational all-sequence limit for m>=3 and rational slopes in (1,m-1), relative only to named Literature inputs. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFullLiteratureLimit
open KroneckerFrameIdentity KroneckerPeriodicTail KroneckerRationalWordRotation
open KroneckerFullLiteratureUpper KroneckerInteriorLiteratureLower


end KroneckerFullLiteratureLimit
end

/- Original module: KroneckerNonprimitiveLiteratureLimit -/
section
/-! The full-interior rational limit does not require a reduced fraction as input. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerNonprimitiveLiteratureLimit
open KroneckerFrameIdentity KroneckerPeriodicTail KroneckerRationalWordRotation
open KroneckerFullLiteratureLimit KroneckerRationalReduction KroneckerRationalRateInvariant


end KroneckerNonprimitiveLiteratureLimit
end

/- Original module: KroneckerParameterFrameJoint -/
section
/-! Uniform rational neighborhoods on the actual determinant-one frame parameter domain. -/
set_option autoImplicit false
namespace KroneckerParameterFrameJoint
open KroneckerLogic KroneckerParameterApproximable KroneckerRationalEntropy

noncomputable def value {m : ℕ} (x : ParameterDomain m) : ℝ :=
  KroneckerFrameObservables.value m ⟨x.val.a,x.val.b,x.val.d₁,by have := x.val.hd₁; omega⟩


end KroneckerParameterFrameJoint
end

/- Original module: KroneckerEulerObservables -/
section
/-! The Euler domain carries, rather than assumes away, the named source interface. -/
set_option autoImplicit false
namespace KroneckerEulerObservables
open KroneckerFrameIdentity KroneckerLiteratureCountNatural

structure EulerPoint (m : ℕ) where
  P : Parameters
  E : ℕ
  hmP : P.m=m
  source : Literature P (E : ℤ)

def height {m : ℕ} (x : EulerPoint m) : ℕ := x.P.a
noncomputable def slope {m : ℕ} (x : EulerPoint m) : ℝ := (x.P.b : ℝ)/x.P.a
noncomputable def value {m : ℕ} (x : EulerPoint m) : ℝ := Real.log (x.E : ℝ)/x.P.a

theorem point_dictionary (m : ℕ) (x : EulerPoint m) :
    KroneckerWordCounts.runCount m (KroneckerFrameBadDensity.frameWord x.P.a x.P.b x.P.d₁) 0 = m*x.E := by
  simpa only [x.hmP] using literal_frame_identity_nat x.P x.E x.source

end KroneckerEulerObservables
end
end

section

set_option autoImplicit false
open Filter
namespace KroneckerEulerFramePositivity
open KroneckerEulerObservables KroneckerFrameBadDensity

def toFrame {m : ℕ} (x : EulerPoint m) : KroneckerFrameObservables.FramePoint :=
  ⟨x.P.a,x.P.b,x.P.d₁,by have := x.P.hd₁; omega⟩

theorem euler_positive_of_alphabet (m : ℕ) (hm : 3 ≤ m) (x : EulerPoint m)
    (hlegal : ∀ r ∈ frameWord x.P.a x.P.b x.P.d₁, 1 ≤ r ∧ r ≤ m-1) : 0 < x.E := by
  have hne : frameWord x.P.a x.P.b x.P.d₁ ≠ [] := by
    intro he
    have h := congrArg List.length he
    simp only [KroneckerFrameWord.frameWord_length,List.length_nil] at h
    omega
  have hp := KroneckerWordBounds.runCount_pos m hm _ hne hlegal
  rw [point_dictionary m x] at hp
  by_contra h
  have hz : x.E = 0 := by omega
  simp [hz] at hp

theorem eventual_euler_positive (m : ℕ) (hm : 3 ≤ m) (x : ℕ → EulerPoint m)
    (hlegal : ∀ᶠ n in atTop, ∀ r ∈ frameWord (x n).P.a (x n).P.b (x n).P.d₁,
      1 ≤ r ∧ r ≤ m-1) : ∀ᶠ n in atTop, 0 < (x n).E :=
  hlegal.mono (fun n hn => euler_positive_of_alphabet m hm (x n) hn)

end KroneckerEulerFramePositivity
end

