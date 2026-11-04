import KroneckerCurrentMechanicalNotation
import KroneckerRationalPeriodAlphabet
import KroneckerChainRecoveredSkeleton

/-! Explicit parameters in the manuscript restored to the PR30 structure.
The finite rational path W_(p,q) and the infinite sequence R_(p,q) are
different objects. Their simple-run index is one-based.
The final section records the map for an explicitly chosen family of
representatives and proves that changing the family does not change it.
-/
set_option autoImplicit false
noncomputable section

namespace KroneckerBetaRationalRuns
open KroneckerPaperPaths KroneckerWordCounts KroneckerMechanicalRuns
open KroneckerMechanicalWords KroneckerRationalWordRotation
open KroneckerCurrentMechanicalNotation

def length (p q i : ℕ) : ℤ := mechanicalRun ((p : ℝ) / q) 0 (i - 1)

def path (p q : ℕ) : TNEPath := runPath (rationalPeriod p q) 0

def sequence (p q i : ℕ) : TNEPath :=
  runPath [natRun ((p : ℝ) / q) 0 (i - 1)] 0

theorem length_formula (p q i : ℕ) (hi : 0 < i) :
    length p q i = ⌊(i : ℝ) * (p : ℝ) / q⌋ -
      ⌊((i - 1 : ℕ) : ℝ) * (p : ℝ) / q⌋ := by
  simp only [length, mechanicalRun, mechanicalPrefix,
    Nat.sub_add_cancel hi, zero_add, ← mul_div_assoc]

theorem path_mechanical_factor (p q : ℕ) :
    path p q = MechRunFactor ((p : ℝ) / q) 0 1 q := by
  rw [MechRunFactor_one]
  rfl

theorem sequence_length (p q i : ℕ) :
    sequence p q i = runPath [(length p q i).toNat] 0 := rfl

end KroneckerBetaRationalRuns

namespace KroneckerBetaRepresentativeChoices
open KroneckerChainLocalSlotClasses KroneckerChainRepresentativeIndependence
open KroneckerDimensionedChainGluing KroneckerDimensionedSupportClasses
open KroneckerChainIncidence KroneckerChainPortColors
open KroneckerChainSlotAssignments

def supportMap {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (ρ : FamilyClass d σ → RepresentativeFamily d σ)
    (X : FamilyClass d σ) : Quotient dimensionedSetoid :=
  Quotient.mk dimensionedSetoid (gluedRepresentative (ρ X))

theorem supportMap_eq {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (ρ : FamilyClass d σ → RepresentativeFamily d σ)
    (hρ : ∀ X, representedClass (ρ X) = X) :
    supportMap ρ = dimensionedGlueClasses := by
  funext X
  calc
    supportMap ρ X = dimensionedGlueClasses (representedClass (ρ X)) :=
      (dimensioned_glue_of_representative (ρ X)).symm
    _ = dimensionedGlueClasses X := congrArg dimensionedGlueClasses (hρ X)

theorem supportMap_independent {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (ρ ρ' : FamilyClass d σ → RepresentativeFamily d σ)
    (hρ : ∀ X, representedClass (ρ X) = X)
    (hρ' : ∀ X, representedClass (ρ' X) = X) :
    supportMap ρ = supportMap ρ' :=
  (supportMap_eq ρ hρ).trans (supportMap_eq ρ' hρ').symm

theorem supportImage_independent {n : ℕ} {d : Block n → ℕ} {σ : ColorChoices n}
    (ρ ρ' : FamilyClass d σ → RepresentativeFamily d σ)
    (hρ : ∀ X, representedClass (ρ X) = X)
    (hρ' : ∀ X, representedClass (ρ' X) = X) :
    Set.range (supportMap ρ) = Set.range (supportMap ρ') :=
  congrArg Set.range (supportMap_independent ρ ρ' hρ hρ')

end KroneckerBetaRepresentativeChoices

#print axioms KroneckerBetaRationalRuns.length
#print axioms KroneckerBetaRationalRuns.path
#print axioms KroneckerBetaRationalRuns.sequence
#print axioms KroneckerBetaRationalRuns.length_formula
#print axioms KroneckerBetaRationalRuns.path_mechanical_factor
#print axioms KroneckerBetaRationalRuns.sequence_length
#print axioms KroneckerBetaRepresentativeChoices.supportMap
#print axioms KroneckerBetaRepresentativeChoices.supportMap_eq
#print axioms KroneckerBetaRepresentativeChoices.supportMap_independent
#print axioms KroneckerBetaRepresentativeChoices.supportImage_independent
