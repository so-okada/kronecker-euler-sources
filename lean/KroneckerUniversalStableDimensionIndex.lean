import KroneckerStableColoredRepresentatives

/-! The universal-word bounded stable dimension index uses the same actual
nonzero all-subrepresentation King-stability witnesses as the direct-sum
index. Its quotient of witnessed representatives is proved exactly equivalent
to this subset of the established universal dimension-deck quotient. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalStableDimensionIndex
open KroneckerReducedColorWords KroneckerStableColoredRepresentatives
open KroneckerDeckDimensionClasses KroneckerQuiverPullbackComposition
open KroneckerFiniteSupportStability KroneckerFiniteSupportDeckRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable

def StableIndex (B : ℕ) (θ : Fin 2 → ℤ) : Set DimensionClass :=
  {q | ∃ S : SupportedRepresentation coloredCoverQuiver,
    S.1 ≠ 0 ∧ S.1.sum (fun _ k => k) ≤ B ∧
    FiniteSupportStable S.1 (θ ∘ KroneckerUniversalWordBaseProjection.baseVertex) S.2 ∧
    Quotient.mk dimensionSetoid S.1 = q}

def representativeIndex (B : ℕ) (θ : Fin 2 → ℤ) (S : WordStable B θ) : StableIndex B θ :=
  ⟨Quotient.mk dimensionSetoid S.val.1,S.val,S.property.1,S.property.2.1,S.property.2.2,rfl⟩

def quotientIndex (B : ℕ) (θ : Fin 2 → ℤ) : Quotient (wordSetoid B θ) → StableIndex B θ :=
  Quotient.lift (representativeIndex B θ) (fun _ _ h => Subtype.ext (Quotient.sound h))

theorem quotientIndex_bijective (B : ℕ) (θ : Fin 2 → ℤ) : Function.Bijective (quotientIndex B θ) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | h S =>
      induction y using Quotient.inductionOn with | h T =>
        intro h
        have he : Quotient.mk dimensionSetoid S.val.1 = Quotient.mk dimensionSetoid T.val.1 := congrArg Subtype.val h
        have hr : dimensionSetoid S.val.1 T.val.1 := Quotient.exact he
        exact Quotient.sound hr
  · rintro ⟨q,S,hn,hB,hR,hq⟩
    exact ⟨Quotient.mk (wordSetoid B θ) ⟨S,hn,hB,hR⟩,Subtype.ext hq⟩

def indexEquiv (B : ℕ) (θ : Fin 2 → ℤ) : Quotient (wordSetoid B θ) ≃ StableIndex B θ :=
  Equiv.ofBijective (quotientIndex B θ) (quotientIndex_bijective B θ)

end KroneckerUniversalStableDimensionIndex
