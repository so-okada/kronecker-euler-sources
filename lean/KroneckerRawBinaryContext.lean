import KroneckerThreeFullComposition

section

/-! Compose actual raw binary edit lists with additive insertion and exchange budgets. -/
set_option autoImplicit false
namespace KroneckerRawBinaryConcatenation
open KroneckerRawBinaryEdits

noncomputable def appendRawBinary {R S T : List ℕ} {K₁ K₂ k₁ k₂ : ℕ}
    (p : RawBinary R S K₁ k₁) (q : RawBinary S T K₂ k₂) : RawBinary R T (K₁+K₂) (k₁+k₂) := by
  induction q with
  | nil => simpa using p
  | insert q r hr ih => simpa only [Nat.add_assoc] using RawBinary.insert ih r hr
  | exchange right q ih => simpa only [Nat.add_assoc] using RawBinary.exchange right ih


end KroneckerRawBinaryConcatenation
end

section

/-! A raw binary edit program remains valid inside arbitrary fixed run contexts. -/
set_option autoImplicit false
namespace KroneckerRawBinaryContext
open KroneckerRawBinaryEdits KroneckerRawBinaryConcatenation

noncomputable def contextRawBinary {R S : List ℕ} {K k : ℕ}
    (p : RawBinary R S K k) (A B : List ℕ) : RawBinary (A++R++B) (A++S++B) K k := by
  induction p with
  | nil => exact .nil
  | @insert pre post K k p r hr ih =>
    have q : RawBinary (A++R++B) ((A++pre)++(post++B)) K k := by
      simpa only [List.append_assoc] using ih
    simpa only [List.append_assoc,List.cons_append] using RawBinary.insert q r hr
  | @exchange pre post K k right p ih =>
    have q : RawBinary (A++R++B) ((A++pre)++KroneckerBinaryExchangeShapes.pairRuns right++(post++B)) K k := by
      simpa only [List.append_assoc] using ih
    simpa only [List.append_assoc] using RawBinary.exchange right q

noncomputable def concatenateRawBinary {R S T U : List ℕ} {K k J j : ℕ}
    (p : RawBinary R S K k) (q : RawBinary T U J j) :
    RawBinary (R++T) (S++U) (K+J) (k+j) := by
  have a : RawBinary (R++T) (S++T) K k := by simpa using contextRawBinary p [] T
  have b : RawBinary (S++T) (S++U) J j := by simpa using contextRawBinary q S []
  exact appendRawBinary a b


end KroneckerRawBinaryContext
end

