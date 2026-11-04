import KroneckerAdjustRun
import KroneckerWordEditCost

/- Original module: KroneckerNormalizationCosts -/
section
/-! Directed vertical edit costs add to the absolute word edit cost. -/
set_option autoImplicit false
namespace KroneckerNormalizationCosts
open KroneckerWordEditCost

def raiseCost (X : List ℕ) (k : ℕ) : ℕ := (X.map (fun r => k-r)).sum
def lowerCost (X : List ℕ) (k : ℕ) : ℕ := (X.map (fun r => r-k)).sum

theorem directed_cost_identity (r k : ℕ) :
    (k-r)+(r-k)=((r : ℤ)-(k : ℤ)).natAbs := by
  omega

theorem normalization_cost_identity (X : List ℕ) (k : ℕ) :
    raiseCost X k+lowerCost X k=wordEditCost X k := by
  induction X with
  | nil => simp [raiseCost,lowerCost,wordEditCost]
  | cons r X ih =>
    change ((k-r)+raiseCost X k)+((r-k)+lowerCost X k)=
      ((r : ℤ)-(k : ℤ)).natAbs+wordEditCost X k
    have h := directed_cost_identity r k
    omega

theorem normalization_cost_budget (m : ℕ) (X : List ℕ) (k : ℕ) :
    raiseCost X k+(m+1)*lowerCost X k ≤ (m+1)*wordEditCost X k ∧
    lowerCost X k+(m+1)*raiseCost X k ≤ (m+1)*wordEditCost X k := by
  rw [← normalization_cost_identity]
  constructor <;> nlinarith [Nat.zero_le (m*raiseCost X k),Nat.zero_le (m*lowerCost X k)]

end KroneckerNormalizationCosts
end

/- Original module: KroneckerNormalizationPrograms -/
section
/-! Actual raw programs normalize every run to a constant, in both directions. -/
set_option autoImplicit false
namespace KroneckerNormalizationPrograms
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRawConcatenation
open KroneckerAdjustRun KroneckerNormalizationCosts

theorem normalization_programs (m : ℕ) (X : List ℕ) (k : ℕ) (pre : List ℕ) :
    Nonempty (RawProgram m (runWord (pre++X)) (runWord (pre++List.replicate X.length k))
      0 (raiseCost X k) (lowerCost X k)) ∧
    Nonempty (RawProgram m (runWord (pre++List.replicate X.length k)) (runWord (pre++X))
      0 (lowerCost X k) (raiseCost X k)) := by
  induction X generalizing pre with
  | nil =>
    constructor <;> exact ⟨RawProgram.nil⟩
  | cons r X ih =>
    obtain ⟨⟨pf⟩,⟨pb⟩⟩ := ih (pre++[k])
    simp only [List.append_assoc,List.singleton_append] at pf pb
    obtain ⟨pa⟩ := adjust_run_exists m pre X r k
    obtain ⟨pd⟩ := adjust_run_exists m pre X k r
    constructor
    · exact ⟨by simpa [raiseCost,lowerCost,List.replicate_succ] using appendRaw pa pf⟩
    · exact ⟨by simpa [raiseCost,lowerCost,List.replicate_succ,Nat.add_comm] using appendRaw pb pd⟩

end KroneckerNormalizationPrograms
end
