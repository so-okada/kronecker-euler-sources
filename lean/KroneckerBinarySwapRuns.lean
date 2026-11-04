import KroneckerRawBinaryContext

/- Original module: KroneckerBinarySwapPrograms -/
section
/-! Counted programs of adjacent unequal exchanges on literal binary words. -/
set_option autoImplicit false
namespace KroneckerBinarySwapPrograms

def pairBits (right : Bool) : List Bool := if right then [false,true] else [true,false]

inductive Swaps (X : List Bool) : List Bool → ℕ → Type
  | nil : Swaps X X 0
  | step {pre post : List Bool} {k : ℕ} (right : Bool)
      (p : Swaps X (pre++pairBits right++post) k) :
      Swaps X (pre++pairBits (!right)++post) (k+1)


theorem swaps_count {X Y : List Bool} {k : ℕ} (p : Swaps X Y k) (b : Bool) : X.count b=Y.count b := by
  induction p with
  | nil => rfl
  | step right p ih =>
    cases right <;> cases b <;> simp [pairBits,List.count_append] at ih ⊢ <;> omega

end KroneckerBinarySwapPrograms
end

/- Original module: KroneckerBinarySwapContext -/
section
/-! Concatenate and contextualize counted binary swap programs without changing their cost. -/
set_option autoImplicit false
namespace KroneckerBinarySwapContext
open KroneckerBinarySwapPrograms

noncomputable def appendSwaps {X Y Z : List Bool} {k l : ℕ}
    (p : Swaps X Y k) (q : Swaps Y Z l) : Swaps X Z (k+l) := by
  induction q with
  | nil => simpa using p
  | step right q ih => simpa only [Nat.add_assoc] using Swaps.step right ih

noncomputable def contextSwaps {X Y : List Bool} {k : ℕ} (p : Swaps X Y k) (A B : List Bool) :
    Swaps (A++X++B) (A++Y++B) k := by
  induction p with
  | nil => exact .nil
  | @step pre post k right p ih =>
    have q : Swaps (A++X++B) ((A++pre)++pairBits right++(post++B)) k := by
      simpa only [List.append_assoc] using ih
    simpa only [List.append_assoc] using Swaps.step right q


end KroneckerBinarySwapContext
end

/- Original module: KroneckerBinarySwapRuns -/
section
/-! Every counted bit-swap program is an actual binary-run exchange list with the same cost. -/
set_option autoImplicit false
namespace KroneckerBinarySwapRuns
open KroneckerBinarySwapPrograms KroneckerRawBinaryEdits KroneckerBinaryExchangeShapes

def bitRuns (xs : List Bool) : List ℕ := xs.map (fun b => if b then 2 else 1)

theorem bitRuns_pair (right : Bool) : bitRuns (pairBits right)=pairRuns right := by
  cases right <;> rfl

noncomputable def swapsToRaw {X Y : List Bool} {k : ℕ} (p : Swaps X Y k) :
    RawBinary (bitRuns X) (bitRuns Y) 0 k := by
  induction p with
  | nil => exact .nil
  | @step pre post k right p ih =>
    have q : RawBinary (bitRuns X) (bitRuns pre++pairRuns right++bitRuns post) 0 k := by
      simpa only [bitRuns,List.map_append,← bitRuns_pair] using ih
    have h := RawBinary.exchange right q
    simpa only [bitRuns,List.map_append,← bitRuns_pair] using h


end KroneckerBinarySwapRuns
end
