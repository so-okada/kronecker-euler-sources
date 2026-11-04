import KroneckerRunWordSplice

/- Original module: KroneckerRawConcatenation -/
section
/-! Concatenate raw edit programs, adding their exact K/A/D costs. -/
set_option autoImplicit false
namespace KroneckerRawConcatenation
open KroneckerRawMixedPrograms

def appendRaw {m : ℕ} {U V W : List Bool} {K A D L B E : ℕ}
    (p : RawProgram m U V K A D) (q : RawProgram m V W L B E) :
    RawProgram m U W (K+L) (A+B) (D+E) :=
  match q with
  | .nil => p
  | .complete q r i hr hi => by simpa only [Nat.add_assoc] using RawProgram.complete (appendRaw p q) r i hr hi
  | .insert q i hi => by simpa only [Nat.add_assoc] using RawProgram.insert (appendRaw p q) i hi
  | .delete q i hi hv => by simpa only [Nat.add_assoc] using RawProgram.delete (appendRaw p q) i hi hv


end KroneckerRawConcatenation
end

/- Original module: KroneckerRawRunSteps -/
section
/-! Primitive run-list edits are realized by fixed raw edge edits. -/
set_option autoImplicit false
namespace KroneckerRawRunSteps
open KroneckerStack KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRunWordSplice
open KroneckerVerticalInsertionRuns KroneckerRunDeletionPosition

def insertCompleteRun {m : ℕ} (pre post : List ℕ) (r : ℕ) (hr : 1 ≤ r ∧ r ≤ m-2) :
    RawProgram m (runWord (pre++post)) (runWord (pre++r::post)) 1 0 0 := by
  have hi : (runWord pre).length ≤ (runWord (pre++post)).length := by simp [runWord]
  simpa only [complete_runWord] using RawProgram.complete (m:=m) (U:=runWord (pre++post)) .nil r (runWord pre).length hr hi

def insertRunVertical (m : ℕ) (pre post : List ℕ) (r : ℕ) :
    RawProgram m (runWord (pre++r::post)) (runWord (pre++(r+1)::post)) 0 1 0 := by
  have hi : (runWord pre).length+1 ≤ (runWord (pre++r::post)).length := by simp [runWord,runShape]
  simpa only [insert_runWord] using RawProgram.insert (m:=m) (U:=runWord (pre++r::post)) .nil ((runWord pre).length+1) hi

noncomputable def deleteRunVertical (m : ℕ) (pre post : List ℕ) (r : ℕ) :
    RawProgram m (runWord (pre++(r+1)::post)) (runWord (pre++r::post)) 0 0 1 := by
  let hi := Classical.choose (runDeletion_data pre post r)
  have hd := Classical.choose_spec (runDeletion_data pre post r)
  simpa only [hd.2] using RawProgram.delete (m:=m) (U:=runWord (pre++(r+1)::post)) .nil (runDeletionIndex pre r) hi hd.1


end KroneckerRawRunSteps
end
