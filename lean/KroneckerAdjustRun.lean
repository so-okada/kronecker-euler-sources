import KroneckerRawRunSteps

/- Original module: KroneckerRunEditPrograms -/
section
/-! A direct run-list interface for legal complete-run and vertical edits. -/
set_option autoImplicit false
namespace KroneckerRunEditPrograms
open KroneckerWordCounts KroneckerFiberBudget KroneckerRawMixedPrograms KroneckerRawConcatenation
open KroneckerRawRunSteps KroneckerFullComposition

inductive RunEdits (m : ℕ) (rs : List ℕ) : List ℕ → ℕ → ℕ → ℕ → Type
  | nil : RunEdits m rs rs 0 0 0
  | complete {pre post : List ℕ} {K A D : ℕ} (p : RunEdits m rs (pre++post) K A D)
      (r : ℕ) (hr : 1 ≤ r ∧ r ≤ m-2) : RunEdits m rs (pre++r::post) (K+1) A D
  | rise {pre post : List ℕ} {r K A D : ℕ} (p : RunEdits m rs (pre++r::post) K A D)
      (hr : 1 ≤ r ∧ r+1 ≤ m-2) : RunEdits m rs (pre++(r+1)::post) K (A+1) D
  | fall {pre post : List ℕ} {r K A D : ℕ} (p : RunEdits m rs (pre++(r+1)::post) K A D)
      (hr : 1 ≤ r ∧ r+1 ≤ m-2) : RunEdits m rs (pre++r::post) K A (D+1)

noncomputable def toRaw {m : ℕ} {rs ts : List ℕ} {K A D : ℕ} (p : RunEdits m rs ts K A D) :
    RawProgram m (runWord rs) (runWord ts) K A D := by
  induction p with
  | nil => exact .nil
  | @complete pre post K A D p r hr ih =>
    exact appendRaw ih (insertCompleteRun pre post r hr)
  | @rise pre post r K A D p hr ih =>
    exact appendRaw ih (insertRunVertical m pre post r)
  | @fall pre post r K A D p hr ih =>
    exact appendRaw ih (deleteRunVertical m pre post r)


end KroneckerRunEditPrograms
end

/- Original module: KroneckerIncreaseRun -/
section
/-! Increase a chosen run by an arbitrary prescribed number of vertical insertions. -/
set_option autoImplicit false
namespace KroneckerIncreaseRun
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRawConcatenation KroneckerRawRunSteps

def increaseRun (m : ℕ) (pre post : List ℕ) (r : ℕ) : (t : ℕ) →
    RawProgram m (runWord (pre++r::post)) (runWord (pre++(r+t)::post)) 0 t 0
  | 0 => .nil
  | t+1 => by
    simpa only [Nat.zero_add,Nat.add_zero,Nat.add_assoc] using
      appendRaw (increaseRun m pre post r t) (insertRunVertical m pre post (r+t))

theorem increase_run_exists (m : ℕ) (pre post : List ℕ) (r t : ℕ) :
    Nonempty (RawProgram m (runWord (pre++r::post)) (runWord (pre++(r+t)::post)) 0 t 0) :=
  ⟨increaseRun m pre post r t⟩

end KroneckerIncreaseRun
end

/- Original module: KroneckerDecreaseRun -/
section
/-! Decrease a chosen run by an arbitrary prescribed number of vertical deletions. -/
set_option autoImplicit false
namespace KroneckerDecreaseRun
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRawConcatenation KroneckerRawRunSteps

noncomputable def decreaseRun (m : ℕ) (pre post : List ℕ) (r : ℕ) : (t : ℕ) →
    RawProgram m (runWord (pre++(r+t)::post)) (runWord (pre++r::post)) 0 0 t
  | 0 => .nil
  | t+1 => by
    simpa only [Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm 1 t] using
      appendRaw (deleteRunVertical m pre post (r+t)) (decreaseRun m pre post r t)

theorem decrease_run_exists (m : ℕ) (pre post : List ℕ) (r t : ℕ) :
    Nonempty (RawProgram m (runWord (pre++(r+t)::post)) (runWord (pre++r::post)) 0 0 t) :=
  ⟨decreaseRun m pre post r t⟩

end KroneckerDecreaseRun
end

/- Original module: KroneckerAdjustRun -/
section
/-! An explicit edit program changes one run with the two exact directed costs. -/
set_option autoImplicit false
namespace KroneckerAdjustRun
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerIncreaseRun KroneckerDecreaseRun

theorem adjust_run_exists (m : ℕ) (pre post : List ℕ) (r s : ℕ) :
    Nonempty (RawProgram m (runWord (pre++r::post)) (runWord (pre++s::post)) 0 (s-r) (r-s)) := by
  by_cases h : r ≤ s
  · have he : r+(s-r)=s := by omega
    have hz : r-s=0 := by omega
    simpa only [he,hz] using increase_run_exists m pre post r (s-r)
  · have he : s+(r-s)=r := by omega
    have hz : s-r=0 := by omega
    simpa only [he,hz] using decrease_run_exists m pre post s (r-s)

end KroneckerAdjustRun
end
