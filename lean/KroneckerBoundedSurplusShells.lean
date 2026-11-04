import KroneckerRecolCollars
import KroneckerResidualColoringFinite

/-! Prescribed unary shells send all inputs of bounded surplus injectively to surplus zero. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerBoundedSurplusShells
open KroneckerColoring KroneckerWordCounts KroneckerProgramExecution
open KroneckerCollarColoring KroneckerCollarConnected KroneckerCollarRecovery
open KroneckerSurplusColoringFinite

abbrev BoundedColorings (m n : ℕ) (U : List Bool) :=
  {a : SurplusColorings m U // a.1 ≤ n}

def zeroShells {m : ℕ} (hm : 3 ≤ m) (pairs : List (ℕ × ℕ))
    (hp : LegalPairs m pairs) (U : List Bool)
    (a : BoundedColorings m pairs.length U) :
    ConnectedColorings m (collarPath pairs U) 0 := by
  refine ⟨collarColoring hm pairs hp a.val.1 U a.val.2.val, ?_⟩
  have h := collarColoring_connected hm pairs hp a.val.1 U a.val.2.val a.val.2.property
  simpa only [Nat.sub_eq_zero_of_le a.property] using h

theorem zeroShells_recover {m : ℕ} (hm : 3 ≤ m) (pairs : List (ℕ × ℕ))
    (hp : LegalPairs m pairs) (U : List Bool)
    (a : BoundedColorings m pairs.length U) :
    recoverCollar pairs U (zeroShells hm pairs hp U a).val = a.val.2.val :=
  recover_collarColoring hm pairs hp a.val.1 U a.val.2.val

theorem zeroShells_injective {m : ℕ} (hm : 3 ≤ m) (pairs : List (ℕ × ℕ))
    (hp : LegalPairs m pairs) (U : List Bool) :
    Function.Injective (zeroShells hm pairs hp U) := by
  intro a b he
  apply Subtype.ext
  apply surplusForget_injective m U
  calc
    surplusForget a.val = recoverCollar pairs U (zeroShells hm pairs hp U a).val :=
      (zeroShells_recover hm pairs hp U a).symm
    _ = recoverCollar pairs U (zeroShells hm pairs hp U b).val :=
      congrArg (fun z : ConnectedColorings m (collarPath pairs U) 0 =>
        recoverCollar pairs U z.val) he
    _ = surplusForget b.val := zeroShells_recover hm pairs hp U b

theorem zeroShells_execution {m : ℕ} (hm : 3 ≤ m) (pairs : List (ℕ × ℕ))
    (hp : LegalPairs m pairs) (U : List Bool)
    (a : BoundedColorings m pairs.length U) :
    KroneckerRecolCollars.Execution hm U
      (KroneckerManuscriptRecolorMaps.fromPalette (KroneckerPaperPaths.ofSteps U 0) a.val.2.val)
      a.val.1 pairs
      (KroneckerManuscriptRecolorMaps.fromPalette
        (KroneckerPaperPaths.ofSteps (collarPath pairs U) 0) (zeroShells hm pairs hp U a).val) :=
  KroneckerRecolCollars.collar_execution hm pairs hp a.val.1 U a.val.2.val

end KroneckerBoundedSurplusShells
