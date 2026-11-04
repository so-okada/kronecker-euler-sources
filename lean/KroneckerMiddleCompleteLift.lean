import KroneckerRawMixedPrograms

/- Original module: KroneckerSpliceContext -/
section
/-! Translate complete-block insertion through fixed left and right contexts. -/
set_option autoImplicit false
namespace KroneckerSpliceContext
open KroneckerListSplice

theorem splice_context {α : Type*} (pre xs post block : List α) (i : ℕ) (hi : i ≤ xs.length) :
    splice (pre.length+i) block (pre++xs++post)=pre++splice i block xs++post := by
  induction pre with
  | nil =>
    simp only [List.length_nil,Nat.zero_add,List.nil_append,splice]
    rw [List.take_append_of_le_length hi,List.drop_append_of_le_length hi]
    simp only [List.append_assoc]
  | cons a pre ih =>
    simpa only [List.length_cons,Nat.add_right_comm,List.cons_append,splice,
      List.take_succ_cons,List.drop_succ_cons] using congrArg (List.cons a) ih

end KroneckerSpliceContext
end

/- Original module: KroneckerBufferedGaps -/
section
/-! The right buffer keeps every middle endpoint strictly before the final edge. -/
set_option autoImplicit false
namespace KroneckerBufferedGaps
open KroneckerStack KroneckerColoredShell KroneckerCollarColoring KroneckerMiddleContext

theorem rightContext_positive (pairs : List (ℕ×ℕ)) (v : ℕ) : 1 ≤ (rightContext pairs v).length := by
  simp [rightContext,runShape]

theorem middle_complete_bounds (pairs : List (ℕ×ℕ)) (u v : ℕ) (U : List Bool) (i : ℕ)
    (hi : i ≤ U.length) :
    1 ≤ (leftContext pairs u).length+i ∧
      (leftContext pairs u).length+i < (collarPath pairs (shellPath u v U)).length := by
  rw [collar_middle_context]
  have hl := leftContext_positive pairs u
  have hr := rightContext_positive pairs v
  simp only [List.length_append]
  omega

end KroneckerBufferedGaps
end

/- Original module: KroneckerMiddleCompleteLift -/
section
/-! Lift a raw complete-run insertion without consuming a new collar pair. -/
set_option autoImplicit false
namespace KroneckerMiddleCompleteLift
open KroneckerColoredShell KroneckerCollarColoring KroneckerMixedPrograms KroneckerCompleteRunPalette
open KroneckerMiddleContext KroneckerSpliceContext KroneckerBufferedGaps

theorem complete_middle_path (pairs : List (ℕ×ℕ)) (u v r i : ℕ) (V : List Bool) (hi : i ≤ V.length) :
    completePath r ((leftContext pairs u).length+i) (collarPath pairs (shellPath u v V))=
      collarPath pairs (shellPath u v (completePath r i V)) := by
  unfold completePath
  rw [collar_middle_context,splice_context _ _ _ _ _ hi,collar_middle_context]

def completeLift {m u v : ℕ} {U V : List Bool} {K A D : ℕ} (pairs : List (ℕ×ℕ))
    (p : MixedProgram m (shellPath u v U) (collarPath pairs (shellPath u v V)) K A D)
    (r i : ℕ) (hr : 1 ≤ r ∧ r ≤ m-2) (hi : i ≤ V.length) :
    MixedProgram m (shellPath u v U) (collarPath pairs (shellPath u v (completePath r i V))) (K+1) A D := by
  simpa only [complete_middle_path pairs u v r i V hi] using
    MixedProgram.complete p r ((leftContext pairs u).length+i) hr (middle_complete_bounds pairs u v V i hi)

end KroneckerMiddleCompleteLift
end
