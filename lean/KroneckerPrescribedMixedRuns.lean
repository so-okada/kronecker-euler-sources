import KroneckerMixedLayerBudget

/- Original module: KroneckerPrescribedMixedCount -/
section
/-! Full raw mixed composition with arbitrary prescribed collar pairs and the original B_m(n,D). -/
set_option autoImplicit false
namespace KroneckerPrescribedMixedCount
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerCollarColoring
open KroneckerRawMixedPrograms KroneckerMiddleContext KroneckerRawProgramCount
open KroneckerPrescribedLayerSplit KroneckerMixedLayerBudget

theorem prescribed_mixed_count {m u v : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {K A D : ℕ}
    (p : RawProgram m U V K A D) (pairs : List (ℕ×ℕ))
    (hp : EditPairs m pairs) (hs : K+A+(m+1)*D ≤ pairs.length) :
    pathCount m U 0 ≤ fiberBudget m (U.count true) D*pathCount m (collarPath pairs (shellPath u v V)) 0 := by
  let k := pairs.length-(A+D)
  have h := mixed_layer_lengths pairs hs
  have hle := editPairs_sublist (List.drop_sublist k pairs) hp
  have hld := editPairs_legal (editPairs_sublist (List.take_sublist k pairs) hp)
  have hc := raw_program_count hm hu hv p (pairs.drop k) (pairs.take k) h.1 hle hld h.2
  simpa only [← collarPath_append,List.take_append_drop] using hc

theorem prescribed_mixed_real {m u v : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) {U V : List Bool} {K A D : ℕ}
    (p : RawProgram m U V K A D) (pairs : List (ℕ×ℕ))
    (hp : EditPairs m pairs) (hs : K+A+(m+1)*D ≤ pairs.length) :
    (pathCount m U 0 : ℝ)/(fiberBudget m (U.count true) D : ℝ) ≤
      (pathCount m (collarPath pairs (shellPath u v V)) 0 : ℝ) := by
  let k := pairs.length-(A+D)
  have h := mixed_layer_lengths pairs hs
  have hle := editPairs_sublist (List.drop_sublist k pairs) hp
  have hld := editPairs_legal (editPairs_sublist (List.take_sublist k pairs) hp)
  have hc := raw_program_real hm hu hv p (pairs.drop k) (pairs.take k) h.1 hle hld h.2
  simpa only [← collarPath_append,List.take_append_drop] using hc

end KroneckerPrescribedMixedCount
end

/- Original module: KroneckerPrescribedMixedRuns -/
section
/-! Full mixed comparison for literal left/right run collars in their prescribed order. -/
set_option autoImplicit false
namespace KroneckerPrescribedMixedRuns
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerPrescribedCollars
open KroneckerRawMixedPrograms KroneckerPrescribedMixedCount KroneckerOrientationPositions KroneckerPrescribedRunPrograms

theorem prescribed_mixed_run_count {m u v P K A D : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) (rs ts left right : List ℕ)
    (p : RawProgram m (runWord rs) (runWord ts) K A D)
    (hl : ∀ r ∈ left,1 ≤ r ∧ r ≤ m-2) (hr : ∀ r ∈ right,1 ≤ r ∧ r ≤ m-2)
    (hll : left.length=P) (hrl : right.length=P) (hP : K+A+(m+1)*D ≤ P) :
    runCount m rs 0 ≤ fiberBudget m rs.length D*runCount m (left++(u::ts++[v])++right) 0 := by
  have hlen : left.length=right.length := by omega
  have h := prescribed_mixed_count hm hu hv p (pairCollars left right)
    (pairCollars_edit_legal left right hl hr) (by rw [pairCollars_length left right hlen,hll]; exact hP)
  simpa only [shellPath_runWord,pairCollars_path left right _ hlen,runWord_horizontal_count,runCount] using h

theorem prescribed_mixed_run_real {m u v P K A D : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) (rs ts left right : List ℕ)
    (p : RawProgram m (runWord rs) (runWord ts) K A D)
    (hl : ∀ r ∈ left,1 ≤ r ∧ r ≤ m-2) (hr : ∀ r ∈ right,1 ≤ r ∧ r ≤ m-2)
    (hll : left.length=P) (hrl : right.length=P) (hP : K+A+(m+1)*D ≤ P) :
    (runCount m rs 0 : ℝ)/(fiberBudget m rs.length D : ℝ) ≤
      (runCount m (left++(u::ts++[v])++right) 0 : ℝ) := by
  have hlen : left.length=right.length := by omega
  have h := prescribed_mixed_real hm hu hv p (pairCollars left right)
    (pairCollars_edit_legal left right hl hr) (by rw [pairCollars_length left right hlen,hll]; exact hP)
  simpa only [shellPath_runWord,pairCollars_path left right _ hlen,runWord_horizontal_count,runCount] using h

end KroneckerPrescribedMixedRuns
end
