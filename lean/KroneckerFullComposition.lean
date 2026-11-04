import KroneckerPrescribedMixedRuns

/-! Full prescribed-target composition for arbitrary complete-run and vertical edit lists.
The separately labeled wrapped-parse owner identity is not needed or asserted. -/
set_option autoImplicit false
namespace KroneckerFullComposition
open KroneckerWordCounts KroneckerFiberBudget KroneckerRawMixedPrograms KroneckerPrescribedMixedRuns

theorem composition_prescribed_target {m u v P K A D : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) (rs ts left right : List ℕ)
    (p : RawProgram m (runWord rs) (runWord ts) K A D)
    (ht : ∀ r ∈ ts,1 ≤ r ∧ r ≤ m-2)
    (hl : ∀ r ∈ left,1 ≤ r ∧ r ≤ m-2) (hr : ∀ r ∈ right,1 ≤ r ∧ r ≤ m-2)
    (hll : left.length=P) (hrl : right.length=P) (hP : K+A+(m+1)*D ≤ P) :
    (∀ r ∈ left++(u::ts++[v])++right,1 ≤ r ∧ r ≤ m-2) ∧
    (runCount m rs 0 : ℝ)/(fiberBudget m rs.length D : ℝ) ≤
      (runCount m (left++(u::ts++[v])++right) 0 : ℝ) := by
  constructor
  · intro r h
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with (hleft | ((rfl | hmiddle) | rfl)) | hright
    · exact hl r hleft
    · exact hu
    · exact ht r hmiddle
    · exact hv
    · exact hr r hright
  · exact prescribed_mixed_run_real hm hu hv rs ts left right p hl hr hll hrl hP

end KroneckerFullComposition
