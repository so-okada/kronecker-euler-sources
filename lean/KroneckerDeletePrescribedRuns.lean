import KroneckerDeletePrescribedCount
import KroneckerPrescribedMixedRuns

/-! Prescribed collars for deletion and for the restricted comparison in
Proposition 4.10 (`prop:composition`) of the manuscript. -/
set_option autoImplicit false
namespace KroneckerDeletePrescribedRuns
open KroneckerWordCounts KroneckerFiberBudget KroneckerColoredShell KroneckerPrescribedCollars
open KroneckerRawMixedPrograms KroneckerDeletePrescribedCount KroneckerOrientationPositions KroneckerPrescribedRunPrograms

theorem prescribed_delete_run_count {m u v P D : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (rs ts left right : List ℕ)
    (p : RawProgram m (runWord rs) (runWord ts) 0 0 D)
    (hl : ∀ r ∈ left,1 ≤ r ∧ r ≤ m-1) (hr : ∀ r ∈ right,1 ≤ r ∧ r ≤ m-1)
    (hll : left.length=P) (hrl : right.length=P) (hP : (m+1)*D ≤ P) :
    runCount m rs 0 ≤ fiberBudget m rs.length D*runCount m (left++(u::ts++[v])++right) 0 := by
  have hlen : left.length=right.length := by omega
  have h := prescribed_delete_count hm hu hv p (pairCollars left right)
    (pairCollars_legal m left right hl hr) (by rw [pairCollars_length left right hlen,hll]; exact hP)
  simpa only [shellPath_runWord,pairCollars_path left right _ hlen,runWord_horizontal_count,runCount] using h

theorem prescribed_delete_run_real {m u v P D : ℕ} (hm : 3 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-1) (hv : 1 ≤ v ∧ v ≤ m-1) (rs ts left right : List ℕ)
    (p : RawProgram m (runWord rs) (runWord ts) 0 0 D)
    (hl : ∀ r ∈ left,1 ≤ r ∧ r ≤ m-1) (hr : ∀ r ∈ right,1 ≤ r ∧ r ≤ m-1)
    (hll : left.length=P) (hrl : right.length=P) (hP : (m+1)*D ≤ P) :
    (runCount m rs 0 : ℝ)/(fiberBudget m rs.length D : ℝ) ≤
      (runCount m (left++(u::ts++[v])++right) 0 : ℝ) := by
  have hlen : left.length=right.length := by omega
  have h := prescribed_delete_real hm hu hv p (pairCollars left right)
    (pairCollars_legal m left right hl hr) (by rw [pairCollars_length left right hlen,hll]; exact hP)
  simpa only [shellPath_runWord,pairCollars_path left right _ hlen,runWord_horizontal_count,runCount] using h

/-- The manuscript's single comparison proposition. Deletion allows run
lengths through `m-1`; any insertion imposes the stated `m-2` restriction.
`RawProgram` fixes the edge edits independently of the grading. -/
theorem prescribed_run_count {m M u v P K A D : ℕ} (hm : 3 ≤ m)
    (hM : M ≤ m-1) (hinsert : 0 < K+A → 4 ≤ m ∧ M ≤ m-2)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (rs ts left right : List ℕ)
    (p : RawProgram m (runWord rs) (runWord ts) K A D)
    (hl : ∀ r ∈ left, 1 ≤ r ∧ r ≤ M)
    (hr : ∀ r ∈ right, 1 ≤ r ∧ r ≤ M)
    (hll : left.length=P) (hrl : right.length=P)
    (hP : K+A+(m+1)*D ≤ P) :
    runCount m rs 0 ≤ fiberBudget m rs.length D *
      runCount m (left++(u::ts++[v])++right) 0 := by
  by_cases hzero : K+A=0
  · have hK : K=0 := by omega
    have hA : A=0 := by omega
    subst K
    subst A
    exact prescribed_delete_run_count hm ⟨hu.1, hu.2.trans hM⟩
      ⟨hv.1, hv.2.trans hM⟩ rs ts left right p
      (fun r h => ⟨(hl r h).1, (hl r h).2.trans hM⟩)
      (fun r h => ⟨(hr r h).1, (hr r h).2.trans hM⟩)
      hll hrl (by simpa using hP)
  · obtain ⟨hm4, hM2⟩ := hinsert (by omega)
    exact KroneckerPrescribedMixedRuns.prescribed_mixed_run_count hm4
      ⟨hu.1, hu.2.trans hM2⟩ ⟨hv.1, hv.2.trans hM2⟩ rs ts left right p
      (fun r h => ⟨(hl r h).1, (hl r h).2.trans hM2⟩)
      (fun r h => ⟨(hr r h).1, (hr r h).2.trans hM2⟩) hll hrl hP

theorem prescribed_run_real {m M u v P K A D : ℕ} (hm : 3 ≤ m)
    (hM : M ≤ m-1) (hinsert : 0 < K+A → 4 ≤ m ∧ M ≤ m-2)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (rs ts left right : List ℕ)
    (p : RawProgram m (runWord rs) (runWord ts) K A D)
    (hl : ∀ r ∈ left, 1 ≤ r ∧ r ≤ M)
    (hr : ∀ r ∈ right, 1 ≤ r ∧ r ≤ M)
    (hll : left.length=P) (hrl : right.length=P)
    (hP : K+A+(m+1)*D ≤ P) :
    (runCount m rs 0 : ℝ) / (fiberBudget m rs.length D : ℝ) ≤
      (runCount m (left++(u::ts++[v])++right) 0 : ℝ) := by
  by_cases hzero : K+A=0
  · have hK : K=0 := by omega
    have hA : A=0 := by omega
    subst K
    subst A
    exact prescribed_delete_run_real hm ⟨hu.1, hu.2.trans hM⟩
      ⟨hv.1, hv.2.trans hM⟩ rs ts left right p
      (fun r h => ⟨(hl r h).1, (hl r h).2.trans hM⟩)
      (fun r h => ⟨(hr r h).1, (hr r h).2.trans hM⟩)
      hll hrl (by simpa using hP)
  · obtain ⟨hm4, hM2⟩ := hinsert (by omega)
    exact KroneckerPrescribedMixedRuns.prescribed_mixed_run_real hm4
      ⟨hu.1, hu.2.trans hM2⟩ ⟨hv.1, hv.2.trans hM2⟩ rs ts left right p
      (fun r h => ⟨(hl r h).1, (hl r h).2.trans hM2⟩)
      (fun r h => ⟨(hr r h).1, (hr r h).2.trans hM2⟩) hll hrl hP

end KroneckerDeletePrescribedRuns
