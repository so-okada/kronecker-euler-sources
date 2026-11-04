import KroneckerDeletePrescribedRuns
import KroneckerDeleteBinaryProgram

/-! The three-arrow comparison has one binomial budget and an all-one target. -/
set_option autoImplicit false
namespace KroneckerDeleteBinaryCount
open KroneckerWordCounts KroneckerFiberBudget KroneckerDeletePrescribedRuns
open KroneckerDeleteBinaryProgram

theorem all_one_shells (n D : ℕ) :
    List.replicate (4*D) 1 ++ (1 :: List.replicate n 1 ++ [1]) ++
      List.replicate (4*D) 1 = List.replicate (n+2+8*D) 1 := by
  rw [← List.replicate_succ, ← List.replicate_one, ← List.replicate_add,
    ← List.replicate_add, ← List.replicate_add]
  congr 1
  omega

theorem fiberBudget_three (n D : ℕ) : fiberBudget 3 n D=(n+D).choose D*64^D := by
  unfold fiberBudget
  congr 1
  rw [show 2*3*D=6*D by omega,pow_mul]
  norm_num

theorem binary_count (rs : List ℕ) (hr : ∀ r∈rs,r=1 ∨ r=2) :
    runCount 3 rs 0 ≤ (rs.length+rs.count 2).choose (rs.count 2)*64^(rs.count 2) *
      runCount 3 (List.replicate (rs.length+2+8*rs.count 2) 1) 0 := by
  let D := rs.count 2
  have h := prescribed_run_count (m:=3) (M:=2) (u:=1) (v:=1) (P:=4*D)
    (by decide) (by decide) (by simp) (by decide) (by decide)
    rs (List.replicate rs.length 1)
    (List.replicate (4*D) 1) (List.replicate (4*D) 1) (binaryDelete 3 rs hr)
    (by simp) (by simp) (by simp) (by simp) (by omega)
  simpa only [all_one_shells,fiberBudget_three] using h

end KroneckerDeleteBinaryCount
