import KroneckerRawRunSteps

/-! Delete exactly one vertical from every original length-two run. -/
set_option autoImplicit false
namespace KroneckerDeleteBinaryProgram
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRawConcatenation
open KroneckerRawRunSteps KroneckerContextDeletion KroneckerListDeletion

noncomputable def contextDelete {m : ℕ} {U V : List Bool} {K A D : ℕ}
    (p : RawProgram m U V K A D) (hK : K=0) (hA : A=0) (pre post : List Bool) :
    RawProgram m (pre++U++post) (pre++V++post) 0 0 D := by
  induction p with
  | nil => exact .nil
  | complete p r i hr hi ih => omega
  | insert p i hi ih => omega
  | @delete V K A D p i hi hv ih =>
    simpa only [removeAt_context pre V post i hi] using
      RawProgram.delete (ih hK hA) (pre.length+i) (by simp; omega)
        (by simpa only [getElem_context pre V post i hi] using hv)

noncomputable def binaryDelete (m : ℕ) (rs : List ℕ) (hr : ∀ r∈rs,r=1 ∨ r=2) :
    RawProgram m (runWord rs) (runWord (List.replicate rs.length 1)) 0 0 (rs.count 2) := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih =>
    have ht : ∀ t∈rs,t=1 ∨ t=2 := fun t ht => hr t (by simp [ht])
    have q := contextDelete (ih ht) rfl rfl (runWord [1]) []
    have q' : RawProgram m (runWord (1::rs))
        (runWord (List.replicate (rs.length+1) 1)) 0 0 (rs.count 2) := by
      simpa [runWord,List.replicate_succ] using q
    by_cases h : r=1
    · subst r
      simpa using q'
    · have h2 : r=2 := (hr r (by simp)).resolve_left h
      subst r
      have d := deleteRunVertical m [] rs 1
      have c := appendRaw d q'
      simpa [Nat.add_comm] using c

theorem binary_sum (rs : List ℕ) (hr : ∀ r∈rs,r=1 ∨ r=2) :
    rs.sum=rs.length+rs.count 2 := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have ht := ih (fun t ht => hr t (by simp [ht]))
    rcases hr r (by simp) with rfl | rfl <;> simp at * <;> omega

theorem binary_deletions (rs : List ℕ) (hr : ∀ r∈rs,r=1 ∨ r=2) :
    rs.count 2=rs.sum-rs.length := by
  have := binary_sum rs hr
  omega

end KroneckerDeleteBinaryProgram
