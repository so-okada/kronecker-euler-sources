import KroneckerSourceHorizontalShadow

/-! Uncolored bounded source gradings, independent of binomial color choices.
This closes the finite predicate/weight dictionary needed by Theorem 4.10.
No scattering coefficient or geometric Euler identification is assumed here. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerSourceGradingDictionary
open KroneckerStack KroneckerCompatibility KroneckerColoring KroneckerWeights
open KroneckerSourceIntervalCounts KroneckerSourceCompatibility
open scoped BigOperators

def rawTrace {m N : ℕ} (shape : ℕ → Bool) (d : Grades m N) (i : ℕ) : Edge :=
  if h : N=0 then .H 0 else
  if shape (i%N) then .H (d ⟨i%N,Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩).val
  else .V (d ⟨i%N,Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩).val

def SourceTight {m N : ℕ} (shape : ℕ → Bool) (a b : ℤ) (d : Grades m N) : Prop :=
  Cyclic (rawTrace shape d) N ∧ hWeight (rawTrace shape d) 0 N=b ∧
    vWeight (rawTrace shape d) 0 N=a ∧ KroneckerSourceHorizontalShadow.Support (rawTrace shape d) N

theorem raw_before {m N : ℕ} (shape : ℕ → Bool) (d : Grades m N) (i : ℕ) (hi : i<N) :
    rawTrace shape d i=if shape i then .H (d ⟨i,hi⟩).val else .V (d ⟨i,hi⟩).val := by
  simp [rawTrace,Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hi),Nat.mod_eq_of_lt hi]

theorem raw_eq_representative {m N : ℕ} (shape : ℕ → Bool) (d : Grades m N) :
    rawTrace shape d=trace shape (representative d) := by
  funext i
  simp only [rawTrace,trace,paint,representative,grade]

theorem trace_eq_raw_grades {m N : ℕ} (shape : ℕ → Bool) (g : Coloring m N) :
    trace shape g=rawTrace shape (grades g) := by
  funext i
  simp only [rawTrace,trace,paint,grades,grade]

theorem raw_grade_bound {m N : ℕ} (shape : ℕ → Bool) (d : Grades m N) (i : ℕ) :
    (rawTrace shape d i).grade≤m := by
  unfold rawTrace
  split_ifs with h hshape
  · simp [Edge.grade]
  · exact Nat.le_of_lt_succ (d _).isLt
  · exact Nat.le_of_lt_succ (d _).isLt

theorem hWeight_total {m N : ℕ} (shape : ℕ → Bool) (g : Coloring m N) :
    hWeight (trace shape g) 0 N=HTotal shape g := by
  rw [hWeight,Nat.Ico_zero_eq_range,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_before shape g i i.isLt]

theorem vWeight_total {m N : ℕ} (shape : ℕ → Bool) (g : Coloring m N) :
    vWeight (trace shape g) 0 N=VTotal shape g := by
  rw [vWeight,Nat.Ico_zero_eq_range,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_before shape g i i.isLt]

theorem hCount_edges {m N : ℕ} (shape : ℕ → Bool) (g : Coloring m N) :
    hCount (trace shape g) 0 N=HEdges shape N := by
  rw [KroneckerSourceIntervalCounts.hCount,Nat.Ico_zero_eq_range,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_before shape g i i.isLt]
  cases shape i.val <;> simp [paint,hFlag]

theorem vCount_edges {m N : ℕ} (shape : ℕ → Bool) (g : Coloring m N) :
    vCount (trace shape g) 0 N=VEdges shape N := by
  rw [KroneckerSourceIntervalCounts.vCount,Nat.Ico_zero_eq_range,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_before shape g i i.isLt]
  cases shape i.val <;> simp [paint,vFlag]

theorem source_tight_iff_representative {m N : ℕ} (shape : ℕ → Bool) (a b : ℤ) (d : Grades m N) :
    SourceTight shape a b d ↔ KroneckerTight.Tight shape a b (representative d) := by
  unfold SourceTight KroneckerTight.Tight
  rw [raw_eq_representative,cyclic_iff (trace_periodic shape (representative d)),
    hWeight_total,vWeight_total,KroneckerSourceHorizontalShadow.support_iff_internal]

theorem colored_tight_iff {m N : ℕ} (shape : ℕ → Bool) (a b : ℤ) (g : Coloring m N) :
    KroneckerTight.Tight shape a b g ↔ SourceTight shape a b (grades g) := by
  unfold SourceTight KroneckerTight.Tight
  rw [← trace_eq_raw_grades,cyclic_iff (trace_periodic shape g),hWeight_total,vWeight_total,
    KroneckerSourceHorizontalShadow.support_iff_internal]

theorem weighted_tight_eq {m N : ℕ} (shape : ℕ → Bool) (a b : ℤ) :
    weightedCount (SourceTight (m:=m) (N:=N) shape a b)=
      weightedCount (fun d : Grades m N => KroneckerTight.Tight shape a b (representative d)) := by
  congr 1
  funext d
  exact propext (source_tight_iff_representative shape a b d)




end KroneckerSourceGradingDictionary
