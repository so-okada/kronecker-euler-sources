import KroneckerGoodPartitionUpper
import KroneckerBadWindowBounds

/- Original module: KroneckerIntervalBadStarts -/
section
/-! Count bad full windows in an interval and remove its first run exactly. -/
set_option autoImplicit false
namespace KroneckerIntervalBadStarts
open KroneckerMechanicalWindows KroneckerBadWindowCount KroneckerBadWindowBounds
open KroneckerWindowDiscrepancy

noncomputable def intervalBad (s u : ℝ) (p : ℤ) (q start n : ℕ) : ℕ :=
  ((Finset.range (n+1-q)).filter (fun i => windowSum s u q (start+i) ≠ p)).card

theorem interval_bad_zero (s u : ℝ) (p : ℤ) (q start : ℕ) (hq : 1 ≤ q) :
    intervalBad s u p q start 0=0 := by
  simp [intervalBad,show 0+1-q=0 by omega]

theorem interval_bad_successor (s u : ℝ) (p : ℤ) (q start n : ℕ) :
    intervalBad s u p q start (n+1)=intervalBad s u p q (start+1) n+
      if q ≤ n+1 ∧ windowSum s u q start ≠ p then 1 else 0 := by
  classical
  by_cases hlen : q ≤ n+1
  · have hsize : n+1+1-q=(n+1-q)+1 := by omega
    simp only [intervalBad,hsize,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero,hlen,true_and]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show start+(i+1)=start+1+i by omega]
  · have h0 : n+1-q=0 := by omega
    have h1 : n+1+1-q=0 := by omega
    simp [intervalBad,h0,h1,hlen]

theorem interval_bad_origin (s u : ℝ) (p : ℤ) (q n : ℕ) :
    intervalBad s u p q 0 n=badWindows s u p q (n+1-q) := by
  simp only [intervalBad,badWindows,nonzeroCount,discrepancy,Nat.zero_add,sub_ne_zero]

end KroneckerIntervalBadStarts
end

/- Original module: KroneckerGoodLengthPartition -/
section
/-! Scan the first run: cut at bad starts and otherwise merge into the first good piece. -/
set_option autoImplicit false
namespace KroneckerGoodLengthPartition
open KroneckerMechanicalWindows KroneckerGoodIntervals KroneckerIntervalBadStarts

def GoodLengths (s u : ℝ) (p : ℤ) (q start : ℕ) : List ℕ → Prop
  | [] => True
  | k::ks => GoodWindows s u p q start k ∧ GoodLengths s u p q (start+k) ks

theorem good_length_partition (s u : ℝ) (p : ℤ) (q n start : ℕ) (hq : 2 ≤ q) :
    ∃ lengths : List ℕ, lengths ≠ [] ∧ lengths.sum=n ∧
      GoodLengths s u p q start lengths ∧ lengths.length ≤ intervalBad s u p q start n+1 := by
  classical
  induction n generalizing start with
  | zero =>
    refine ⟨[0],by simp,by simp,?_,?_⟩
    · constructor
      · intro i hi; omega
      · trivial
    · rw [interval_bad_zero s u p q start (by omega)]
      simp
  | succ n ih =>
    obtain ⟨lengths,hne,hsum,hgood,hcount⟩ := ih (start+1)
    by_cases hbad : q ≤ n+1 ∧ windowSum s u q start ≠ p
    · refine ⟨1::lengths,by simp,by simp [hsum]; omega,?_,?_⟩
      · exact ⟨by intro i hi; omega,hgood⟩
      · rw [interval_bad_successor s u p q start n,ite_eq_left hbad]
        simp only [List.length_cons]
        omega
    · cases lengths with
      | nil => exact False.elim (hne rfl)
      | cons k ks =>
        have hgood' : GoodWindows s u p q (start+1) k ∧ GoodLengths s u p q (start+1+k) ks := hgood
        refine ⟨(k+1)::ks,by simp,?_,?_,?_⟩
        · simp only [List.sum_cons] at hsum ⊢
          omega
        · constructor
          · intro i hi
            by_cases hi0 : i=0
            · subst i
              have hk : k ≤ n := by simp only [List.sum_cons] at hsum; omega
              have hq' : q ≤ n+1 := by omega
              have hw : windowSum s u q start=p := by by_contra h; exact hbad ⟨hq',h⟩
              simpa using hw
            · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
              have h := hgood'.1 j (by omega)
              simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
          · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hgood'.2
        · rw [interval_bad_successor s u p q start n,ite_eq_right hbad]
          simpa only [List.length_cons,Nat.add_zero] using hcount

end KroneckerGoodLengthPartition
end

/- Original module: KroneckerSparseGoodPartition -/
section
/-! Turn the recursive length partition into literal adjacent mechanical subwords. -/
set_option autoImplicit false
namespace KroneckerSparseGoodPartition
open KroneckerMechanicalWords KroneckerMechanicalWordSums KroneckerGoodIntervals
open KroneckerGoodLengthPartition KroneckerGoodPartitionUpper KroneckerIntervalBadStarts

def adjacentIntervals (start : ℕ) : List ℕ → List (ℕ×ℕ)
  | [] => []
  | k::ks => (start,k)::adjacentIntervals (start+k) ks

theorem adjacent_intervals_length (start : ℕ) (lengths : List ℕ) :
    (adjacentIntervals start lengths).length=lengths.length := by
  induction lengths generalizing start with
  | nil => rfl
  | cons k ks ih => simp only [adjacentIntervals,List.length_cons,ih]

theorem adjacent_intervals_partition (s u : ℝ) (p : ℤ) (q start : ℕ) (lengths : List ℕ)
    (h : GoodLengths s u p q start lengths) :
    GoodPartition s u p q start lengths.sum (adjacentIntervals start lengths) := by
  induction lengths generalizing start with
  | nil => constructor <;> simp [adjacentIntervals,mechanicalWord]
  | cons k ks ih =>
    obtain ⟨hfirst,htail⟩ := h
    obtain ⟨hflat,hgood⟩ := ih (start+k) htail
    constructor
    · simp only [adjacentIntervals,List.flatMap_cons,List.sum_cons,hflat]
      exact (mechanicalWord_append s u start k ks.sum).symm
    · intro z hz
      simp only [adjacentIntervals,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hfirst
      · exact hgood z hz

theorem sparse_good_partition (s u : ℝ) (p : ℤ) (q start n : ℕ) (hq : 2 ≤ q) :
    ∃ parts, GoodPartition s u p q start n parts ∧
      parts.length ≤ intervalBad s u p q start n+1 := by
  obtain ⟨lengths,_,hsum,hgood,hcount⟩ := good_length_partition s u p q n start hq
  refine ⟨adjacentIntervals start lengths,?_,?_⟩
  · simpa only [hsum] using adjacent_intervals_partition s u p q start lengths hgood
  · simpa only [adjacent_intervals_length] using hcount

end KroneckerSparseGoodPartition
end
