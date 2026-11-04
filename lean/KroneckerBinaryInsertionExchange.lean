import KroneckerBinaryFirstOccurrence

section

/-! Realize the entire binary prefix area by a finite sequence of unequal adjacent exchanges. -/
set_option autoImplicit false
namespace KroneckerBinaryGreedyExchange
open KroneckerBinaryPrefixArea KroneckerBinaryBubbleArea KroneckerBinaryBubble
open KroneckerBinarySwapPrograms KroneckerBinarySwapContext KroneckerBinaryFirstOccurrence

theorem binary_area_program (xs ys : List Bool) (hl : xs.length=ys.length)
    (hc : ∀ b : Bool, xs.count b=ys.count b) : Nonempty (Swaps xs ys (swapDistance xs ys)) := by
  induction ys generalizing xs with
  | nil =>
    have hx : xs=[] := List.length_eq_zero_iff.mp hl
    subst xs
    exact ⟨.nil⟩
  | cons b ys ih =>
    have hb : b ∈ xs := List.count_pos_iff.mp (by rw [hc b,List.count_cons_self]; omega)
    obtain ⟨j,rest,rfl⟩ := first_occurrence b xs hb
    have hp : Swaps (List.replicate j (!b)++b::rest) (b::List.replicate j (!b)++rest) j := by
      cases b
      · exact bubbleFalse j rest
      · exact bubbleTrue j rest
    have hl' : (List.replicate j (!b)++rest).length=ys.length := by
      simp only [List.length_append,List.length_replicate,List.length_cons] at hl ⊢
      omega
    have hj : j ≤ ys.length := by
      simp only [List.length_append,List.length_replicate] at hl'
      omega
    have hc' : ∀ c : Bool, (List.replicate j (!b)++rest).count c=ys.count c := by
      intro c
      have h1 := swaps_count hp c
      have h2 := hc c
      simp only [List.cons_append,List.count_cons] at h1 h2
      omega
    obtain ⟨q⟩ := ih _ hl' hc'
    have hq : Swaps (b::List.replicate j (!b)++rest) (b::ys)
        (swapDistance (List.replicate j (!b)++rest) ys) := by
      simpa using contextSwaps q [b] []
    have he : swapDistance (List.replicate j (!b)++b::rest) (b::ys)=
        j+swapDistance (List.replicate j (!b)++rest) ys := by
      cases b
      · exact bubbleFalse_area j rest ys hj
      · exact bubbleTrue_area j rest ys hj
    rw [he]
    exact ⟨appendSwaps hp hq⟩

noncomputable def areaProgram (xs ys : List Bool) (hl : xs.length=ys.length)
    (hc : xs.count true=ys.count true) : Swaps xs ys (swapDistance xs ys) :=
  Classical.choice (binary_area_program xs ys hl (same_counts_of_length_count xs ys hl hc))


end KroneckerBinaryGreedyExchange
end

section

/- Original module: KroneckerBinaryAppendInsertions -/
section
/-! Append a prescribed binary list using one complete-run insertion per letter and no exchanges. -/
set_option autoImplicit false
namespace KroneckerBinaryAppendInsertions
open KroneckerBinarySwapRuns KroneckerRawBinaryEdits

noncomputable def appendBits (xs as : List Bool) :
    RawBinary (bitRuns xs) (bitRuns (xs++as)) as.length 0 := by
  induction as with
  | nil => simpa using (RawBinary.nil : RawBinary (bitRuns xs) (bitRuns xs) 0 0)
  | cons b as ih =>
    have hp : RawBinary (bitRuns xs) (bitRuns xs++bitRuns as) as.length 0 := by
      simpa only [bitRuns,List.map_append] using ih
    have hr : 1 ≤ (if b then 2 else 1 : ℕ) ∧ (if b then 2 else 1 : ℕ) ≤ 2 := by
      cases b <;> decide
    simpa only [bitRuns,List.map_append,List.map_cons,List.length_cons] using
      RawBinary.insert hp (if b then 2 else 1) hr


end KroneckerBinaryAppendInsertions
end

/- Original module: KroneckerBinaryBalancingLetters -/
section
/-! The canonical appended balancing word has exactly the missing zeros and ones. -/
set_option autoImplicit false
namespace KroneckerBinaryBalancingLetters
open KroneckerBinaryFirstOccurrence

def balancingLetters (xs ys : List Bool) : List Bool :=
  List.replicate (ys.count false-xs.count false) false++
  List.replicate (ys.count true-xs.count true) true

theorem balancing_counts (xs ys : List Bool)
    (hc : ∀ b : Bool, xs.count b ≤ ys.count b) (b : Bool) :
    (xs++balancingLetters xs ys).count b=ys.count b := by
  have h := hc b
  cases b <;> simp [balancingLetters,List.count_append,List.count_replicate] <;> omega

theorem balancing_length (xs ys : List Bool) (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    xs.length+(balancingLetters xs ys).length=ys.length := by
  have hf := balancing_counts xs ys hc false
  have ht := balancing_counts xs ys hc true
  have hx := count_true_false (xs++balancingLetters xs ys)
  have hy := count_true_false ys
  simp only [List.length_append] at hx
  omega

theorem balancing_length_sub (xs ys : List Bool) (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    (balancingLetters xs ys).length=ys.length-xs.length := by
  have h := balancing_length xs ys hc
  omega

end KroneckerBinaryBalancingLetters
end

/- Original module: KroneckerBinaryInsertionExchange -/
section
/-! Domination of both letter counts gives an actual insertion/exchange program. -/
set_option autoImplicit false
namespace KroneckerBinaryInsertionExchange
open KroneckerBinaryAppendInsertions KroneckerBinaryBalancingLetters KroneckerBinaryGreedyExchange
open KroneckerBinaryPrefixArea KroneckerBinarySwapRuns KroneckerRawBinaryConcatenation
open KroneckerRawBinaryEdits

noncomputable def insertionExchange (xs ys : List Bool)
    (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    RawBinary (bitRuns xs) (bitRuns ys) (ys.length-xs.length)
      (swapDistance (xs++balancingLetters xs ys) ys) := by
  let as := balancingLetters xs ys
  have hl : (xs++as).length=ys.length := by
    simpa only [List.length_append] using balancing_length xs ys hc
  have ht : (xs++as).count true=ys.count true := balancing_counts xs ys hc true
  have p := appendRawBinary (appendBits xs as) (swapsToRaw (areaProgram (xs++as) ys hl ht))
  simpa only [Nat.add_zero,Nat.zero_add,as,balancing_length_sub xs ys hc] using p


end KroneckerBinaryInsertionExchange
end
end

section

/-! Identify the recursive exchange cost with the sum of absolute prefix-count differences. -/
set_option autoImplicit false
namespace KroneckerBinaryPrefixSum
open KroneckerBinaryPrefixArea

def prefixDelta (d : ℤ) (xs ys : List Bool) (j : ℕ) : ℤ :=
  d+(xs.take j).count true-(ys.take j).count true

theorem count_cons_int (x : Bool) (xs : List Bool) :
    ((x::xs).count true : ℤ)=bit x+(xs.count true : ℤ) := by
  cases x with
  | false => simp [bit]
  | true => simp [bit,add_comm]

theorem prefixDelta_cons (d : ℤ) (x y : Bool) (xs ys : List Bool) (j : ℕ) :
    prefixDelta d (x::xs) (y::ys) (j+1)=prefixDelta (d+bit x-bit y) xs ys j := by
  simp only [prefixDelta,List.take_succ_cons,count_cons_int]
  ring

theorem prefixArea_sum (d : ℤ) (xs ys : List Bool) (hl : xs.length=ys.length) :
    prefixArea d xs ys=∑ j ∈ Finset.range xs.length, (prefixDelta d xs ys (j+1)).natAbs := by
  induction xs generalizing d ys with
  | nil => simp [prefixArea]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length=ys.length := by simpa using hl
      simp only [List.length_cons,Finset.sum_range_succ',prefixDelta_cons]
      rw [prefixArea,ih _ _ hl']
      simp [prefixDelta,Nat.add_comm]

theorem swapDistance_prefix_sum (xs ys : List Bool) (hl : xs.length=ys.length) :
    swapDistance xs ys=∑ j ∈ Finset.range xs.length,
      (((xs.take (j+1)).count true : ℤ)-(ys.take (j+1)).count true).natAbs := by
  simpa [swapDistance,prefixDelta] using prefixArea_sum 0 xs ys hl

end KroneckerBinaryPrefixSum
end

