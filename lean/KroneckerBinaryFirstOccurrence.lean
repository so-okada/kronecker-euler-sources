import KroneckerBinarySwapRuns

/- Original module: KroneckerBinaryPrefixArea -/
section
/-! The area between binary prefix-count functions, computed recursively with an integer offset. -/
set_option autoImplicit false
namespace KroneckerBinaryPrefixArea

def bit (b : Bool) : ℤ := if b then 1 else 0

def prefixArea (d : ℤ) : List Bool → List Bool → ℕ
  | x::xs,y::ys => (d+bit x-bit y).natAbs+prefixArea (d+bit x-bit y) xs ys
  | _,_ => 0

def swapDistance (xs ys : List Bool) : ℕ := prefixArea 0 xs ys

theorem bit_bounds (b : Bool) : 0≤bit b ∧ bit b≤1 := by cases b <;> decide

theorem prefixArea_same_head (d : ℤ) (b : Bool) (xs ys : List Bool) :
    prefixArea d (b::xs) (b::ys)=d.natAbs+prefixArea d xs ys := by
  simp only [prefixArea,add_sub_cancel_right]

theorem swapDistance_same_head (b : Bool) (xs ys : List Bool) :
    swapDistance (b::xs) (b::ys)=swapDistance xs ys := by
  simp [swapDistance,prefixArea_same_head]

theorem swapDistance_self (xs : List Bool) : swapDistance xs xs=0 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => rw [swapDistance_same_head,ih]

end KroneckerBinaryPrefixArea
end

/- Original module: KroneckerBinaryAreaComplement -/
section
/-! Complementing both binary words negates prefix discrepancies and preserves their absolute area. -/
set_option autoImplicit false
namespace KroneckerBinaryAreaComplement
open KroneckerBinaryPrefixArea

theorem bit_not (b : Bool) : bit (!b)=1-bit b := by cases b <;> rfl

theorem prefixArea_complement (d : ℤ) (xs ys : List Bool) :
    prefixArea (-d) (xs.map Bool.not) (ys.map Bool.not)=prefixArea d xs ys := by
  induction xs generalizing d ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.map_cons,prefixArea,bit_not]
      have he : -d+(1-bit x)-(1-bit y)=-(d+bit x-bit y) := by ring
      rw [he,Int.natAbs_neg,ih]

theorem swapDistance_complement (xs ys : List Bool) :
    swapDistance (xs.map Bool.not) (ys.map Bool.not)=swapDistance xs ys := by
  simpa [swapDistance] using prefixArea_complement 0 xs ys

end KroneckerBinaryAreaComplement
end

/- Original module: KroneckerBinaryBubble -/
section
/-! Move one bit across a block of opposite bits with exactly the block length in unequal swaps. -/
set_option autoImplicit false
namespace KroneckerBinaryBubble
open KroneckerBinarySwapPrograms KroneckerBinarySwapContext

noncomputable def bubbleFalse (j : ℕ) (xs : List Bool) :
    Swaps (List.replicate j true++false::xs) (false::List.replicate j true++xs) j := by
  induction j with
  | zero => exact .nil
  | succ j ih =>
    have q : Swaps (List.replicate (j+1) true++false::xs)
        ([]++pairBits false++(List.replicate j true++xs)) j := by
      simpa [pairBits,List.replicate_succ] using contextSwaps ih [true] []
    simpa [pairBits,List.replicate_succ] using Swaps.step false q

noncomputable def bubbleTrue (j : ℕ) (xs : List Bool) :
    Swaps (List.replicate j false++true::xs) (true::List.replicate j false++xs) j := by
  induction j with
  | zero => exact .nil
  | succ j ih =>
    have q : Swaps (List.replicate (j+1) false++true::xs)
        ([]++pairBits true++(List.replicate j false++xs)) j := by
      simpa [pairBits,List.replicate_succ] using contextSwaps ih [false] []
    simpa [pairBits,List.replicate_succ] using Swaps.step true q

theorem bubble_programs (j : ℕ) (xs : List Bool) :
    Nonempty (Swaps (List.replicate j true++false::xs) (false::List.replicate j true++xs) j) ∧
    Nonempty (Swaps (List.replicate j false++true::xs) (true::List.replicate j false++xs) j) :=
  ⟨⟨bubbleFalse j xs⟩,⟨bubbleTrue j xs⟩⟩

end KroneckerBinaryBubble
end

/- Original module: KroneckerBinaryAreaOffset -/
section
/-! Moving one unmatched one across a block of ones changes prefix area by exactly the block length. -/
set_option autoImplicit false
namespace KroneckerBinaryAreaOffset
open KroneckerBinaryPrefixArea

theorem natAbs_succ_nonneg (d : ℤ) (hd : 0 ≤ d) : (d+1).natAbs=d.natAbs+1 := by
  omega

theorem prefixArea_offset_block (j : ℕ) (d : ℤ) (hd : 0 ≤ d)
    (xs ys : List Bool) (hl : j < ys.length) :
    prefixArea (d+1) (List.replicate j true++false::xs) ys =
      j+prefixArea d (List.replicate j true++true::xs) ys := by
  induction j generalizing d ys with
  | zero =>
    cases ys with
    | nil => simp at hl
    | cons y ys => simp [prefixArea,bit]
  | succ j ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hb := bit_bounds y
      have hd' : 0 ≤ d+1-bit y := by omega
      have hl' : j < ys.length := by simpa using hl
      have he : d+1+bit true-bit y=(d+1-bit y)+1 := by simp [bit]; omega
      simp only [List.replicate_succ,List.cons_append,prefixArea]
      rw [he,ih _ hd' _ hl',natAbs_succ_nonneg _ hd']
      simp only [bit,ite_true]
      omega

end KroneckerBinaryAreaOffset
end

/- Original module: KroneckerBinaryBubbleArea -/
section
/-! The greedy bubble step decreases prefix area by exactly its counted swaps. -/
set_option autoImplicit false
namespace KroneckerBinaryBubbleArea
open KroneckerBinaryPrefixArea KroneckerBinaryAreaOffset KroneckerBinaryAreaComplement

theorem bubbleFalse_area (j : ℕ) (xs ys : List Bool) (hl : j ≤ ys.length) :
    swapDistance (List.replicate j true++false::xs) (false::ys)=
      j+swapDistance (List.replicate j true++xs) ys := by
  cases j with
  | zero => simpa using swapDistance_same_head false xs ys
  | succ j =>
    have hh := prefixArea_offset_block j 0 (by omega) xs ys (by omega)
    have he : List.replicate j true++true::xs=List.replicate (j+1) true++xs := by
      simp only [List.replicate_succ',List.append_assoc,List.singleton_append]
    rw [he] at hh
    change 1+prefixArea 1 (List.replicate j true++false::xs) ys = _
    change prefixArea 1 (List.replicate j true++false::xs) ys = _ at hh
    rw [hh]
    simp [swapDistance,Nat.add_assoc,Nat.add_left_comm]

theorem bubbleTrue_area (j : ℕ) (xs ys : List Bool) (hl : j ≤ ys.length) :
    swapDistance (List.replicate j false++true::xs) (true::ys)=
      j+swapDistance (List.replicate j false++xs) ys := by
  have h := bubbleFalse_area j (xs.map Bool.not) (ys.map Bool.not) (by simpa using hl)
  have hc := swapDistance_complement (List.replicate j false++true::xs) (true::ys)
  have ht := swapDistance_complement (List.replicate j false++xs) ys
  simp only [List.map_append,List.map_replicate,List.map_cons,Bool.not_false,Bool.not_true] at hc ht
  rw [hc,ht] at h
  exact h

end KroneckerBinaryBubbleArea
end

/- Original module: KroneckerBinaryFirstOccurrence -/
section
/-! Locate the first requested bit and identify the preceding constant opposite block. -/
set_option autoImplicit false
namespace KroneckerBinaryFirstOccurrence

theorem first_occurrence (b : Bool) (xs : List Bool) (hb : b ∈ xs) :
    ∃ j rest, xs=List.replicate j (!b)++b::rest := by
  induction xs with
  | nil => simp at hb
  | cons x xs ih =>
    by_cases h : x=b
    · exact ⟨0,xs,by simp [h]⟩
    · have hx : x=(!b) := by cases x <;> cases b <;> simp_all
      have hb' : b ∈ xs := by simpa [List.mem_cons,Ne.symm h] using hb
      obtain ⟨j,rest,he⟩ := ih hb'
      exact ⟨j+1,rest,by simp [List.replicate_succ,hx,he]⟩

theorem count_true_false (xs : List Bool) : xs.count true+xs.count false=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all <;> omega

theorem same_counts_of_length_count (xs ys : List Bool)
    (hl : xs.length=ys.length) (hc : xs.count true=ys.count true) :
    ∀ b : Bool, xs.count b=ys.count b := by
  have hx := count_true_false xs
  have hy := count_true_false ys
  intro b
  cases b <;> omega

end KroneckerBinaryFirstOccurrence
end
