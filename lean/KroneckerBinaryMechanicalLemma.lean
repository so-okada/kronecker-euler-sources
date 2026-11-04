import KroneckerBinaryInsertionExchange
import KroneckerMechanicalCountDomination
import KroneckerIrrationalWordSubsequence
import KroneckerSmallBlockCoefficients

section

/-! A balanced tail of length C contributes at most C squared to binary prefix area. -/
set_option autoImplicit false
namespace KroneckerBinaryBalancedArea
open KroneckerBinaryPrefixArea KroneckerBinaryPrefixSum

theorem balanced_offset_bound (d : ℤ) (xs ys : List Bool)
    (hl : xs.length=ys.length) (hb : d+(xs.count true : ℤ)-(ys.count true : ℤ)=0) :
    d.natAbs ≤ xs.length := by
  have hx := List.count_le_length (a := true) (l := xs)
  have hy := List.count_le_length (a := true) (l := ys)
  omega

theorem prefixArea_balanced_le_sq (d : ℤ) (xs ys : List Bool)
    (hl : xs.length=ys.length) (hb : d+(xs.count true : ℤ)-(ys.count true : ℤ)=0) :
    prefixArea d xs ys ≤ xs.length^2 := by
  induction xs generalizing d ys with
  | nil => simp [prefixArea]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length=ys.length := by simpa using hl
      have hb' : d+bit x-bit y+(xs.count true : ℤ)-(ys.count true : ℤ)=0 := by
        rw [count_cons_int,count_cons_int] at hb
        omega
      have h1 := balanced_offset_bound _ xs ys hl' hb'
      have h2 := ih _ ys hl' hb'
      simp only [prefixArea,List.length_cons]
      nlinarith

end KroneckerBinaryBalancedArea
end

section

/-! Insert a prescribed binary run prefix without any exchanges, including before the old middle. -/
set_option autoImplicit false
namespace KroneckerBinaryPrefixInsertions
open KroneckerRawBinaryEdits KroneckerRawBinaryConcatenation KroneckerRawBinaryContext

noncomputable def prependBinary (R A : List ℕ) (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ 2) :
    RawBinary R (A++R) A.length 0 := by
  induction A with
  | nil => exact .nil
  | cons a A ih =>
    have ha := hA a (by simp)
    have htail : ∀ r ∈ A, 1 ≤ r ∧ r ≤ 2 := fun r hr => hA r (by simp [hr])
    have hp : RawBinary R ([]++(A++R)) A.length 0 := ih htail
    simpa only [List.nil_append,List.cons_append,List.length_cons] using RawBinary.insert hp a ha


noncomputable def prependAfter {R S : List ℕ} {K k : ℕ} (p : RawBinary R S K k)
    (A : List ℕ) (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ 2) : RawBinary R (A++S) (A.length+K) k := by
  have q := appendRawBinary p (prependBinary S A hA)
  simpa only [Nat.add_zero,Nat.add_comm] using q


end KroneckerBinaryPrefixInsertions
end

section

/-! A mechanical binary prefix followed by an arbitrary binary exceptional last run. -/
set_option autoImplicit false
namespace KroneckerBinaryTerminalWord
open KroneckerMechanicalBits KroneckerMechanicalLetterBounds KroneckerBinarySwapRuns
open KroneckerMechanicalWords

noncomputable def terminalBits (s u : ℝ) (n : ℕ) (b : Bool) : List Bool := mechanicalBits s u n++[b]

theorem terminalBits_length (s u : ℝ) (n : ℕ) (b : Bool) : (terminalBits s u n b).length=n+1 := by
  simp [terminalBits,mechanicalBits_length]

theorem terminalBits_runs (s u : ℝ) (n : ℕ) (b : Bool) (hs : 1 ≤ s ∧ s ≤ 2) :
    bitRuns (terminalBits s u n b)=mechanicalWord s u 0 n++[if b then 2 else 1] := by
  have h := congrArg (fun xs => xs++[if b then 2 else 1]) (mechanicalBits_runs s u n hs)
  simpa only [terminalBits,bitRuns,List.map_append,List.map_cons,List.map_nil] using h

theorem terminal_letter_error (s u : ℝ) (n : ℕ) (b c : Bool) (hs : 1 ≤ s ∧ s ≤ 2) :
    |((terminalBits s u n b).count c : ℝ)-((n+1 : ℕ) : ℝ)*frequency s c| < 2 := by
  have h := abs_lt.mp (mechanical_letter_error s u n hs c)
  have hf := frequency_bounds s hs c
  have he : (([b] : List Bool).count c : ℝ) ≤ 1 := by
    have hh := List.count_le_length (a:=c) (l:=[b]); exact_mod_cast hh
  have he0 : (0 : ℝ) ≤ ([b].count c : ℝ) := by positivity
  simp only [terminalBits,List.count_append,Nat.cast_add,Nat.cast_one]
  apply abs_lt.mpr
  constructor <;> nlinarith

end KroneckerBinaryTerminalWord
end

section

/- Original module: KroneckerBinarySquareComparison -/
section
/-! A crude uniform bound for a count-dominated finite binary comparison. -/
set_option autoImplicit false
namespace KroneckerBinarySquareComparison
open KroneckerBinaryInsertionExchange KroneckerBinaryBalancingLetters KroneckerBinaryBalancedArea
open KroneckerBinaryPrefixArea KroneckerBinarySwapRuns KroneckerRawBinaryEdits

theorem insertion_exchange_square (xs ys : List Bool)
    (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    ∃ k, Nonempty (RawBinary (bitRuns xs) (bitRuns ys) (ys.length-xs.length) k) ∧ k ≤ ys.length^2 := by
  have hl : (xs++balancingLetters xs ys).length=ys.length := by
    simpa only [List.length_append] using balancing_length xs ys hc
  have ht := balancing_counts xs ys hc true
  have hb : (0 : ℤ)+((xs++balancingLetters xs ys).count true : ℤ)-(ys.count true : ℤ)=0 := by omega
  have ha := prefixArea_balanced_le_sq 0 (xs++balancingLetters xs ys) ys hl hb
  rw [hl] at ha
  exact ⟨_,⟨insertionExchange xs ys hc⟩,ha⟩

end KroneckerBinarySquareComparison
end

/- Original module: KroneckerBinaryTerminalDomination -/
section
/-! One exceptional binary terminal run costs one extra unit in the count-domination budget. -/
set_option autoImplicit false
namespace KroneckerBinaryTerminalDomination
open KroneckerBinaryTerminalWord KroneckerMechanicalBits KroneckerMechanicalLetterBounds
open KroneckerMechanicalCountDomination

theorem terminal_count_domination (s u t v τ e : ℝ) (n C : ℕ) (b : Bool)
    (hs : 1 ≤ s ∧ s ≤ 2) (ht : 1 ≤ t ∧ t ≤ 2)
    (hmargin : ∀ c : Bool, τ ≤ frequency t c) (hst : |s-t| ≤ e)
    (hbudget : 3+((n+1 : ℕ) : ℝ)*e ≤ (C : ℝ)*τ) :
    ∀ c : Bool, (terminalBits s u n b).count c ≤ (mechanicalBits t v (n+1+C)).count c := by
  intro c
  have ha := (abs_lt.mp (terminal_letter_error s u n b c hs)).2
  have hb := (abs_lt.mp (mechanical_letter_error t v (n+1+C) ht c)).1
  have hfreq : frequency s c-frequency t c ≤ e :=
    (le_abs_self _).trans (by rw [frequency_distance]; exact hst)
  have hnf := mul_le_mul_of_nonneg_left hfreq (show (0 : ℝ) ≤ (n+1 : ℕ) by positivity)
  have hCf := mul_le_mul_of_nonneg_left (hmargin c) (show (0 : ℝ) ≤ C by positivity)
  have hreal : ((terminalBits s u n b).count c : ℝ) ≤
      ((mechanicalBits t v (n+1+C)).count c : ℝ) := by
    push_cast at hb ha hnf hbudget
    nlinarith
  exact_mod_cast hreal

end KroneckerBinaryTerminalDomination
end

/- Original module: KroneckerBinaryTerminalEdits -/
section
/-! The exceptional terminal block admits a bounded actual comparison at every target phase. -/
set_option autoImplicit false
namespace KroneckerBinaryTerminalEdits
open KroneckerBinaryTerminalWord KroneckerBinaryTerminalDomination KroneckerBinarySquareComparison
open KroneckerMechanicalBits KroneckerMechanicalWords KroneckerMechanicalLetterBounds KroneckerRawBinaryEdits

theorem terminal_block_edits (s u t v τ e : ℝ) (n C : ℕ) (b : Bool)
    (hs : 1 ≤ s ∧ s ≤ 2) (ht : 1 ≤ t ∧ t ≤ 2)
    (hmargin : ∀ c : Bool, τ ≤ frequency t c) (hst : |s-t| ≤ e)
    (hbudget : 3+((n+1 : ℕ) : ℝ)*e ≤ (C : ℝ)*τ) :
    ∃ k, Nonempty (RawBinary (mechanicalWord s u 0 n++[if b then 2 else 1])
      (mechanicalWord t v 0 (n+1+C)) C k) ∧ k ≤ (n+1+C)^2 := by
  have hc := terminal_count_domination s u t v τ e n C b hs ht hmargin hst hbudget
  obtain ⟨k,hp,hk⟩ := insertion_exchange_square (terminalBits s u n b) (mechanicalBits t v (n+1+C)) hc
  refine ⟨k,?_,?_⟩
  · simpa only [terminalBits_runs s u n b hs,mechanicalBits_runs t v (n+1+C) ht,
      terminalBits_length,mechanicalBits_length,Nat.add_sub_cancel_left] using hp
  · simpa only [mechanicalBits_length] using hk

end KroneckerBinaryTerminalEdits
end

/- Original module: KroneckerShiftedBinaryTerminal -/
section
/-! The bounded exceptional terminal comparison is independent of both starting indices. -/
set_option autoImplicit false
namespace KroneckerShiftedBinaryTerminal
open KroneckerBinaryTerminalEdits KroneckerMechanicalWordShift KroneckerMechanicalWords
open KroneckerMechanicalLetterBounds KroneckerRawBinaryEdits

theorem shifted_terminal_edits (s u t v τ e : ℝ) (i a n C : ℕ) (b : Bool)
    (hs : 1 ≤ s ∧ s ≤ 2) (ht : 1 ≤ t ∧ t ≤ 2)
    (hmargin : ∀ c : Bool, τ ≤ frequency t c) (hst : |s-t| ≤ e)
    (hbudget : 3+((n+1 : ℕ) : ℝ)*e ≤ (C : ℝ)*τ) :
    ∃ k, Nonempty (RawBinary (mechanicalWord s u i n++[if b then 2 else 1])
      (mechanicalWord t v a (n+1+C)) C k) ∧ k ≤ (n+1+C)^2 := by
  obtain ⟨k,hp,hk⟩ := terminal_block_edits s (u+(i : ℝ)*s) t (v+(a : ℝ)*t) τ e n C b
    hs ht hmargin hst hbudget
  refine ⟨k,?_,hk⟩
  simpa only [← word_shift] using hp

end KroneckerShiftedBinaryTerminal
end
end

section

/- Original module: KroneckerMechanicalBinaryArea -/
section
/-! Mechanical binary exchange area is the mass of the actual floor-prefix discrepancy. -/
set_option autoImplicit false
namespace KroneckerMechanicalBinaryArea
open KroneckerMechanicalBits KroneckerMechanicalBitCounts KroneckerBinaryPrefixArea
open KroneckerBinaryPrefixSum KroneckerPrefixDiscrepancy

theorem mechanical_binary_area (s u t v : ℝ) (n : ℕ)
    (hs : 1 ≤ s ∧ s ≤ 2) (ht : 1 ≤ t ∧ t ≤ 2)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) :
    (swapDistance (mechanicalBits s u n) (mechanicalBits t v n) : ℝ)=
      ∑ j ∈ Finset.range n, |discrepancy s u t v (j+1)| := by
  rw [swapDistance_prefix_sum _ _ (by simp [mechanicalBits_length]),mechanicalBits_length]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.cast_natAbs,mechanical_prefix_count_difference s u t v n (j+1)
    (by have := Finset.mem_range.mp hj; omega) hs ht hu hv]
  simp only [Int.cast_abs,Int.cast_sub,discrepancy]

end KroneckerMechanicalBinaryArea
end

/- Original module: KroneckerAlignedBinaryArea -/
section
/-! Aligned binary mechanical words have exchange area supported only at near-integer visits. -/
set_option autoImplicit false
namespace KroneckerAlignedBinaryArea
open KroneckerMechanicalBits KroneckerBinaryPrefixArea KroneckerMechanicalBinaryArea
open KroneckerBoundaryVisits KroneckerAlignedOrbitError

theorem aligned_binary_area (s u t v ε : ℝ) (n : ℕ)
    (hs : 1 ≤ s ∧ s ≤ 2) (ht : 1 ≤ t ∧ t ≤ 2)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) (hε : ε ≤ 1)
    (hclose : |u-v|+(n : ℝ)*|s-t| < ε) :
    swapDistance (mechanicalBits s u n) (mechanicalBits t v n) ≤ visits s u ε n := by
  have h := discrepancy_mass_le_visits s u t v ε n hε
    (fun j hj => block_orbit_error s u t v ε n (j+1) (by omega) hclose)
  rw [← mechanical_binary_area s u t v n hs ht hu hv] at h
  exact_mod_cast h

end KroneckerAlignedBinaryArea
end

/- Original module: KroneckerBinaryAreaAppend -/
section
/-! Split binary prefix area at a common block boundary, retaining its actual discrepancy. -/
set_option autoImplicit false
namespace KroneckerBinaryAreaAppend
open KroneckerBinaryPrefixArea KroneckerBinaryPrefixSum

theorem prefixArea_append (d : ℤ) (xs ys as bs : List Bool) (hl : xs.length=ys.length) :
    prefixArea d (xs++as) (ys++bs)=prefixArea d xs ys+
      prefixArea (d+(xs.count true : ℤ)-(ys.count true : ℤ)) as bs := by
  induction xs generalizing d ys with
  | nil =>
    have hy : ys=[] := List.length_eq_zero_iff.mp hl.symm
    subst ys
    simp [prefixArea]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length=ys.length := by simpa using hl
      simp only [List.cons_append,prefixArea]
      rw [ih _ _ hl']
      rw [count_cons_int,count_cons_int]
      have he : d+bit x-bit y+(xs.count true : ℤ)-(ys.count true : ℤ)=
          d+(bit x+(xs.count true : ℤ))-(bit y+(ys.count true : ℤ)) := by ring
      rw [he,Nat.add_assoc]

theorem swapDistance_append (xs ys as bs : List Bool) (hl : xs.length=ys.length) :
    swapDistance (xs++as) (ys++bs)=swapDistance xs ys+
      prefixArea ((xs.count true : ℤ)-(ys.count true : ℤ)) as bs := by
  simpa [swapDistance] using prefixArea_append 0 xs ys as bs hl

end KroneckerBinaryAreaAppend
end

/- Original module: KroneckerBinaryPaddedArea -/
section
/-! Appending C balancing letters costs at most C squared beyond the original block discrepancy. -/
set_option autoImplicit false
namespace KroneckerBinaryPaddedArea
open KroneckerBinaryPrefixArea KroneckerBinaryAreaAppend KroneckerBinaryBalancedArea

theorem padded_swapDistance_bound (xs ys as bs : List Bool)
    (hl : xs.length=ys.length) (ht : as.length=bs.length)
    (hc : (xs++as).count true=(ys++bs).count true) :
    swapDistance (xs++as) (ys++bs) ≤ swapDistance xs ys+as.length^2 := by
  have hb : (xs.count true : ℤ)-(ys.count true : ℤ)+(as.count true : ℤ)-(bs.count true : ℤ)=0 := by
    simp only [List.count_append] at hc
    omega
  rw [swapDistance_append xs ys as bs hl]
  exact Nat.add_le_add_left (prefixArea_balanced_le_sq _ as bs ht hb) _

end KroneckerBinaryPaddedArea
end

/- Original module: KroneckerBinaryInsertionCost -/
section
/-! Quantitative insertion/exchange comparison from a prefix discrepancy and the length surplus. -/
set_option autoImplicit false
namespace KroneckerBinaryInsertionCost
open KroneckerBinaryInsertionExchange KroneckerBinaryBalancingLetters KroneckerBinaryPaddedArea
open KroneckerBinaryPrefixArea KroneckerBinarySwapRuns KroneckerRawBinaryEdits

theorem balancing_swap_cost (xs ys : List Bool)
    (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    swapDistance (xs++balancingLetters xs ys) ys ≤
      swapDistance xs (ys.take xs.length)+(ys.length-xs.length)^2 := by
  have hlen := balancing_length xs ys hc
  have hl : xs.length ≤ ys.length := by omega
  have hf : xs.length=(ys.take xs.length).length := by simp [List.length_take,Nat.min_eq_left hl]
  have ht : (balancingLetters xs ys).length=(ys.drop xs.length).length := by
    simp only [balancing_length_sub xs ys hc,List.length_drop]
  have hh := padded_swapDistance_bound xs (ys.take xs.length) (balancingLetters xs ys)
    (ys.drop xs.length) hf ht (by simpa using balancing_counts xs ys hc true)
  simpa only [List.take_append_drop,balancing_length_sub xs ys hc] using hh

theorem insertion_cost_program (xs ys : List Bool)
    (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    ∃ k, Nonempty (RawBinary (bitRuns xs) (bitRuns ys) (ys.length-xs.length) k) ∧
      k ≤ swapDistance xs (ys.take xs.length)+(ys.length-xs.length)^2 := by
  exact ⟨_,⟨insertionExchange xs ys hc⟩,balancing_swap_cost xs ys hc⟩

end KroneckerBinaryInsertionCost
end

/- Original module: KroneckerIrrationalBinaryArea -/
section
/-! Nearby irrational slopes admit uniformly sparse binary exchange-area bounds after alignment. -/
set_option autoImplicit false
namespace KroneckerIrrationalBinaryArea
open KroneckerMechanicalBits KroneckerBinaryPrefixArea KroneckerAlignedBinaryArea
open KroneckerIrrationalVisitDensity

theorem irrational_binary_area (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ ε δ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧
      ∀ s t u v : ℝ, |s-r| < δ → (1 ≤ s ∧ s ≤ 2) → (1 ≤ t ∧ t ≤ 2) →
      (0 ≤ u ∧ u < 1) → (0 ≤ v ∧ v < 1) → ∀ n : ℕ,
      |u-v|+(n : ℝ)*|s-t| < ε →
      swapDistance (mechanicalBits s u n) (mechanicalBits t v n) ≤ n/q+1 := by
  obtain ⟨ε,δ,hε,hε1,hδ,h⟩ := irrational_visit_density r hr q hq
  refine ⟨ε,δ,hε,hε1,hδ,?_⟩
  intro s t u v hs hsb htb hu hv n hc
  exact (aligned_binary_area s u t v ε n hsb htb hu hv hε1 hc).trans (h s hs u n)

end KroneckerIrrationalBinaryArea
end

/- Original module: KroneckerMechanicalBlockEdits -/
section
/-! Actual binary mechanical block edits: C insertions and prefix-area plus C squared exchanges. -/
set_option autoImplicit false
namespace KroneckerMechanicalBlockEdits
open KroneckerMechanicalBits KroneckerMechanicalWords KroneckerBinaryPrefixArea
open KroneckerBinaryInsertionCost KroneckerMechanicalCountDomination KroneckerMechanicalLetterBounds
open KroneckerRawBinaryEdits

theorem mechanical_block_edits (s u t v τ e : ℝ) (n C : ℕ)
    (hs : 1 ≤ s ∧ s ≤ 2) (ht : 1 ≤ t ∧ t ≤ 2)
    (hmargin : ∀ b : Bool, τ ≤ frequency t b) (hst : |s-t| ≤ e)
    (hbudget : 2+(n : ℝ)*e ≤ (C : ℝ)*τ) :
    ∃ k, Nonempty (RawBinary (mechanicalWord s u 0 n) (mechanicalWord t v 0 (n+C)) C k) ∧
      k ≤ swapDistance (mechanicalBits s u n) (mechanicalBits t v n)+C^2 := by
  have hc := mechanical_count_domination s u t v τ e n C hs ht hmargin hst hbudget
  obtain ⟨k,hp,hk⟩ := insertion_cost_program (mechanicalBits s u n) (mechanicalBits t v (n+C)) hc
  refine ⟨k,?_,?_⟩
  · simpa only [mechanicalBits_runs s u n hs,mechanicalBits_runs t v (n+C) ht,
      mechanicalBits_length,Nat.add_sub_cancel_left] using hp
  · simpa only [mechanicalBits_length,mechanicalBits_take _ _ _ _ (Nat.le_add_right n C),
      Nat.add_sub_cancel_left] using hk

end KroneckerMechanicalBlockEdits
end

/- Original module: KroneckerUniformBinaryAlignment -/
section
/-! Every pair of nearby binary mechanical blocks can be phase-aligned at a uniformly bounded shift. -/
set_option autoImplicit false
namespace KroneckerUniformBinaryAlignment
open KroneckerMechanicalBits KroneckerBinaryPrefixArea KroneckerIrrationalBinaryArea
open KroneckerUniformBlockAlignment

theorem uniform_binary_alignment (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s t u v : ℝ,
      |s-r| < δ → |t-r| < δ → (1 ≤ s ∧ s ≤ 2) → (1 ≤ t ∧ t ≤ 2) →
      (0 ≤ u ∧ u < 1) → (0 ≤ v ∧ v < 1) → ∀ n ≤ L,
      ∃ j < Q, swapDistance (mechanicalBits s u n)
        (mechanicalBits t (Int.fract (v+(j : ℝ)*t)) n) ≤ n/q+1 := by
  obtain ⟨ε,d,hε,hε1,hd,harea⟩ := irrational_binary_area r hr q hq
  obtain ⟨Q,hQ,hQall⟩ := uniform_block_alignment r ε hr hε
  refine ⟨Q,hQ,?_⟩
  intro L
  obtain ⟨a,ha,halign⟩ := hQall L
  refine ⟨min d a,lt_min hd ha,?_⟩
  intro s t u v hs ht hsb htb hu hv n hn
  obtain ⟨j,hj,hclose⟩ := halign s t u v (hs.trans_le (min_le_right _ _))
    (ht.trans_le (min_le_right _ _)) hu hv n hn
  refine ⟨j,hj,harea s t u _ (hs.trans_le (min_le_left _ _)) hsb htb hu
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ n hclose⟩

end KroneckerUniformBinaryAlignment
end

/- Original module: KroneckerUniformBinaryBlock -/
section
/-! Uniformly phase-align and edit into an actual shifted mechanical target block. -/
set_option autoImplicit false
namespace KroneckerUniformBinaryBlock
open KroneckerUniformBinaryAlignment KroneckerMechanicalBlockEdits KroneckerMechanicalLetterBounds
open KroneckerMechanicalWords KroneckerRawBinaryEdits KroneckerNormalizedWindow

theorem uniform_binary_block (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s t u v τ e : ℝ, |s-r| < δ → |t-r| < δ →
      (1 ≤ s ∧ s ≤ 2) → (1 ≤ t ∧ t ≤ 2) →
      (0 ≤ u ∧ u < 1) → (0 ≤ v ∧ v < 1) →
      (∀ b : Bool, τ ≤ frequency t b) → |s-t| ≤ e →
      ∀ n ≤ L, ∀ C : ℕ, 2+(n : ℝ)*e ≤ (C : ℝ)*τ →
      ∃ j < Q, ∃ k, Nonempty (RawBinary (mechanicalWord s u 0 n)
        (mechanicalWord t v j (n+C)) C k) ∧ k ≤ n/q+1+C^2 := by
  obtain ⟨Q,hQ,hall⟩ := uniform_binary_alignment r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L
  obtain ⟨δ,hδ,h⟩ := hall L
  refine ⟨δ,hδ,?_⟩
  intro s t u v τ e hs ht hsb htb hu hv hm he n hn C hbudget
  obtain ⟨j,hj,harea⟩ := h s t u v hs ht hsb htb hu hv n hn
  obtain ⟨k,hp,hk⟩ := mechanical_block_edits s u t (Int.fract (v+(j : ℝ)*t)) τ e n C
    hsb htb hm he hbudget
  refine ⟨j,hj,k,?_,by omega⟩
  simpa only [← normalized_window] using hp

end KroneckerUniformBinaryBlock
end

/- Original module: KroneckerUniformBinaryPrefixBlock -/
section
/-! A complete literal target prefix is obtained by inserting its phase prefix and editing the aligned block. -/
set_option autoImplicit false
namespace KroneckerUniformBinaryPrefixBlock
open KroneckerUniformBinaryBlock KroneckerBinaryPrefixInsertions KroneckerMechanicalLetterBounds
open KroneckerMechanicalWords KroneckerMechanicalWordSums KroneckerRawBinaryEdits

theorem uniform_binary_prefix_block (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s t u v τ e : ℝ, |s-r| < δ → |t-r| < δ →
      (1 ≤ s ∧ s ≤ 2) → (1 ≤ t ∧ t ≤ 2) →
      (0 ≤ u ∧ u < 1) → (0 ≤ v ∧ v < 1) →
      (∀ b : Bool, τ ≤ frequency t b) → |s-t| ≤ e →
      ∀ n ≤ L, ∀ C : ℕ, 2+(n : ℝ)*e ≤ (C : ℝ)*τ →
      ∃ j < Q, ∃ k, Nonempty (RawBinary (mechanicalWord s u 0 n)
        (mechanicalWord t v 0 (j+n+C)) (j+C) k) ∧ k ≤ n/q+1+C^2 := by
  obtain ⟨Q,hQ,hall⟩ := uniform_binary_block r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L
  obtain ⟨δ,hδ,h⟩ := hall L
  refine ⟨δ,hδ,?_⟩
  intro s t u v τ e hs ht hsb htb hu hv hm he n hn C hbudget
  obtain ⟨j,hj,k,⟨p⟩,hk⟩ := h s t u v τ e hs ht hsb htb hu hv hm he n hn C hbudget
  refine ⟨j,hj,k,?_,hk⟩
  have hprefix := mechanicalWord_legal t v 0 j 2 htb.1 htb.2
  have hp := prependAfter p (mechanicalWord t v 0 j) hprefix
  have hword : mechanicalWord t v 0 j++mechanicalWord t v j (n+C)=
      mechanicalWord t v 0 (j+n+C) := by
    simpa only [Nat.zero_add,Nat.add_assoc] using (mechanicalWord_append t v 0 j (n+C)).symm
  rw [hword,mechanicalWord_length] at hp
  exact ⟨hp⟩

end KroneckerUniformBinaryPrefixBlock
end
end

section

/- Original module: KroneckerBinaryLastRun -/
section
/-! Every nonempty ordinary mechanical binary word is a prefix with one legal final run. -/
set_option autoImplicit false
namespace KroneckerBinaryLastRun
open KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem mechanical_last_binary (s u : ℝ) (n : ℕ) (hs : 1 ≤ s ∧ s ≤ 2) :
    ∃ b : Bool, mechanicalWord s u 0 (n+1)=mechanicalWord s u 0 n++[if b then 2 else 1] := by
  have hr := natRun_legal s u n 2 hs.1 hs.2
  have he : natRun s u n=1 ∨ natRun s u n=2 := by omega
  rw [mechanicalWord_append,mechanicalWord_one]
  simp only [Nat.zero_add]
  rcases he with h | h
  · exact ⟨false,by simp [h]⟩
  · exact ⟨true,by simp [h]⟩

theorem binary_run_as_bit (r : ℕ) (hr : 1 ≤ r ∧ r ≤ 2) : ∃ b : Bool, r=(if b then 2 else 1) := by
  have he : r=1 ∨ r=2 := by omega
  rcases he with rfl | rfl
  · exact ⟨false,rfl⟩
  · exact ⟨true,rfl⟩

end KroneckerBinaryLastRun
end

/- Original module: KroneckerBinarySlopeMargin -/
section
/-! An interior binary slope has a uniform positive margin for both letter frequencies. -/
set_option autoImplicit false
namespace KroneckerBinarySlopeMargin
open KroneckerMechanicalLetterBounds

theorem binary_slope_margin (r : ℝ) (hr : 1 < r ∧ r < 2) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ s : ℝ, |s-r| < τ →
      (1 ≤ s ∧ s ≤ 2) ∧ ∀ b : Bool, τ ≤ frequency s b := by
  let τ := min (r-1) (2-r)/2
  have hτ : 0 < τ := by dsimp [τ]; exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have ha : 2*τ ≤ r-1 := by dsimp [τ]; have := min_le_left (r-1) (2-r); linarith
  have hb : 2*τ ≤ 2-r := by dsimp [τ]; have := min_le_right (r-1) (2-r); linarith
  refine ⟨τ,hτ,?_⟩
  intro s hs
  have h := abs_lt.mp hs
  refine ⟨⟨by linarith,by linarith⟩,?_⟩
  intro b
  cases b <;> simp only [frequency,Bool.false_eq_true,ite_false,ite_true] <;> linarith

theorem exists_binary_padding (τ : ℝ) (hτ : 0 < τ) : ∃ C : ℕ, 4 < (C : ℝ)*τ := by
  obtain ⟨C,hC⟩ := exists_nat_gt (4/τ)
  exact ⟨C,(div_lt_iff₀ hτ).mp hC⟩

end KroneckerBinarySlopeMargin
end

/- Original module: KroneckerBinaryNeighborhoodBudget -/
section
/-! Shrink one neighborhood to enforce binary legality, frequency margins and the terminal block budget. -/
set_option autoImplicit false
namespace KroneckerBinaryNeighborhoodBudget
open KroneckerBinarySlopeMargin KroneckerMechanicalLetterBounds

theorem binary_neighborhood_budget (r τ d : ℝ) (C L : ℕ) (hτ : 0 < τ) (hd : 0 < d)
    (hmargin : ∀ s : ℝ, |s-r| < τ → (1 ≤ s ∧ s ≤ 2) ∧ ∀ b : Bool, τ ≤ frequency s b)
    (hC : 4 < (C : ℝ)*τ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ, |s-r| < δ → |t-r| < δ →
      |s-r| < d ∧ |t-r| < d ∧ (1 ≤ s ∧ s ≤ 2) ∧ (1 ≤ t ∧ t ≤ 2) ∧
      (∀ b : Bool, τ ≤ frequency t b) ∧
      3+(L : ℝ)*|s-t| ≤ (C : ℝ)*τ := by
  let δ := min d (min τ (1/(4*((L : ℝ)+1))))
  have hδ : 0 < δ := lt_min hd (lt_min hτ (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro s t hs ht
  have hsd := hs.trans_le (min_le_left _ _)
  have htd := ht.trans_le (min_le_left _ _)
  have hsτ : |s-r| < τ := hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htτ : |t-r| < τ := ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : |s-t| < 1/(2*((L : ℝ)+1)) := by
    have hs' := hs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have ht' := ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have htri : |s-t| ≤ |s-r|+|t-r| := by
      simpa [abs_sub_comm t r] using abs_sub_le s r t
    have heq : 1/(2*((L : ℝ)+1))=2*(1/(4*((L : ℝ)+1))) := by
      field_simp
      norm_num
    rw [heq]
    linarith
  have hmul := (lt_div_iff₀ (by positivity : (0 : ℝ)<2*((L : ℝ)+1))).mp hsmall
  have habs := abs_nonneg (s-t)
  refine ⟨hsd,htd,(hmargin s hsτ).1,(hmargin t htτ).1,(hmargin t htτ).2,?_⟩
  nlinarith

end KroneckerBinaryNeighborhoodBudget
end

/- Original module: KroneckerBinaryQuotientBudget -/
section
/-! A blockwise rate bound scales to every finite prefix without denominator loss. -/
set_option autoImplicit false
namespace KroneckerBinaryQuotientBudget

theorem quotient_rate_budget (n L D : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hD : (D : ℝ) ≤ η*(L : ℝ)) :
    (((n/L)*D : ℕ) : ℝ) ≤ η*(n : ℝ) := by
  have hdiv := Nat.div_mul_le_self n L
  have hdivR : ((n/L : ℕ) : ℝ)*(L : ℝ) ≤ n := by exact_mod_cast hdiv
  have h1 := mul_le_mul_of_nonneg_left hD (show (0 : ℝ) ≤ (n/L : ℕ) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hdivR hη
  push_cast
  nlinarith

theorem binary_affine_budgets (n L Q C D K k T : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hQ : ((Q+C : ℕ) : ℝ) ≤ η*(L : ℝ)) (hD : (D : ℝ) ≤ η*(L : ℝ))
    (hT : T=n+1+K) (hK : K ≤ (n/L)*(Q+C)+C) (hk : k ≤ (n/L)*D+(L+C)^2) :
    (T : ℝ) ≤ (1+η)*((n+1 : ℕ) : ℝ)+C ∧
      (k : ℝ) ≤ η*((n+1 : ℕ) : ℝ)+((L+C)^2 : ℕ) := by
  have h1 := quotient_rate_budget n L (Q+C) η hη hQ
  have h2 := quotient_rate_budget n L D η hη hD
  have hKR : (K : ℝ) ≤ (((n/L)*(Q+C)+C : ℕ) : ℝ) := by exact_mod_cast hK
  have hkR : (k : ℝ) ≤ (((n/L)*D+(L+C)^2 : ℕ) : ℝ) := by exact_mod_cast hk
  have hTR : (T : ℝ)=((n+1+K : ℕ) : ℝ) := by exact_mod_cast hT
  push_cast at h1 h2 hKR hkR hTR ⊢
  constructor <;> nlinarith

end KroneckerBinaryQuotientBudget
end

/- Original module: KroneckerBinarySmallCoefficients -/
section
/-! Choose the period and block length so both binary insertion and exchange rates are small. -/
set_option autoImplicit false
namespace KroneckerBinarySmallCoefficients
open KroneckerSmallBlockCoefficients

theorem binary_small_coefficients (η : ℝ) (hη : 0 < η) :
    ∃ q : ℕ, 0 < q ∧ ∀ Q C : ℕ, ∃ L : ℕ, 0 < L ∧
      ((Q+C : ℕ) : ℝ) ≤ η*(L : ℝ) ∧
      ((L/q+1+C^2 : ℕ) : ℝ) ≤ η*(L : ℝ) := by
  obtain ⟨q,hq,h⟩ := small_block_coefficients η hη
  refine ⟨q,hq,?_⟩
  intro Q C
  obtain ⟨L,hL,hQ,hD⟩ := h (Q+C+C^2)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have ha := (div_lt_iff₀ hLR).mp hQ
  have hb := (div_lt_iff₀ hLR).mp hD
  push_cast at ha hb
  refine ⟨L,hL,?_,?_⟩ <;> push_cast <;> nlinarith [sq_nonneg (C : ℝ)]

end KroneckerBinarySmallCoefficients
end

/- Original module: KroneckerBinaryTailInsertions -/
section
/-! Fill any remaining mechanical target tail by complete-run insertions alone. -/
set_option autoImplicit false
namespace KroneckerBinaryTailInsertions
open KroneckerRawBinaryEdits KroneckerRawBinaryConcatenation KroneckerRawBinaryContext
open KroneckerBinaryPrefixInsertions KroneckerMechanicalWords KroneckerMechanicalWordSums

noncomputable def appendBinary (R A : List ℕ) (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ 2) :
    RawBinary R (R++A) A.length 0 := by
  have p := contextRawBinary (prependBinary [] A hA) R []
  simpa using p

theorem fill_mechanical_tail {R : List ℕ} {K k T N : ℕ} (t v : ℝ)
    (p : RawBinary R (mechanicalWord t v 0 T) K k) (ht : 1 ≤ t ∧ t ≤ 2) (hTN : T ≤ N) :
    Nonempty (RawBinary R (mechanicalWord t v 0 N) (K+(N-T)) k) := by
  have q := appendBinary (mechanicalWord t v 0 T) (mechanicalWord t v T (N-T))
    (mechanicalWord_legal t v T (N-T) 2 ht.1 ht.2)
  have h := appendRawBinary p q
  have hw : mechanicalWord t v 0 T++mechanicalWord t v T (N-T)=mechanicalWord t v 0 N := by
    simpa only [Nat.zero_add,Nat.add_sub_of_le hTN] using (mechanicalWord_append t v 0 T (N-T)).symm
  simpa only [hw,mechanicalWord_length,Nat.add_zero] using (show Nonempty _ from ⟨h⟩)

end KroneckerBinaryTailInsertions
end

/- Original module: KroneckerGreedyBinaryBlocks -/
section
/-! Greedily concatenate actual binary block comparisons, retaining all insertion and exchange counts. -/
set_option autoImplicit false
namespace KroneckerGreedyBinaryBlocks
open KroneckerRawBinaryEdits KroneckerRawBinaryContext KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem greedy_binary_blocks (s t u v : ℝ) (L Q C D : ℕ)
    (hmatch : ∀ i a : ℕ, ∃ j < Q, ∃ k,
      Nonempty (RawBinary (mechanicalWord s u i L) (mechanicalWord t v a (j+L+C)) (j+C) k) ∧ k ≤ D)
    (a : ℕ) :
    ∃ T K k, Nonempty (RawBinary (mechanicalWord s u 0 (a*L)) (mechanicalWord t v 0 T) K k) ∧
      T=a*L+K ∧ K ≤ a*(Q+C) ∧ k ≤ a*D := by
  induction a with
  | zero =>
    refine ⟨0,0,0,?_,by simp,by simp,by simp⟩
    simpa [mechanicalWord] using (show Nonempty (RawBinary [] [] 0 0) from ⟨.nil⟩)
  | succ a ih =>
    obtain ⟨T,K,k,⟨p⟩,hT,hK,hk⟩ := ih
    obtain ⟨j,hj,h,⟨q⟩,hh⟩ := hmatch (a*L) T
    have hp := concatenateRawBinary p q
    have hsource : mechanicalWord s u 0 (a*L)++mechanicalWord s u (a*L) L=
        mechanicalWord s u 0 ((a+1)*L) := by
      simpa only [Nat.zero_add,Nat.succ_mul] using (mechanicalWord_append s u 0 (a*L) L).symm
    have htarget : mechanicalWord t v 0 T++mechanicalWord t v T (j+L+C)=
        mechanicalWord t v 0 (T+(j+L+C)) := by
      simpa only [Nat.zero_add] using (mechanicalWord_append t v 0 T (j+L+C)).symm
    rw [hsource,htarget] at hp
    refine ⟨T+(j+L+C),K+(j+C),k+h,⟨hp⟩,?_,?_,?_⟩
    · simp only [Nat.succ_mul]; omega
    · simp only [Nat.succ_mul]; omega
    · simp only [Nat.succ_mul]; omega

end KroneckerGreedyBinaryBlocks
end

/- Original module: KroneckerBinaryTerminalAssembly -/
section
/-! Concatenate all ordinary block programs with one exceptional terminal block. -/
set_option autoImplicit false
namespace KroneckerBinaryTerminalAssembly
open KroneckerGreedyBinaryBlocks KroneckerRawBinaryContext KroneckerRawBinaryEdits
open KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem binary_blocks_terminal (s t u v : ℝ) (L Q C D a n : ℕ) (b : Bool)
    (hmatch : ∀ i T : ℕ, ∃ j < Q, ∃ k,
      Nonempty (RawBinary (mechanicalWord s u i L) (mechanicalWord t v T (j+L+C)) (j+C) k) ∧ k ≤ D)
    (hterminal : ∀ T : ℕ, ∃ k,
      Nonempty (RawBinary (mechanicalWord s u (a*L) n++[if b then 2 else 1])
        (mechanicalWord t v T (n+1+C)) C k) ∧ k ≤ (n+1+C)^2) :
    ∃ T K k, Nonempty (RawBinary (mechanicalWord s u 0 (a*L+n)++[if b then 2 else 1])
      (mechanicalWord t v 0 T) K k) ∧
      T=a*L+n+1+K ∧ K ≤ a*(Q+C)+C ∧ k ≤ a*D+(n+1+C)^2 := by
  obtain ⟨T,K,k,⟨p⟩,hT,hK,hk⟩ := greedy_binary_blocks s t u v L Q C D hmatch a
  obtain ⟨h,⟨q⟩,hh⟩ := hterminal T
  have hp := concatenateRawBinary p q
  have hs : mechanicalWord s u 0 (a*L)++(mechanicalWord s u (a*L) n++[if b then 2 else 1])=
      mechanicalWord s u 0 (a*L+n)++[if b then 2 else 1] := by
    rw [← List.append_assoc]
    congr 1
    simpa only [Nat.zero_add] using (mechanicalWord_append s u 0 (a*L) n).symm
  have ht : mechanicalWord t v 0 T++mechanicalWord t v T (n+1+C)=
      mechanicalWord t v 0 (T+(n+1+C)) := by
    simpa only [Nat.zero_add] using (mechanicalWord_append t v 0 T (n+1+C)).symm
  rw [hs,ht] at hp
  exact ⟨T+(n+1+C),K+C,k+h,⟨hp⟩,by omega,by omega,by omega⟩

end KroneckerBinaryTerminalAssembly
end

/- Original module: KroneckerShiftedBinaryBlock -/
section
/-! The uniform local binary comparison applies at arbitrary source and target indices. -/
set_option autoImplicit false
namespace KroneckerShiftedBinaryBlock
open KroneckerUniformBinaryPrefixBlock KroneckerMechanicalLetterBounds KroneckerNormalizedWindow
open KroneckerMechanicalWords KroneckerRawBinaryEdits

theorem shifted_binary_block (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ s t τ e : ℝ, |s-r| < δ → |t-r| < δ →
      (1 ≤ s ∧ s ≤ 2) → (1 ≤ t ∧ t ≤ 2) →
      (∀ b : Bool, τ ≤ frequency t b) → |s-t| ≤ e →
      ∀ u v : ℝ, ∀ i a n : ℕ, n ≤ L → ∀ C : ℕ, 2+(n : ℝ)*e ≤ (C : ℝ)*τ →
      ∃ j < Q, ∃ k, Nonempty (RawBinary (mechanicalWord s u i n)
        (mechanicalWord t v a (j+n+C)) (j+C) k) ∧ k ≤ n/q+1+C^2 := by
  obtain ⟨Q,hQ,hall⟩ := uniform_binary_prefix_block r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L
  obtain ⟨δ,hδ,h⟩ := hall L
  refine ⟨δ,hδ,?_⟩
  intro s t τ e hs ht hsb htb hm he u v i a n hn C hb
  obtain ⟨j,hj,k,hp,hk⟩ := h s t (Int.fract (u+(i : ℝ)*s))
    (Int.fract (v+(a : ℝ)*t)) τ e hs ht hsb htb
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ hm he n hn C hb
  refine ⟨j,hj,k,?_,hk⟩
  simpa only [← normalized_window] using hp

end KroneckerShiftedBinaryBlock
end

/- Original module: KroneckerBinaryWholeWord -/
section
/-! A whole mechanical prefix plus an exceptional final bit admits an actual uniformly bounded edit program. -/
set_option autoImplicit false
namespace KroneckerBinaryWholeWord
open KroneckerShiftedBinaryBlock KroneckerShiftedBinaryTerminal KroneckerBinaryTerminalAssembly
open KroneckerMechanicalWords KroneckerMechanicalLetterBounds KroneckerRawBinaryEdits

theorem binary_whole_word (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, 0 < L → ∃ δ : ℝ, 0 < δ ∧
      ∀ s t τ e : ℝ, |s-r| < δ → |t-r| < δ →
      (1 ≤ s ∧ s ≤ 2) → (1 ≤ t ∧ t ≤ 2) →
      (∀ b : Bool, τ ≤ frequency t b) → |s-t| ≤ e →
      ∀ C : ℕ, 3+(L : ℝ)*e ≤ (C : ℝ)*τ → ∀ u v : ℝ, ∀ n : ℕ, ∀ b : Bool,
      ∃ T K k, Nonempty (RawBinary (mechanicalWord s u 0 n++[if b then 2 else 1])
        (mechanicalWord t v 0 T) K k) ∧ T=n+1+K ∧
        K ≤ (n/L)*(Q+C)+C ∧ k ≤ (n/L)*(L/q+1+C^2)+(L+C)^2 := by
  obtain ⟨Q,hQ,hall⟩ := shifted_binary_block r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L hL
  obtain ⟨δ,hδ,h⟩ := hall L
  refine ⟨δ,hδ,?_⟩
  intro s t τ e hs ht hsb htb hm he C hbudget u v n b
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have hrem : n%L+1 ≤ L := by have := Nat.mod_lt n hL; omega
  have hremR : ((n%L+1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hrem
  have hterm : 3+((n%L+1 : ℕ) : ℝ)*e ≤ (C : ℝ)*τ := by
    have hh := mul_le_mul_of_nonneg_right hremR he0
    linarith
  have hmch : ∀ i T : ℕ, ∃ j < Q, ∃ k,
      Nonempty (RawBinary (mechanicalWord s u i L) (mechanicalWord t v T (j+L+C)) (j+C) k) ∧
        k ≤ L/q+1+C^2 := by
    intro i T
    exact h s t τ e hs ht hsb htb hm he u v i T L le_rfl C (by linarith)
  have hterminal : ∀ T : ℕ, ∃ k,
      Nonempty (RawBinary (mechanicalWord s u ((n/L)*L) (n%L)++[if b then 2 else 1])
        (mechanicalWord t v T (n%L+1+C)) C k) ∧ k ≤ (n%L+1+C)^2 := by
    intro T
    exact shifted_terminal_edits s u t v τ e ((n/L)*L) T (n%L) C b hsb htb hm he hterm
  obtain ⟨T,K,k,hp,hT,hK,hk⟩ := binary_blocks_terminal s t u v L Q C (L/q+1+C^2)
    (n/L) (n%L) b hmch hterminal
  have hn : (n/L)*L+n%L=n := by have := Nat.div_add_mod n L; nlinarith
  rw [hn] at hp hT
  refine ⟨T,K,k,hp,hT,hK,?_⟩
  have hsquare : (n%L+1+C)^2 ≤ (L+C)^2 := Nat.pow_le_pow_left (by omega) 2
  omega

end KroneckerBinaryWholeWord
end

/- Original module: KroneckerBinaryMechanicalExceptional -/
section
/-! Uniform full-length binary mechanical comparison, including one arbitrary binary final run. -/
set_option autoImplicit false
namespace KroneckerBinaryMechanicalExceptional
open KroneckerBinaryWholeWord KroneckerBinarySlopeMargin KroneckerBinarySmallCoefficients
open KroneckerBinaryNeighborhoodBudget KroneckerBinaryQuotientBudget KroneckerBinaryTailInsertions
open KroneckerMechanicalWords KroneckerRawBinaryEdits

theorem binary_mechanical_exceptional (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ n : ℕ, ∀ b : Bool, ∀ N : ℕ,
      (1+η)*((n+1 : ℕ) : ℝ)+(B : ℝ) ≤ N →
      ∃ k, Nonempty (RawBinary (mechanicalWord s u 0 n++[if b then 2 else 1])
        (mechanicalWord t v 0 N) (N-(n+1)) k) ∧ (k : ℝ) ≤ η*((n+1 : ℕ) : ℝ)+B := by
  obtain ⟨τ,hτ,hmargin⟩ := binary_slope_margin r hrb
  obtain ⟨C,hC⟩ := exists_binary_padding τ hτ
  obtain ⟨q,hq,hcoeff⟩ := binary_small_coefficients η hη
  obtain ⟨Q,hQ,hall⟩ := binary_whole_word r hr q hq
  obtain ⟨L,hL,hQrate,hDrate⟩ := hcoeff Q C
  obtain ⟨d,hd,h⟩ := hall L hL
  obtain ⟨δ,hδ,hnear⟩ := binary_neighborhood_budget r τ d C L hτ hd hmargin hC
  let B := C+(L+C)^2+1
  refine ⟨δ,hδ,B,by dsimp [B]; omega,?_⟩
  intro s t hs ht u v n b N hN
  obtain ⟨hsd,htd,hsb,htb,hm,hbudget⟩ := hnear s t hs ht
  obtain ⟨T,K,k,⟨p⟩,hT,hK,hk⟩ := h s t τ |s-t| hsd htd hsb htb hm le_rfl C hbudget u v n b
  have hbud := binary_affine_budgets n L Q C (L/q+1+C^2) K k T η hη.le hQrate hDrate hT hK hk
  have hBC : (C : ℝ) ≤ B := by exact_mod_cast (show C ≤ B by dsimp [B]; omega)
  have hBD : (((L+C)^2 : ℕ) : ℝ) ≤ B := by exact_mod_cast (show (L+C)^2 ≤ B by dsimp [B]; omega)
  have hTN : T ≤ N := by
    have hreal : (T : ℝ) ≤ N := by linarith [hbud.1]
    exact_mod_cast hreal
  have hp := fill_mechanical_tail t v p htb hTN
  have hcount : K+(N-T)=N-(n+1) := by omega
  rw [hcount] at hp
  exact ⟨k,hp,by linarith [hbud.2]⟩

end KroneckerBinaryMechanicalExceptional
end

/- Original module: KroneckerBinaryMechanicalNatural -/
section
/-! State the exceptional-run comparison directly for natural run types one and two. -/
set_option autoImplicit false
namespace KroneckerBinaryMechanicalNatural
open KroneckerBinaryMechanicalExceptional KroneckerBinaryLastRun KroneckerMechanicalWords KroneckerRawBinaryEdits

theorem binary_mechanical_natural (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ n z N : ℕ,
      (1 ≤ z ∧ z ≤ 2) → (1+η)*((n+1 : ℕ) : ℝ)+(B : ℝ) ≤ N →
      ∃ k, Nonempty (RawBinary (mechanicalWord s u 0 n++[z])
        (mechanicalWord t v 0 N) (N-(n+1)) k) ∧ (k : ℝ) ≤ η*((n+1 : ℕ) : ℝ)+B := by
  obtain ⟨δ,hδ,B,hB,h⟩ := binary_mechanical_exceptional r η hr hrb hη
  refine ⟨δ,hδ,B,hB,?_⟩
  intro s t hs ht u v n z N hz hN
  obtain ⟨b,rfl⟩ := binary_run_as_bit z hz
  exact h s t hs ht u v n b N hN

end KroneckerBinaryMechanicalNatural
end

/- Original module: KroneckerBinaryMechanicalOrdinary -/
section
/-! The same uniform comparison holds for ordinary mechanical words, including the empty word. -/
set_option autoImplicit false
namespace KroneckerBinaryMechanicalOrdinary
open KroneckerBinaryMechanicalExceptional KroneckerBinaryLastRun KroneckerBinarySlopeMargin
open KroneckerMechanicalWords KroneckerBinaryPrefixInsertions KroneckerRawBinaryEdits

theorem binary_mechanical_ordinary (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ l N : ℕ,
      (1+η)*(l : ℝ)+(B : ℝ) ≤ N →
      ∃ k, Nonempty (RawBinary (mechanicalWord s u 0 l)
        (mechanicalWord t v 0 N) (N-l) k) ∧ (k : ℝ) ≤ η*(l : ℝ)+B := by
  obtain ⟨δ,hδ,B,hB,h⟩ := binary_mechanical_exceptional r η hr hrb hη
  obtain ⟨τ,hτ,hm⟩ := binary_slope_margin r hrb
  refine ⟨min δ τ,lt_min hδ hτ,B,hB,?_⟩
  intro s t hs ht u v l N hN
  have hsb := (hm s (hs.trans_le (min_le_right _ _))).1
  have htb := (hm t (ht.trans_le (min_le_right _ _))).1
  cases l with
  | zero =>
    have p := prependBinary [] (mechanicalWord t v 0 N) (mechanicalWord_legal t v 0 N 2 htb.1 htb.2)
    refine ⟨0,?_,by simp⟩
    simpa [mechanicalWord_length,mechanicalWord] using (show Nonempty _ from ⟨p⟩)
  | succ n =>
    obtain ⟨b,hword⟩ := mechanical_last_binary s u n hsb
    obtain ⟨k,hp,hk⟩ := h s t (hs.trans_le (min_le_left _ _)) (ht.trans_le (min_le_left _ _))
      u v n b N hN
    rw [← hword] at hp
    exact ⟨k,hp,hk⟩

end KroneckerBinaryMechanicalOrdinary
end

/- Original module: KroneckerBinaryMechanicalSource -/
section
/-! Exact source domain for the binary mechanical lemma, with at most one exceptional final run. -/
set_option autoImplicit false
namespace KroneckerBinaryMechanicalSource
open KroneckerMechanicalWords

def BinaryMechanicalSource (s u : ℝ) (l : ℕ) (R : List ℕ) : Prop :=
  R=mechanicalWord s u 0 l ∨ ∃ n z : ℕ, l=n+1 ∧ 1 ≤ z ∧ z ≤ 2 ∧ R=mechanicalWord s u 0 n++[z]

theorem binary_source_length {s u : ℝ} {l : ℕ} {R : List ℕ} (h : BinaryMechanicalSource s u l R) :
    R.length=l := by
  rcases h with rfl | ⟨n,z,hl,hz1,hz2,rfl⟩
  · exact mechanicalWord_length s u 0 l
  · simp only [List.length_append,mechanicalWord_length,List.length_singleton]
    omega

theorem binary_source_legal {s u : ℝ} {l : ℕ} {R : List ℕ}
    (h : BinaryMechanicalSource s u l R) (hs : 1 ≤ s ∧ s ≤ 2) :
    ∀ z ∈ R, 1 ≤ z ∧ z ≤ 2 := by
  rcases h with rfl | ⟨n,z,hl,hz1,hz2,rfl⟩
  · exact mechanicalWord_legal s u 0 l 2 hs.1 hs.2
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact mechanicalWord_legal s u 0 n 2 hs.1 hs.2 x hx
    · have he : x=z := by simpa using hx
      subst x
      exact ⟨hz1,hz2⟩

end KroneckerBinaryMechanicalSource
end

/- Original module: KroneckerBinaryMechanicalLemma -/
section
/-! The manuscript binary mechanical comparison, with a stronger eta*l+B exchange bound. -/
set_option autoImplicit false
namespace KroneckerBinaryMechanicalLemma
open KroneckerBinaryMechanicalSource KroneckerBinaryMechanicalNatural KroneckerBinaryMechanicalOrdinary
open KroneckerMechanicalWords KroneckerRawBinaryEdits

theorem binary_mechanical_lemma (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ l N : ℕ, ∀ R : List ℕ,
      BinaryMechanicalSource s u l R → (1+η)*(l : ℝ)+(B : ℝ) ≤ N →
      ∃ k, Nonempty (RawBinary R (mechanicalWord t v 0 N) (N-l) k) ∧
        (k : ℝ) ≤ η*(l : ℝ)+B := by
  obtain ⟨d,hd,A,hA,hord⟩ := binary_mechanical_ordinary r η hr hrb hη
  obtain ⟨e,he,C,hC,hexc⟩ := binary_mechanical_natural r η hr hrb hη
  refine ⟨min d e,lt_min hd he,max A C,lt_of_lt_of_le hA (le_max_left _ _),?_⟩
  intro s t hs ht u v l N R hR hN
  have hAB : (A : ℝ) ≤ max A C := by exact_mod_cast (le_max_left A C)
  have hCB : (C : ℝ) ≤ max A C := by exact_mod_cast (le_max_right A C)
  rcases hR with rfl | ⟨n,z,rfl,hz1,hz2,rfl⟩
  · obtain ⟨k,hp,hk⟩ := hord s t (hs.trans_le (min_le_left _ _)) (ht.trans_le (min_le_left _ _))
      u v l N (by linarith)
    exact ⟨k,hp,by linarith⟩
  · obtain ⟨k,hp,hk⟩ := hexc s t (hs.trans_le (min_le_right _ _)) (ht.trans_le (min_le_right _ _))
      u v n z N ⟨hz1,hz2⟩ (by linarith)
    exact ⟨k,hp,by linarith⟩

theorem binary_mechanical_seven (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ l N : ℕ, ∀ R : List ℕ,
      BinaryMechanicalSource s u l R → (1+η)*(l : ℝ)+(B : ℝ) ≤ N →
      ∃ k, Nonempty (RawBinary R (mechanicalWord t v 0 N) (N-l) k) ∧
        (k : ℝ) ≤ 7*η*(l : ℝ)+B := by
  obtain ⟨δ,hδ,B,hB,h⟩ := binary_mechanical_lemma r η hr hrb hη
  refine ⟨δ,hδ,B,hB,?_⟩
  intro s t hs ht u v l N R hR hN
  obtain ⟨k,hp,hk⟩ := h s t hs ht u v l N R hR hN
  refine ⟨k,hp,?_⟩
  nlinarith [mul_nonneg hη.le (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]

end KroneckerBinaryMechanicalLemma
end
end

