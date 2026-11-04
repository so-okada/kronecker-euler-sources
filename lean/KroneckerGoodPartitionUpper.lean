import KroneckerNearbyShortFactor
import KroneckerSublistPrograms
import KroneckerAdjustRun
import KroneckerPeriodicCapIdentity
import KroneckerCompletionPadding
import KroneckerPeriodEndpoints
import KroneckerPiecesCompletion

section

/- Original module: KroneckerWindowSlide -/
section
/-! Consecutive equal window sums force equality of the exchanged runs. -/
set_option autoImplicit false
namespace KroneckerWindowSlide
open KroneckerMechanicalRuns KroneckerMechanicalWindows

theorem window_slide (s u : ℝ) (q i : ℕ) :
    windowSum s u q (i+1)-windowSum s u q i = mechanicalRun s u (i+q)-mechanicalRun s u i := by
  rw [windowSum, windowSum, mechanical_block_sum, mechanical_block_sum]
  unfold mechanicalRun
  rw [show i+1+q=i+q+1 by omega]
  ring

theorem equal_windows_periodic_step (s u : ℝ) (p : ℤ) (q i : ℕ)
    (h0 : windowSum s u q i = p) (h1 : windowSum s u q (i+1) = p) :
    mechanicalRun s u (i+q) = mechanicalRun s u i := by
  have h := window_slide s u q i
  rw [h0, h1] at h
  omega

end KroneckerWindowSlide
end

/- Original module: KroneckerGoodIntervals -/
section
/-! Constant full-window sums on a finite mechanical interval. -/
set_option autoImplicit false
namespace KroneckerGoodIntervals
open KroneckerMechanicalRuns KroneckerMechanicalWindows KroneckerWindowSlide

def GoodWindows (s u : ℝ) (p : ℤ) (q start n : ℕ) : Prop :=
  ∀ i, i+q ≤ n → windowSum s u q (start+i) = p


theorem goodWindows_periodic_step (s u : ℝ) (p : ℤ) (q start n i : ℕ)
    (hgood : GoodWindows s u p q start n) (hi : i+q < n) :
    mechanicalRun s u (start+i+q) = mechanicalRun s u (start+i) := by
  apply equal_windows_periodic_step s u p q (start+i)
  · exact hgood i (by omega)
  · simpa only [Nat.add_assoc] using hgood (i+1) (by omega)

end KroneckerGoodIntervals
end
end

section

/- Original module: KroneckerGoodRunPeriods -/
section
/-! Repeated period steps are valid throughout a finite interval of good windows. -/
set_option autoImplicit false
namespace KroneckerGoodRunPeriods
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerGoodIntervals

theorem good_run_multiple (s u : ℝ) (p : ℤ) (q start n i k : ℕ)
    (hgood : GoodWindows s u p q start n) (hbound : i+k*q < n) :
    mechanicalRun s u (start+(i+k*q)) = mechanicalRun s u (start+i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hb : i+k*q+q < n := by simpa only [Nat.succ_mul, Nat.add_assoc] using hbound
    have hstep := goodWindows_periodic_step s u p q start n (i+k*q) hgood hb
    have hk : i+k*q < n := by omega
    have hre : start+(i+(k+1)*q) = start+(i+k*q)+q := by rw [Nat.add_mul]; omega
    rw [hre, hstep, ih hk]

theorem good_natRun_multiple (s u : ℝ) (p : ℤ) (q start n i k : ℕ)
    (hgood : GoodWindows s u p q start n) (hbound : i+k*q < n) :
    natRun s u (start+(i+k*q)) = natRun s u (start+i) := by
  unfold natRun
  rw [good_run_multiple s u p q start n i k hgood hbound]

end KroneckerGoodRunPeriods
end

/- Original module: KroneckerGoodPeriodBlocks -/
section
/-! Every complete period block in a good interval equals its first period block. -/
set_option autoImplicit false
namespace KroneckerGoodPeriodBlocks
open KroneckerMechanicalWords KroneckerGoodIntervals KroneckerGoodRunPeriods

theorem good_period_block (s u : ℝ) (p : ℤ) (q start n k : ℕ)
    (hgood : GoodWindows s u p q start n) (hbound : (k+1)*q ≤ n) :
    mechanicalWord s u (start+k*q) q = mechanicalWord s u start q := by
  apply List.ext_getElem
  · simp only [mechanicalWord_length]
  · intro i hi hi'
    have hiq : i < q := by simpa only [mechanicalWord_length] using hi'
    simp only [mechanicalWord, List.getElem_ofFn]
    have hb : i+k*q < n := by nlinarith
    have heq : start+k*q+i = start+(i+k*q) := by omega
    rw [heq]
    exact good_natRun_multiple s u p q start n i k hgood hb

end KroneckerGoodPeriodBlocks
end

/- Original module: KroneckerGoodWordRepetition -/
section
/-! A good block of J*q runs is exactly J copies of its first q runs. -/
set_option autoImplicit false
namespace KroneckerGoodWordRepetition
open KroneckerMechanicalWords KroneckerMechanicalWordSums KroneckerPeriodicWords
open KroneckerGoodIntervals KroneckerGoodPeriodBlocks

theorem good_word_repetition (s u : ℝ) (p : ℤ) (q start J : ℕ)
    (hgood : GoodWindows s u p q start (J*q)) :
    mechanicalWord s u start (J*q) = repeatRuns (mechanicalWord s u start q) J := by
  induction J with
  | zero => simp [mechanicalWord, repeatRuns]
  | succ J ih =>
    have hsub : GoodWindows s u p q start (J*q) := by
      intro i hi
      exact hgood i (by nlinarith)
    have hlen : (J+1)*q = J*q+q := by ring
    rw [hlen, mechanicalWord_append, good_period_block s u p q start ((J+1)*q) J hgood le_rfl,
      ih hsub]
    rfl

end KroneckerGoodWordRepetition
end
end

section

/- Original module: KroneckerGoodWordRemainder -/
section
/-! A good interval consists of full copies of its first period and a literal remainder. -/
set_option autoImplicit false
namespace KroneckerGoodWordRemainder
open KroneckerMechanicalWords KroneckerMechanicalWordSums KroneckerMechanicalSlices
open KroneckerGoodIntervals KroneckerGoodRunPeriods KroneckerGoodWordRepetition KroneckerPeriodicWords

theorem good_word_tail (s u : ℝ) (p : ℤ) (q start n k r : ℕ)
    (hgood : GoodWindows s u p q start n) (hbound : k*q+r ≤ n) :
    mechanicalWord s u (start+k*q) r=mechanicalWord s u start r := by
  apply List.ext_getElem
  · simp only [mechanicalWord_length]
  · intro i hi hi'
    have hir : i < r := by simpa only [mechanicalWord_length] using hi'
    simp only [mechanicalWord,List.getElem_ofFn]
    rw [show start+k*q+i=start+(i+k*q) by omega]
    exact good_natRun_multiple s u p q start n i k hgood (by omega)

theorem good_word_remainder (s u : ℝ) (p : ℤ) (q start n : ℕ) (hq : 0 < q)
    (hgood : GoodWindows s u p q start n) :
    mechanicalWord s u start n = repeatRuns (mechanicalWord s u start q) (n/q) ++
      (mechanicalWord s u start q).take (n%q) := by
  have hdecomp : n/q*q+n%q=n := Nat.div_add_mod' n q
  have hbound : n/q*q ≤ n := Nat.div_mul_le_self n q
  have hsub : GoodWindows s u p q start (n/q*q) := fun i hi => hgood i (hi.trans hbound)
  have htake : (mechanicalWord s u start q).take (n%q)=mechanicalWord s u start (n%q) := by
    simpa using mechanicalWord_slice s u start q 0 (n%q) (by have h := Nat.mod_lt n hq; omega)
  conv_lhs => rw [←hdecomp,mechanicalWord_append]
  rw [good_word_repetition s u p q start (n/q) hsub,
    good_word_tail s u p q start n (n/q) (n%q) hgood hdecomp.le,htake]

end KroneckerGoodWordRemainder
end

/- Original module: KroneckerShortPhasePiece -/
section
/-! The previously proved short-factor classification supplies literal periodic pieces. -/
set_option autoImplicit false
namespace KroneckerShortPhasePiece
open KroneckerMechanicalWords KroneckerPeriodicWords KroneckerPhasePieces
open KroneckerRationalWordRotation KroneckerNearbyShortFactor

theorem short_phase_piece (p q : ℕ) (hq : 1 < q) (hc : p.Coprime q)
    (s u : ℝ) (start n : ℕ) (hn : n < q)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    PhasePiece (rationalPeriod p q) (mechanicalWord s u start n) := by
  obtain ⟨j,hj,heq⟩ := nearby_short_factor p q hq hc s u start n hn hs
  refine ⟨j,0,n,?_,?_,?_⟩
  · simpa only [rationalPeriod_length] using hj.le
  · simpa only [rationalPeriod_length] using hn
  · simpa only [repeatRuns,List.nil_append] using heq

end KroneckerShortPhasePiece
end

/- Original module: KroneckerGoodIntervalPhasePiece -/
section
/-! Every nearby-rational interval without bad full windows is an exact periodic piece. -/
set_option autoImplicit false
namespace KroneckerGoodIntervalPhasePiece
open KroneckerMechanicalWords KroneckerGoodIntervals KroneckerGoodWordRemainder
open KroneckerShortPhasePiece KroneckerNearbyRationalPhase KroneckerRationalWordRotation
open KroneckerPhasePieces

theorem good_interval_phase_piece (p q : ℕ) (hq : 1 < q) (hc : p.Coprime q)
    (s u : ℝ) (start n : ℕ) (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2)
    (hgood : GoodWindows s u (p : ℤ) q start n) :
    PhasePiece (rationalPeriod p q) (mechanicalWord s u start n) := by
  by_cases hn : n < q
  · exact short_phase_piece p q hq hc s u start n hn hs
  · have hfirst : KroneckerMechanicalWindows.windowSum s u q start=(p : ℤ) := by
      simpa using hgood 0 (by omega)
    obtain ⟨j,hj,hword⟩ := nearby_good_window_rotation p q hq hc s u start hs hfirst
    refine ⟨j,n/q,n%q,?_,?_,?_⟩
    · simpa only [rationalPeriod_length] using hj.le
    · simpa only [rationalPeriod_length] using Nat.mod_lt n (show 0 < q by omega)
    · rw [good_word_remainder s u (p : ℤ) q start n (by omega) hgood,hword]

end KroneckerGoodIntervalPhasePiece
end
end

section

/- Original module: KroneckerSurroundPrograms -/
section
/-! Insert prescribed legal prefix and suffix runs without editing the old runs. -/
set_option autoImplicit false
namespace KroneckerSurroundPrograms
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerSublistPrograms


end KroneckerSurroundPrograms
end

/- Original module: KroneckerTerminalMarker -/
section
/-! Raise the terminal unit run to the first run of the target period. -/
set_option autoImplicit false
namespace KroneckerTerminalMarker
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerAdjustRun


end KroneckerTerminalMarker
end

/- Original module: KroneckerPeriodicCapProgram -/
section
/-! Complete a frame prefix and repair its terminal marker, with exact edit costs. -/
set_option autoImplicit false
namespace KroneckerPeriodicCapProgram
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRawConcatenation
open KroneckerSublistPrograms KroneckerSurroundPrograms KroneckerTerminalMarker KroneckerPeriodicWords


end KroneckerPeriodicCapProgram
end

/- Original module: KroneckerSplitPeriodicUpper -/
section
/-! The complete-run construction yields an actual finite periodic upper bound. -/
set_option autoImplicit false
namespace KroneckerSplitPeriodicUpper
open KroneckerWordCounts KroneckerPeriodicWords KroneckerPeriodicCapProgram
open KroneckerPeriodicCapIdentity KroneckerCompletionPadding KroneckerPrescribedMixedRuns


end KroneckerSplitPeriodicUpper
end

/- Original module: KroneckerPeriodicCompletionUpper -/
section
/-! Periodic domination from an explicit subsequence completion, with no map premise. -/
set_option autoImplicit false
namespace KroneckerPeriodicCompletionUpper
open KroneckerWordCounts KroneckerPeriodicWords KroneckerCompletionPadding
open KroneckerSplitPeriodicUpper KroneckerPeriodEndpoints


end KroneckerPeriodicCompletionUpper
end

/- Original module: KroneckerPiecesFiniteUpper -/
section
/-! The number of periodic pieces explicitly bounds the finite count comparison length. -/
set_option autoImplicit false
namespace KroneckerPiecesFiniteUpper
open KroneckerWordCounts KroneckerPeriodicWords KroneckerPhasePieces
open KroneckerPiecesCompletion KroneckerPeriodicCompletionUpper KroneckerCompletionPadding


end KroneckerPiecesFiniteUpper
end

/- Original module: KroneckerGoodPartitionUpper -/
section
/-! A literal partition into good intervals yields a count bound with explicit overhead. -/
set_option autoImplicit false
namespace KroneckerGoodPartitionUpper
open KroneckerMechanicalWords KroneckerGoodIntervals KroneckerGoodIntervalPhasePiece
open KroneckerPiecesFiniteUpper KroneckerRationalWordRotation KroneckerRationalPeriodAlphabet
open KroneckerWordCounts KroneckerPeriodicWords KroneckerCompletionPadding

def GoodPartition (s u : ℝ) (p : ℤ) (q start n : ℕ) (parts : List (ℕ×ℕ)) : Prop :=
  parts.flatMap (fun z => mechanicalWord s u z.1 z.2)=mechanicalWord s u start n ∧
    ∀ z ∈ parts, GoodWindows s u p q z.1 z.2


end KroneckerGoodPartitionUpper
end
end

