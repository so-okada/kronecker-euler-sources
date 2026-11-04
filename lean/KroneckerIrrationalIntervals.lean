import KroneckerIrrationalWordSubsequence
import KroneckerSmallBlockCoefficients
import KroneckerLowerScheduleBudget
import KroneckerEventualFrameData
import KroneckerMechanicalCollarIdentity
import KroneckerUpperScheduleBudget
import KroneckerFrameObservables

section

/-! First align retained runs, then complete their prescribed target subsequence. -/
set_option autoImplicit false
namespace KroneckerPairedSublistPrograms
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerRawConcatenation
open KroneckerPairedRunCosts KroneckerPairedRunPrograms KroneckerSublistPrograms

theorem paired_sublist_program (m : ℕ) (X Y Z : List ℕ) (hlen : X.length=Y.length)
    (hsub : Y.Sublist Z) (hZ : ∀ r ∈ Z,1 ≤ r ∧ r ≤ m-2) :
    Nonempty (RawProgram m (runWord X) (runWord Z) (Z.length-X.length) (rises X Y) (falls X Y)) := by
  obtain ⟨p⟩ := paired_program m X Y [] hlen
  obtain ⟨q⟩ := sublist_program hsub hZ [] []
  simp only [List.nil_append,List.append_nil] at p q
  exact ⟨by simpa only [Nat.zero_add,Nat.add_zero,hlen] using appendRaw p q⟩

end KroneckerPairedSublistPrograms
end

section

/- Original module: KroneckerScaledPeriodicLimit -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerScaledPeriodicLimit
open KroneckerPeriodicWords KroneckerPeriodicLog KroneckerPeriodicTail KroneckerPeriodicLimit

theorem scaled_periodic_limit (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hlegal : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (a b : ℕ → ℕ)
    (ha : Tendsto a atTop atTop) (c : ℝ) (hc : 0 < c)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun n => Real.log (periodicCount m W (b n) : ℝ)/(a n : ℝ))
      atTop (𝓝 (c*periodicGrowth m W)) := by
  have hb := KroneckerPositiveDensity.positive_density_atTop a b ha c hc hr
  have h := hr.mul ((periodicLog_limit m hm W hne hlegal).comp hb)
  apply h.congr'
  filter_upwards [hb.eventually (eventually_ge_atTop 1)] with n hn
  have hbR : (b n : ℝ) ≠ 0 := by exact_mod_cast (show b n ≠ 0 by omega)
  dsimp [Function.comp_def,periodicLog]
  field_simp

end KroneckerScaledPeriodicLimit
end

/- Original module: KroneckerRoundedPeriodicLog -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerRoundedPeriodicLog
open KroneckerPeriodicRounding KroneckerPeriodicWords KroneckerPeriodicTail
open KroneckerMechanicalWords KroneckerWordCounts

theorem upper_rounded_periodic_log (m : ℕ) (hm : 3 ≤ m) (t v : ℝ)
    (p : ℤ) (q : ℕ) (hq : 0 < q) (hp : (q : ℝ)*t=p)
    (ht : 1 ≤ t) (htM : t ≤ (m-1 : ℕ))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n => Real.log (runCount m
      (mechanicalWord t v 0 (upperPeriods q c (a n)*q)) 0 : ℝ)/(a n : ℝ)) atTop
      (𝓝 (c*(periodicGrowth m (mechanicalWord t v 0 q)/(q : ℝ)))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : mechanicalWord t v 0 q ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [mechanicalWord_length,List.length_nil] at hh
    omega
  have h := KroneckerScaledPeriodicLimit.scaled_periodic_limit m hm (mechanicalWord t v 0 q) hne
    (mechanicalWord_legal t v 0 q (m-1) ht htM) a (fun n => upperPeriods q c (a n)) ha
    (c/(q : ℝ)) (by positivity) (KroneckerRoundedScaling.ceil_scaling a ha _ (by positivity))
  have he : c/(q : ℝ)*periodicGrowth m (mechanicalWord t v 0 q)=
      c*(periodicGrowth m (mechanicalWord t v 0 q)/(q : ℝ)) := by ring
  simpa only [periodicCount,← KroneckerRationalPeriodRepetition.mechanical_repetition_start t v p q 0 _ hp,he] using h

theorem lower_rounded_periodic_log (m : ℕ) (hm : 3 ≤ m) (t v : ℝ)
    (p : ℤ) (q : ℕ) (hq : 0 < q) (hp : (q : ℝ)*t=p)
    (ht : 1 ≤ t) (htM : t ≤ (m-1 : ℕ))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n => Real.log (runCount m
      (mechanicalWord t v 0 (lowerPeriods q c (a n)*q)) 0 : ℝ)/(a n : ℝ)) atTop
      (𝓝 (c*(periodicGrowth m (mechanicalWord t v 0 q)/(q : ℝ)))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : mechanicalWord t v 0 q ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [mechanicalWord_length,List.length_nil] at hh
    omega
  have h := KroneckerScaledPeriodicLimit.scaled_periodic_limit m hm (mechanicalWord t v 0 q) hne
    (mechanicalWord_legal t v 0 q (m-1) ht htM) a (fun n => lowerPeriods q c (a n)) ha
    (c/(q : ℝ)) (by positivity) (KroneckerRoundedScaling.floor_scaling a ha _ (by positivity))
  have he : c/(q : ℝ)*periodicGrowth m (mechanicalWord t v 0 q)=
      c*(periodicGrowth m (mechanicalWord t v 0 q)/(q : ℝ)) := by ring
  simpa only [periodicCount,← KroneckerRationalPeriodRepetition.mechanical_repetition_start t v p q 0 _ hp,he] using h

end KroneckerRoundedPeriodicLog
end
end

section

set_option autoImplicit false
namespace KroneckerRoundedAffineBudget
open KroneckerNaturalQuotientBound

theorem rounded_affine_budget (n L B : ℕ) (hL : 0 < L) :
    (((n/L+1)*B : ℕ) : ℝ) ≤ ((B : ℝ)/L)*(n : ℝ)+B := by
  have h := natural_quotient_bound n L hL
  have hmul := mul_le_mul_of_nonneg_right (add_le_add_right h 1) (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  push_cast at hmul ⊢
  convert hmul using 1 <;> ring

theorem rounded_length_budget (n L Q : ℕ) (hL : 0 < L) :
    (((n/L+1)*(L+Q) : ℕ) : ℝ) ≤ (1+(Q : ℝ)/L)*(n : ℝ)+(L+Q : ℕ) := by
  have h := rounded_affine_budget n L (L+Q) hL
  have he : ((L+Q : ℕ) : ℝ)/(L : ℝ) = 1+(Q : ℝ)/L := by
    push_cast
    rw [add_div, div_self (by exact_mod_cast (Nat.ne_of_gt hL))]
  rwa [he] at h

end KroneckerRoundedAffineBudget
end

section

/- Original module: KroneckerEventualAffineBudget -/
section
set_option autoImplicit false
namespace KroneckerEventualAffineBudget

theorem eventual_affine_budget (a C η : ℝ) (ha : a < η) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → a*(n : ℝ)+C ≤ η*(n : ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (C/(η-a)))
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNC : C/(η-a) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hC : C < (N : ℝ)*(η-a) := (div_lt_iff₀ (by linarith)).mp hNC
  refine ⟨N,by exact_mod_cast hN0,?_⟩
  intro n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

end KroneckerEventualAffineBudget
end

/- Original module: KroneckerEventualBlockBudgets -/
section
set_option autoImplicit false
namespace KroneckerEventualBlockBudgets
open KroneckerRoundedAffineBudget KroneckerEventualAffineBudget

theorem eventual_block_budgets (q Q L : ℕ) (hL : 0 < L) (η : ℝ)
    (hQ : (Q : ℝ)/L < η) (hB : ((2*(L/q+1) : ℕ) : ℝ)/L < η) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      (((n/L+1)*(L+Q) : ℕ) : ℝ) ≤ (1+η)*(n : ℝ) ∧
      (((n/L+1)*(2*(L/q+1)) : ℕ) : ℝ) ≤ η*(n : ℝ) := by
  obtain ⟨N,hN,hNbound⟩ := eventual_affine_budget ((Q : ℝ)/L) (L+Q : ℕ) η hQ
  obtain ⟨M,hM,hMbound⟩ := eventual_affine_budget (((2*(L/q+1) : ℕ) : ℝ)/L)
    (2*(L/q+1) : ℕ) η hB
  refine ⟨max N M,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro n hn
  constructor
  · have h := rounded_length_budget n L Q hL
    have h' := hNbound n (le_trans (le_max_left _ _) hn)
    nlinarith
  · exact (rounded_affine_budget n L (2*(L/q+1)) hL).trans
      (hMbound n (le_trans (le_max_right _ _) hn))

end KroneckerEventualBlockBudgets
end

/- Original module: KroneckerSparseMechanicalSubsequence -/
section
set_option autoImplicit false
namespace KroneckerSparseMechanicalSubsequence
open KroneckerIrrationalWordSubsequence KroneckerSmallBlockCoefficients KroneckerEventualBlockBudgets
open KroneckerMechanicalWords KroneckerPairedRunCosts

theorem sparse_mechanical_subsequence (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ s t : ℝ,
      0 ≤ s → 0 ≤ t → |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ n : ℕ, N ≤ n →
      ∃ T : ℕ, ∃ Y : List ℕ, n ≤ T ∧ (T : ℝ) ≤ (1+η)*(n : ℝ) ∧ Y.length = n ∧
        Y.Sublist (mechanicalWord t v 0 T) ∧ (cost (mechanicalWord s u 0 n) Y : ℝ) ≤ η*(n : ℝ) := by
  obtain ⟨q,hq,hcoeff⟩ := small_block_coefficients η hη
  obtain ⟨Q,_,hL⟩ := irrational_word_subsequence r hr q hq
  obtain ⟨L,hLpos,hQsmall,hBsmall⟩ := hcoeff Q
  obtain ⟨δ,hδ,h⟩ := hL L hLpos
  obtain ⟨N,hN,hbudget⟩ := eventual_block_budgets q Q L hLpos η
    (by linarith) (by linarith)
  refine ⟨δ,hδ,N,hN,?_⟩
  intro s t hs ht hsr htr u v n hn
  obtain ⟨T,Y,hlo,hhi,hlen,hsub,hc⟩ := h s t hs ht hsr htr u v n
  have hb := hbudget n hn
  have hT : (T : ℝ) ≤ (((n/L+1)*(L+Q) : ℕ) : ℝ) := by exact_mod_cast hhi
  have hC : (cost (mechanicalWord s u 0 n) Y : ℝ) ≤
      (((n/L+1)*(2*(L/q+1)) : ℕ) : ℝ) := by exact_mod_cast hc
  exact ⟨T,Y,hlo,hT.trans hb.1,hlen,hsub,hC.trans hb.2⟩

end KroneckerSparseMechanicalSubsequence
end
end

section

/- Original module: KroneckerExceptionalRunCost -/
section
/-! A prescribed exceptional terminal run incurs at most M-1 further vertical edits. -/
set_option autoImplicit false
namespace KroneckerExceptionalRunCost
open KroneckerPairedRunCosts KroneckerPairedCostsAppend

theorem singleton_cost_bound (r s M : ℕ) (hr : 1 ≤ r ∧ r ≤ M) (hs : 1 ≤ s ∧ s ≤ M) :
    cost [r] [s] ≤ M-1 := by
  simp only [cost,rises,falls,List.zipWith_cons_cons,List.zipWith_nil_left,List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

theorem exceptional_cost (X Y : List ℕ) (h : X.length=Y.length) (r s M : ℕ)
    (hr : 1 ≤ r ∧ r ≤ M) (hs : 1 ≤ s ∧ s ≤ M) :
    cost (X++[r]) (Y++[s]) ≤ cost X Y+(M-1) := by
  rw [cost_append X Y [r] [s] h]
  exact Nat.add_le_add_left (singleton_cost_bound r s M hr hs) _

end KroneckerExceptionalRunCost
end

/- Original module: KroneckerExceptionalSubsequence -/
section
set_option autoImplicit false
namespace KroneckerExceptionalSubsequence
open KroneckerExceptionalRunCost KroneckerMechanicalWords KroneckerMechanicalWordSums
open KroneckerPairedRunCosts

theorem exceptional_subsequence (X Y : List ℕ) (t v : ℝ) (T z M B : ℕ)
    (hlen : X.length = Y.length) (hsub : Y.Sublist (mechanicalWord t v 0 T))
    (hc : cost X Y ≤ B) (hz : 1 ≤ z ∧ z ≤ M) (ht : 1 ≤ t) (hM : t ≤ M) :
    ∃ Z : List ℕ, Z.length = X.length+1 ∧
      Z.Sublist (mechanicalWord t v 0 (T+1)) ∧ cost (X++[z]) Z ≤ B+(M-1) := by
  let w := natRun t v T
  refine ⟨Y++[w],?_,?_,?_⟩
  · simp [hlen]
  · rw [mechanicalWord_append,mechanicalWord_one]
    simp only [Nat.zero_add]
    exact hsub.append (List.Sublist.refl _)
  · exact (exceptional_cost X Y hlen z w M hz (natRun_legal t v T M ht hM)).trans
      (Nat.add_le_add_right hc _)

end KroneckerExceptionalSubsequence
end

/- Original module: KroneckerGlobalExceptionalSubsequence -/
section
set_option autoImplicit false
namespace KroneckerGlobalExceptionalSubsequence
open KroneckerIrrationalWordSubsequence KroneckerExceptionalSubsequence KroneckerMechanicalPrefixSublist
open KroneckerMechanicalWords KroneckerPairedRunCosts


end KroneckerGlobalExceptionalSubsequence
end

/- Original module: KroneckerGlobalExceptionalPrograms -/
section
set_option autoImplicit false
namespace KroneckerGlobalExceptionalPrograms
open KroneckerGlobalExceptionalSubsequence KroneckerPairedSublistPrograms
open KroneckerMechanicalWords KroneckerPairedRunCosts KroneckerRawMixedPrograms KroneckerWordCounts


end KroneckerGlobalExceptionalPrograms
end

/- Original module: KroneckerSparseExceptionalSubsequence -/
section
set_option autoImplicit false
namespace KroneckerSparseExceptionalSubsequence
open KroneckerSparseMechanicalSubsequence KroneckerExceptionalSubsequence KroneckerEventualAffineBudget
open KroneckerMechanicalWords KroneckerPairedRunCosts

theorem sparse_exceptional_subsequence (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η) (M : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ s t : ℝ,
      0 ≤ s → 1 ≤ t → t ≤ M → |s-r| < δ → |t-r| < δ →
      ∀ u v : ℝ, ∀ n z : ℕ, N ≤ n → (1 ≤ z ∧ z ≤ M) →
      ∃ T : ℕ, ∃ Y : List ℕ, n+1 ≤ T ∧ (T : ℝ) ≤ (1+η)*((n : ℝ)+1) ∧ Y.length = n+1 ∧
        Y.Sublist (mechanicalWord t v 0 T) ∧
        (cost (mechanicalWord s u 0 n ++ [z]) Y : ℝ) ≤ η*((n : ℝ)+1) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := sparse_mechanical_subsequence r hr (η/2) (by positivity)
  obtain ⟨K,_,hK⟩ := eventual_affine_budget (η/2) (M-1 : ℕ) η (by linarith)
  refine ⟨δ,hδ,max N K,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro s t hs ht htM hsr htr u v n z hn hz
  obtain ⟨T,Y,hlo,hhi,hlen,hsub,hc⟩ := h s t hs (by linarith) hsr htr u v n
    (le_trans (le_max_left _ _) hn)
  obtain ⟨Z,hZlen,hZsub,hZcost⟩ := exceptional_subsequence (mechanicalWord s u 0 n) Y t v T z M
    (cost (mechanicalWord s u 0 n) Y) (by rw [mechanicalWord_length,hlen]) hsub le_rfl hz ht htM
  refine ⟨T+1,Z,by omega,?_,by simpa only [mechanicalWord_length] using hZlen,hZsub,?_⟩
  · push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have hC : (cost (mechanicalWord s u 0 n ++ [z]) Z : ℝ) ≤
        (cost (mechanicalWord s u 0 n) Y : ℝ)+(M-1 : ℕ) := by exact_mod_cast hZcost
    have hbound := hK n (le_trans (le_max_right _ _) hn)
    nlinarith

end KroneckerSparseExceptionalSubsequence
end

/- Original module: KroneckerSparsePrescribedExceptional -/
section
set_option autoImplicit false
namespace KroneckerSparsePrescribedExceptional
open KroneckerSparseExceptionalSubsequence KroneckerMechanicalPrefixSublist KroneckerPairedSublistPrograms
open KroneckerMechanicalWords KroneckerPairedRunCosts KroneckerRawMixedPrograms KroneckerWordCounts

theorem sparse_prescribed_exceptional (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η) (m : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ s t : ℝ,
      0 ≤ s → 1 ≤ t → t ≤ (m-2 : ℕ) → |s-r| < δ → |t-r| < δ →
      ∀ u v : ℝ, ∀ n T z : ℕ, N ≤ n → (1 ≤ z ∧ z ≤ m-2) →
      (1+η)*((n : ℝ)+1) ≤ T → ∃ A D : ℕ, ((A+D : ℕ) : ℝ) ≤ η*((n : ℝ)+1) ∧
        Nonempty (RawProgram m (runWord (mechanicalWord s u 0 n ++ [z]))
          (runWord (mechanicalWord t v 0 T)) (T-(n+1)) A D) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := sparse_exceptional_subsequence r hr η hη (m-2)
  refine ⟨δ,hδ,N,hN,?_⟩
  intro s t hs ht htM hsr htr u v n T z hn hz hT
  obtain ⟨k,Y,_,hhi,hlen,hsub,hc⟩ := h s t hs ht htM hsr htr u v n z hn hz
  have hkT : k ≤ T := by exact_mod_cast hhi.trans hT
  have hsubT := hsub.trans (mechanical_prefix_sublist t v 0 k T hkT)
  let X := mechanicalWord s u 0 n ++ [z]
  refine ⟨rises X Y,falls X Y,hc,?_⟩
  have hp := paired_sublist_program m X Y (mechanicalWord t v 0 T)
    (by simp [X,mechanicalWord_length,hlen]) hsubT (mechanicalWord_legal t v 0 T (m-2) ht htM)
  simpa only [X,List.length_append,List.length_singleton,mechanicalWord_length] using hp

/-! An all-length version absorbs the finite initial range into one constant. -/


end KroneckerSparsePrescribedExceptional
end
end

section

/- Original module: KroneckerMechanicalActualEdits -/
section
/-! Actual finite edit programs have at most twice the boundary-visit cost. -/
set_option autoImplicit false
namespace KroneckerMechanicalActualEdits
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerPairedRunCosts
open KroneckerPairedRunPrograms KroneckerPairedMechanicalCost KroneckerMechanicalWords
open KroneckerBoundaryVisits KroneckerMechanicalBoundaryCost


end KroneckerMechanicalActualEdits
end

/- Original module: KroneckerMechanicalSublistEdits -/
section
/-! Aligned local mechanical edits extend to any prescribed legal supersequence. -/
set_option autoImplicit false
namespace KroneckerMechanicalSublistEdits
open KroneckerWordCounts KroneckerRawMixedPrograms KroneckerPairedRunCosts
open KroneckerPairedSublistPrograms KroneckerPairedMechanicalCost KroneckerMechanicalWords
open KroneckerBoundaryVisits KroneckerMechanicalBoundaryCost


end KroneckerMechanicalSublistEdits
end

/- Original module: KroneckerTotalEditBudget -/
section
/-! A total edit-cost bound supplies the asymmetric surplus-drain budget. -/
set_option autoImplicit false
namespace KroneckerTotalEditBudget



end KroneckerTotalEditBudget
end
end

section

/- Original module: KroneckerRealWeightedBudget -/
section
set_option autoImplicit false
namespace KroneckerRealWeightedBudget

theorem real_weighted_budget (m K A D P n : ℕ) (η : ℝ)
    (hc : ((A+D : ℕ) : ℝ) ≤ η*(n : ℝ))
    (hP : (K : ℝ)+(m+1 : ℕ)*η*(n : ℝ) ≤ P) : K+A+(m+1)*D ≤ P := by
  have hw : A+(m+1)*D ≤ (m+1)*(A+D) := by nlinarith
  have hwR : ((A+(m+1)*D : ℕ) : ℝ) ≤ (m+1 : ℕ)*((A+D : ℕ) : ℝ) := by exact_mod_cast hw
  have hm := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (m+1) : (0 : ℝ) ≤ (m+1 : ℕ))
  have h : ((K+A+(m+1)*D : ℕ) : ℝ) ≤ P := by
    push_cast at hwR ⊢
    push_cast at hm hP
    nlinarith
  exact_mod_cast h

end KroneckerRealWeightedBudget
end

/- Original module: KroneckerSparsePrescribedPrograms -/
section
set_option autoImplicit false
namespace KroneckerSparsePrescribedPrograms
open KroneckerSparseMechanicalSubsequence KroneckerMechanicalPrefixSublist KroneckerPairedSublistPrograms
open KroneckerMechanicalWords KroneckerPairedRunCosts KroneckerRawMixedPrograms KroneckerWordCounts

theorem sparse_prescribed_programs (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, ∀ s t : ℝ,
      0 ≤ s → 1 ≤ t → t ≤ (m-2 : ℕ) → |s-r| < δ → |t-r| < δ →
      ∀ u v : ℝ, ∀ n T : ℕ, N ≤ n → (1+η)*(n : ℝ) ≤ T →
      ∃ A D : ℕ, ((A+D : ℕ) : ℝ) ≤ η*(n : ℝ) ∧
        Nonempty (RawProgram m (runWord (mechanicalWord s u 0 n))
          (runWord (mechanicalWord t v 0 T)) (T-n) A D) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := sparse_mechanical_subsequence r hr η hη
  refine ⟨δ,hδ,N,hN,?_⟩
  intro m s t hs ht htM hsr htr u v n T hn hT
  obtain ⟨k,Y,_,hhi,hlen,hsub,hc⟩ := h s t hs (by linarith) hsr htr u v n hn
  have hkT : k ≤ T := by exact_mod_cast hhi.trans hT
  have hsubT := hsub.trans (mechanical_prefix_sublist t v 0 k T hkT)
  refine ⟨rises (mechanicalWord s u 0 n) Y,falls (mechanicalWord s u 0 n) Y,hc,?_⟩
  have hp := paired_sublist_program m (mechanicalWord s u 0 n) Y (mechanicalWord t v 0 T)
    (by rw [mechanicalWord_length,hlen]) hsubT (mechanicalWord_legal t v 0 T (m-2) ht htM)
  simpa only [mechanicalWord_length] using hp

end KroneckerSparsePrescribedPrograms
end

/- Original module: KroneckerSparsePrescribedCount -/
section
set_option autoImplicit false
namespace KroneckerSparsePrescribedCount
open KroneckerSparsePrescribedPrograms KroneckerRealWeightedBudget KroneckerFullComposition
open KroneckerMechanicalWords KroneckerRawMixedPrograms KroneckerWordCounts KroneckerFiberBudget

theorem sparse_prescribed_count (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, 4 ≤ m → ∀ s t : ℝ,
      0 ≤ s → 1 ≤ t → t ≤ (m-2 : ℕ) → |s-r| < δ → |t-r| < δ →
      ∀ u v : ℝ, ∀ n T P l b : ℕ, N ≤ n → (1+η)*(n : ℝ) ≤ T →
      (1 ≤ l ∧ l ≤ m-2) → (1 ≤ b ∧ b ≤ m-2) →
      ∀ left right : List ℕ, (∀ x ∈ left,1 ≤ x ∧ x ≤ m-2) →
      (∀ x ∈ right,1 ≤ x ∧ x ≤ m-2) → left.length=P → right.length=P →
      ((T-n : ℕ) : ℝ)+(m+1 : ℕ)*η*(n : ℝ) ≤ P →
      ∃ D : ℕ, (D : ℝ) ≤ η*(n : ℝ) ∧
        (runCount m (mechanicalWord s u 0 n) 0 : ℝ)/(fiberBudget m n D : ℝ) ≤
        (runCount m (left++(l::mechanicalWord t v 0 T++[b])++right) 0 : ℝ) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := sparse_prescribed_programs r hr η hη
  refine ⟨δ,hδ,N,hN,?_⟩
  intro m hm s t hs ht htM hsr htr u v n T P l b hn hT hl hb left right hleft hright hll hrl hP
  obtain ⟨A,D,hc,⟨p⟩⟩ := h m s t hs ht htM hsr htr u v n T hn hT
  have hbudget := real_weighted_budget m (T-n) A D P n η hc hP
  have hcount := (composition_prescribed_target hm hl hb (mechanicalWord s u 0 n)
    (mechanicalWord t v 0 T) left right p (mechanicalWord_legal t v 0 T (m-2) ht htM)
    hleft hright hll hrl hbudget).2
  refine ⟨D,?_,by simpa only [mechanicalWord_length] using hcount⟩
  push_cast at hc
  linarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)]

end KroneckerSparsePrescribedCount
end

/- Original module: KroneckerSparseFrameTargetCount -/
section
set_option autoImplicit false
namespace KroneckerSparseFrameTargetCount
open KroneckerFrameBadDensity KroneckerFrameSlope KroneckerMechanicalWords
open KroneckerWordCounts KroneckerFiberBudget

theorem sparse_frame_target_count (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, 4 ≤ m → ∀ s u : ℝ,
      0 ≤ s → |s-r| < δ → ∀ a b d l T P : ℕ,
      1 ≤ frameSlope a b d → frameSlope a b d ≤ (m-2 : ℕ) →
      |frameSlope a b d-r| < δ → N ≤ l →
      P+1+T+1+P=a+1 → (1+η)*(l : ℝ) ≤ T →
      ((T-l : ℕ) : ℝ)+(m+1 : ℕ)*η*(l : ℝ) ≤ P →
      ∃ D : ℕ, (D : ℝ) ≤ η*(l : ℝ) ∧
        (runCount m (mechanicalWord s u 0 l) 0 : ℝ)/(fiberBudget m l D : ℝ) ≤
        (runCount m (frameWord a b d) 0 : ℝ) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := KroneckerSparsePrescribedCount.sparse_prescribed_count r hr η hη
  refine ⟨δ,hδ,N,hN,?_⟩
  intro m hm s u hs hsr a b d l T P ht htM htr hl hsize hT hP
  obtain ⟨L,x,y,R,hX,hL,hR⟩ := KroneckerFrameCollarIdentity.frame_collar_identity a b d P T hsize
  have hlegal := KroneckerFrameWord.frameWord_legal a b d (m-2) ht htM
  have hx : 1 ≤ x ∧ x ≤ m-2 := hlegal x (by rw [hX];simp)
  have hy : 1 ≤ y ∧ y ≤ m-2 := hlegal y (by rw [hX];simp)
  have hleft : ∀ z ∈ L,1 ≤ z ∧ z ≤ m-2 := by
    intro z hz
    exact hlegal z (by rw [hX];simp [hz])
  have hright : ∀ z ∈ R,1 ≤ z ∧ z ≤ m-2 := by
    intro z hz
    exact hlegal z (by rw [hX];simp [hz])
  obtain ⟨D,hD,hcount⟩ := h m hm s (frameSlope a b d) hs ht htM hsr htr u
    ((P+1 : ℕ)*frameSlope a b d) l T P x y hl hT hx hy L R hleft hright hL hR hP
  exact ⟨D,hD,by simpa only [← hX] using hcount⟩

end KroneckerSparseFrameTargetCount
end

/- Original module: KroneckerSparseLogTransfer -/
section
set_option autoImplicit false
namespace KroneckerSparseLogTransfer
open KroneckerFiberBudget KroneckerNormalizedFiberBound KroneckerFiberEnvelopeLimit

theorem count_log_transfer (A B m n D : ℕ) (hA : 0 < A)
    (hcount : (A : ℝ)/(fiberBudget m n D : ℝ) ≤ B) :
    Real.log (A : ℝ) ≤ Real.log (B : ℝ)+Real.log (fiberBudget m n D : ℝ) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hF : (0 : ℝ) < fiberBudget m n D := by exact_mod_cast fiberBudget_positive m n D
  have hlog := Real.log_le_log (div_pos hAR hF) hcount
  rw [Real.log_div hAR.ne' hF.ne'] at hlog
  linarith

theorem normalized_count_log_transfer (A B m n D : ℕ) (hA : 0 < A) (hn : 0 < n)
    (hcount : (A : ℝ)/(fiberBudget m n D : ℝ) ≤ B) :
    Real.log (A : ℝ)/(n : ℝ) ≤ Real.log (B : ℝ)/(n : ℝ)+normalizedFiberLog m n D := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := div_le_div_of_nonneg_right (count_log_transfer A B m n D hA hcount) hnR.le
  simpa only [add_div,normalizedFiberLog] using h

theorem bounded_deletion_envelope (m n D : ℕ) (η τ : ℝ) (hn : 0 < n)
    (hD : (D : ℝ) ≤ η*(n : ℝ)) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    normalizedFiberLog m n D ≤ fiberEnvelope m τ η := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (D : ℝ)/(n : ℝ) ≤ η := (div_le_iff₀ hnR).mpr hD
  have hlog : 0 ≤ Real.log (1+τ) := Real.log_nonneg (by linarith)
  have htlog : Real.log τ ≤ 0 := Real.log_nonpos hτ.le hτ1
  have hcoef : 0 ≤ 2*(m : ℝ)*Real.log 2-Real.log τ := by
    have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    exact sub_nonneg.mpr (htlog.trans (mul_nonneg (mul_nonneg (by norm_num) hm) h2))
  have h1 := mul_le_mul_of_nonneg_right (add_le_add_left hd 1) hlog
  have h2 := mul_le_mul_of_nonneg_right hd hcoef
  have hb := normalizedFiberLog_bound m n D hn τ hτ
  unfold fiberEnvelope
  linarith

end KroneckerSparseLogTransfer
end

/- Original module: KroneckerSparseFrameTargetLog -/
section
set_option autoImplicit false
namespace KroneckerSparseFrameTargetLog
open KroneckerFrameBadDensity KroneckerFrameSlope KroneckerMechanicalWords KroneckerWordCounts
open KroneckerSparseLogTransfer KroneckerFiberEnvelopeLimit KroneckerNormalizedFiberBound

theorem sparse_frame_target_log (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, 4 ≤ m → ∀ s u : ℝ,
      1 ≤ s → s ≤ (m-1 : ℕ) → |s-r| < δ → ∀ a b d l T P : ℕ,
      1 ≤ frameSlope a b d → frameSlope a b d ≤ (m-2 : ℕ) →
      |frameSlope a b d-r| < δ → N ≤ l →
      P+1+T+1+P=a+1 → (1+η)*(l : ℝ) ≤ T →
      ((T-l : ℕ) : ℝ)+(m+1 : ℕ)*η*(l : ℝ) ≤ P → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      Real.log (runCount m (mechanicalWord s u 0 l) 0 : ℝ)/((a : ℝ)+1)-
        ((l : ℝ)/((a : ℝ)+1))*fiberEnvelope m τ η ≤
      Real.log (runCount m (frameWord a b d) 0 : ℝ)/((a : ℝ)+1) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := KroneckerSparseFrameTargetCount.sparse_frame_target_count r hr η hη
  refine ⟨δ,hδ,N,hN,?_⟩
  intro m hm s u hs hsM hsr a b d l T P ht htM htr hl hsize hT hP τ hτ hτ1
  obtain ⟨D,hD,hcount⟩ := h m hm s u (by linarith) hsr a b d l T P ht htM htr hl hsize hT hP
  have hlpos : 0 < l := lt_of_lt_of_le hN hl
  have hlR : (0 : ℝ) < l := by exact_mod_cast hlpos
  have hne : mechanicalWord s u 0 l ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [mechanicalWord_length,List.length_nil] at hh
    omega
  have hpos := KroneckerWordBounds.runCount_pos m (by omega) _ hne (mechanicalWord_legal s u 0 l (m-1) hs hsM)
  have hlog := count_log_transfer _ _ m l D hpos hcount
  have henv := bounded_deletion_envelope m l D η τ hlpos hD hτ hτ1
  have hf : Real.log (KroneckerFiberBudget.fiberBudget m l D : ℝ) ≤ fiberEnvelope m τ η*(l : ℝ) :=
    (div_le_iff₀ hlR).mp henv
  have hraw : Real.log (runCount m (mechanicalWord s u 0 l) 0 : ℝ)-
      (l : ℝ)*fiberEnvelope m τ η ≤ Real.log (runCount m (frameWord a b d) 0 : ℝ) := by nlinarith
  have hnorm := div_le_div_of_nonneg_right hraw (show (0 : ℝ) ≤ (a : ℝ)+1 by positivity)
  simpa only [sub_div,mul_div_right_comm] using hnorm

end KroneckerSparseFrameTargetLog
end

/- Original module: KroneckerEventualLowerComparison -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualLowerComparison
open KroneckerComparisonSchedules KroneckerComparisonScales KroneckerFrameBadDensity
open KroneckerWordCounts KroneckerMechanicalWords KroneckerFiberEnvelopeLimit

theorem eventual_lower_comparison (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : Irrational r)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) (η : ℝ) (hη : 0 < η)
    (hsmall : inflationScale m*η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t v : ℝ, 1 ≤ t → t ≤ (m-2 : ℕ) → |t-r| < δ →
      ∀ q : ℕ, 0 < q → ∀ a b d : ℕ → ℕ, Tendsto a atTop atTop → (∀ n,0 < d n) →
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ n in atTop,
      Real.log (runCount m (mechanicalWord t v 0 (lowerLength m q η (a n+1))) 0 : ℝ)/((a n : ℝ)+1)-
        ((lowerLength m q η (a n+1) : ℝ)/((a n : ℝ)+1))*fiberEnvelope m τ η ≤
      Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/((a n : ℝ)+1) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := KroneckerSparseFrameTargetLog.sparse_frame_target_log r hr η hη
  refine ⟨δ,hδ,?_⟩
  intro t v ht htM htr q hq a b d ha hd hratio τ hτ hτ1
  have has : Tendsto (fun n => a n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp ha
  have hbud := KroneckerLowerScheduleBudget.lower_schedule_budget (fun n => a n+1) has m q N hq η hη hsmall
  have hdata := KroneckerEventualFrameData.eventual_frame_data a b d ha hd r hratio (m-2) 0 hr1 hrM δ hδ
  have ht1 : t ≤ (m-1 : ℕ) := htM.trans (by exact_mod_cast (show m-2 ≤ m-1 by omega))
  filter_upwards [hbud,hdata] with n hn hdatan
  have hh := h m hm t v ht ht1 htr (a n) (b n) (d n)
    (lowerLength m q η (a n+1)) (lowerMiddle m η (a n+1)) (collar m η (a n+1))
    hdatan.2.2.1 hdatan.2.2.2.1 hdatan.2.2.2.2 hn.1 hn.2.2.2 hn.2.1 hn.2.2.1 τ hτ hτ1
  exact hh

end KroneckerEventualLowerComparison
end

/- Original module: KroneckerMechanicalTargetCount -/
section
set_option autoImplicit false
namespace KroneckerMechanicalTargetCount
open KroneckerMechanicalCollarIdentity KroneckerFullComposition KroneckerMechanicalWords
open KroneckerRawMixedPrograms KroneckerWordCounts KroneckerFiberBudget

theorem mechanical_target_count (m : ℕ) (hm : 4 ≤ m) (X : List ℕ) (t v : ℝ)
    (P T K A D : ℕ) (ht : 1 ≤ t) (htM : t ≤ (m-2 : ℕ))
    (p : RawProgram m (runWord X) (runWord (mechanicalWord t v (P+1) T)) K A D)
    (hP : K+A+(m+1)*D ≤ P) :
    (runCount m X 0 : ℝ)/(fiberBudget m X.length D : ℝ) ≤
      (runCount m (mechanicalWord t v 0 (P+1+T+1+P)) 0 : ℝ) := by
  rw [mechanical_collar_identity]
  exact (composition_prescribed_target hm (natRun_legal t v P (m-2) ht htM)
    (natRun_legal t v (P+1+T) (m-2) ht htM) X (mechanicalWord t v (P+1) T)
    (mechanicalWord t v 0 P) (mechanicalWord t v (P+1+T+1) P) p
    (mechanicalWord_legal t v (P+1) T (m-2) ht htM)
    (mechanicalWord_legal t v 0 P (m-2) ht htM)
    (mechanicalWord_legal t v (P+1+T+1) P (m-2) ht htM)
    (mechanicalWord_length t v 0 P) (mechanicalWord_length t v (P+1+T+1) P) hP).2

end KroneckerMechanicalTargetCount
end

/- Original module: KroneckerSparseFullFrameCount -/
section
set_option autoImplicit false
namespace KroneckerSparseFullFrameCount
open KroneckerSparsePrescribedExceptional KroneckerRealWeightedBudget KroneckerMechanicalTargetCount
open KroneckerMechanicalWordShift KroneckerMechanicalWords KroneckerRawMixedPrograms
open KroneckerWordCounts KroneckerFiberBudget KroneckerFrameWord KroneckerFrameBadDensity KroneckerFrameSlope

theorem sparse_full_frame_count (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η)
    (m : ℕ) (hm : 4 ≤ m) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ a b d : ℕ,
      N ≤ a → 0 < b → 0 < d → |frameSlope a b d-r| < δ →
      ∀ t v : ℝ, 1 ≤ t → t ≤ (m-2 : ℕ) → |t-r| < δ → ∀ T P : ℕ,
      (1+η)*((a : ℝ)+1) ≤ T →
      ((T-(a+1) : ℕ) : ℝ)+(m+1 : ℕ)*η*((a : ℝ)+1) ≤ P →
      ∃ D : ℕ, (D : ℝ) ≤ η*((a : ℝ)+1) ∧
        (runCount m (frameWord a b d) 0 : ℝ)/(fiberBudget m (a+1) D : ℝ) ≤
        (runCount m (mechanicalWord t v 0 (P+1+T+1+P)) 0 : ℝ) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := sparse_prescribed_exceptional r hr η hη m
  refine ⟨δ,hδ,N,hN,?_⟩
  intro a b d ha hb hd hsr t v ht htM htr T P hT hP
  have ha0 : 0 < a := hN.trans_le ha
  obtain ⟨A,D,hc,⟨p⟩⟩ := h (frameSlope a b d) t (frameSlope_nonnegative a b d ha0 hb hd)
    ht htM hsr htr 0 (v+((P+1 : ℕ) : ℝ)*t) a T 1 ha (by omega) hT
  rw [← word_shift t v (P+1) T] at p
  change RawProgram m (runWord (frameWord a b d)) _ _ _ _ at p
  have hbudget := real_weighted_budget m (T-(a+1)) A D P (a+1) η
    (by simpa using hc) (by simpa using hP)
  have hcount := mechanical_target_count m hm (frameWord a b d) t v P T (T-(a+1)) A D ht htM p hbudget
  refine ⟨D,?_,by simpa only [frameWord_length] using hcount⟩
  push_cast at hc
  linarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)]

end KroneckerSparseFullFrameCount
end

/- Original module: KroneckerSparseFrameLogComparison -/
section
set_option autoImplicit false
namespace KroneckerSparseFrameLogComparison
open KroneckerSparseFullFrameCount KroneckerSparseLogTransfer KroneckerFiberEnvelopeLimit
open KroneckerWordCounts KroneckerWordBounds KroneckerMechanicalWords
open KroneckerFrameBadDensity KroneckerFrameSlope KroneckerFrameWord

theorem sparse_frame_log_comparison (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η)
    (m : ℕ) (hm : 4 ≤ m) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ a b d : ℕ,
      N ≤ a → 0 < b → 0 < d → 1 ≤ frameSlope a b d → frameSlope a b d ≤ (m-1 : ℕ) →
      |frameSlope a b d-r| < δ → ∀ t v : ℝ,
      1 ≤ t → t ≤ (m-2 : ℕ) → |t-r| < δ → ∀ T P : ℕ,
      (1+η)*((a : ℝ)+1) ≤ T →
      ((T-(a+1) : ℕ) : ℝ)+(m+1 : ℕ)*η*((a : ℝ)+1) ≤ P →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      Real.log (runCount m (frameWord a b d) 0 : ℝ)/((a : ℝ)+1) ≤
        Real.log (runCount m (mechanicalWord t v 0 (P+1+T+1+P)) 0 : ℝ)/((a : ℝ)+1)+
          fiberEnvelope m τ η := by
  obtain ⟨δ,hδ,N,hN,h⟩ := sparse_full_frame_count r hr η hη m hm
  refine ⟨δ,hδ,N,hN,?_⟩
  intro a b d ha hb hd hs hsM hsr t v ht htM htr T P hT hP τ hτ hτ1
  obtain ⟨D,hD,hcount⟩ := h a b d ha hb hd hsr t v ht htM htr T P hT hP
  have hne : frameWord a b d ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [frameWord_length,List.length_nil] at hh
    omega
  have hpos := runCount_pos m (by omega) (frameWord a b d) hne
    (frameWord_legal a b d (m-1) hs hsM)
  have hlog := normalized_count_log_transfer (runCount m (frameWord a b d) 0)
    (runCount m (mechanicalWord t v 0 (P+1+T+1+P)) 0) m (a+1) D hpos (by omega) hcount
  have henv := bounded_deletion_envelope m (a+1) D η τ (by omega) (by simpa using hD) hτ hτ1
  push_cast at hlog
  linarith

end KroneckerSparseFrameLogComparison
end

/- Original module: KroneckerEventualUpperComparison -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerEventualUpperComparison
open KroneckerComparisonSchedules KroneckerFrameBadDensity KroneckerWordCounts
open KroneckerMechanicalWords KroneckerFiberEnvelopeLimit

theorem eventual_upper_comparison (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : Irrational r)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t v : ℝ, 1 ≤ t → t ≤ (m-2 : ℕ) → |t-r| < δ →
      ∀ q : ℕ, 0 < q → ∀ a b d : ℕ → ℕ, Tendsto a atTop atTop → (∀ n,0 < d n) →
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ n in atTop,
      Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/((a n : ℝ)+1) ≤
      Real.log (runCount m (mechanicalWord t v 0 (upperLength m q η (a n+1))) 0 : ℝ)/((a n : ℝ)+1)+
        fiberEnvelope m τ η := by
  obtain ⟨δ,hδ,N,hN,h⟩ := KroneckerSparseFrameLogComparison.sparse_frame_log_comparison r hr η hη m hm
  refine ⟨δ,hδ,?_⟩
  intro t v ht htM htr q hq a b d ha hd hratio τ hτ hτ1
  have has : Tendsto (fun n => a n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp ha
  have hbud := KroneckerUpperScheduleBudget.upper_schedule_budget (fun n => a n+1) has m q 0 hq η hη
  have hdata := KroneckerEventualFrameData.eventual_frame_data a b d ha hd r hratio (m-2) N hr1 hrM δ hδ
  filter_upwards [hbud,hdata] with n hn hdatan
  have hsM : KroneckerFrameSlope.frameSlope (a n) (b n) (d n) ≤ (m-1 : ℕ) :=
    hdatan.2.2.2.1.trans (by exact_mod_cast (show m-2 ≤ m-1 by omega))
  have hh := h (a n) (b n) (d n) hdatan.1 hdatan.2.1 (hd n) hdatan.2.2.1 hsM hdatan.2.2.2.2
    t v ht htM htr (upperMiddle m q η (a n+1)) (collar m η (a n+1))
    (by simpa only [Nat.cast_add,Nat.cast_one] using hn.2.1)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hn.2.2.1) τ hτ hτ1
  simpa only [hn.2.2.2] using hh

end KroneckerEventualUpperComparison
end

/- Original module: KroneckerIrrationalLowerBound -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIrrationalLowerBound
open KroneckerComparisonSchedules KroneckerComparisonScales KroneckerPeriodicTail
open KroneckerFrameBadDensity KroneckerWordCounts KroneckerMechanicalWords KroneckerFiberEnvelopeLimit

theorem irrational_lower_bound (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : Irrational r)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) (η : ℝ) (hη : 0 < η)
    (hsmall : inflationScale m*η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t v : ℝ, 1 ≤ t → t ≤ (m-2 : ℕ) → |t-r| < δ →
      ∀ p : ℤ, ∀ q : ℕ, 0 < q → (q : ℝ)*t=p →
      ∀ a b d : ℕ → ℕ, Tendsto a atTop atTop → (∀ n,0 < d n) →
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (1-inflationScale m*η)*
        (periodicGrowth m (mechanicalWord t v 0 q)/(q : ℝ)-fiberEnvelope m τ η)-ε ≤
      Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/((a n : ℝ)+1) := by
  obtain ⟨δ,hδ,h⟩ := KroneckerEventualLowerComparison.eventual_lower_comparison m hm r hr hr1 hrM η hη hsmall
  refine ⟨δ,hδ,?_⟩
  intro t v ht htM htr p q hq hp a b d ha hd hratio τ hτ hτ1 ε hε
  have has : Tendsto (fun n => a n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp ha
  have ht1 : t ≤ (m-1 : ℕ) := htM.trans (by exact_mod_cast (show m-2 ≤ m-1 by omega))
  have hc : 0 < 1-inflationScale m*η := by linarith
  have hlog := KroneckerRoundedPeriodicLog.lower_rounded_periodic_log m (by omega) t v p q hq hp ht ht1
    (fun n => a n+1) has (1-inflationScale m*η) hc
  have hlen := KroneckerPeriodicRounding.lower_period_length_density (fun n => a n+1) has q hq
    (1-inflationScale m*η) hc.le
  have hlim := hlog.sub (hlen.mul_const (fiberEnvelope m τ η))
  have hbound := (tendsto_order.1 hlim).1
    ((1-inflationScale m*η)*(periodicGrowth m (mechanicalWord t v 0 q)/(q : ℝ)-fiberEnvelope m τ η)-ε)
    (by nlinarith)
  filter_upwards [h t v ht htM htr q hq a b d ha hd hratio τ hτ hτ1,hbound] with n hn hb
  refine le_trans ?_ hn
  simpa only [lowerLength,Nat.cast_add,Nat.cast_one] using hb.le

end KroneckerIrrationalLowerBound
end

/- Original module: KroneckerIrrationalUpperBound -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIrrationalUpperBound
open KroneckerComparisonSchedules KroneckerComparisonScales KroneckerPeriodicTail
open KroneckerFrameBadDensity KroneckerWordCounts KroneckerMechanicalWords KroneckerFiberEnvelopeLimit

theorem irrational_upper_bound (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : Irrational r)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t v : ℝ, 1 ≤ t → t ≤ (m-2 : ℕ) → |t-r| < δ →
      ∀ p : ℤ, ∀ q : ℕ, 0 < q → (q : ℝ)*t=p →
      ∀ a b d : ℕ → ℕ, Tendsto a atTop atTop → (∀ n,0 < d n) →
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/((a n : ℝ)+1) ≤
        (1+inflationScale m*η)*(periodicGrowth m (mechanicalWord t v 0 q)/(q : ℝ))+
          fiberEnvelope m τ η+ε := by
  obtain ⟨δ,hδ,h⟩ := KroneckerEventualUpperComparison.eventual_upper_comparison m hm r hr hr1 hrM η hη
  refine ⟨δ,hδ,?_⟩
  intro t v ht htM htr p q hq hp a b d ha hd hratio τ hτ hτ1 ε hε
  have has : Tendsto (fun n => a n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp ha
  have ht1 : t ≤ (m-1 : ℕ) := htM.trans (by exact_mod_cast (show m-2 ≤ m-1 by omega))
  have hlim := KroneckerRoundedPeriodicLog.upper_rounded_periodic_log m (by omega) t v p q hq hp ht ht1
    (fun n => a n+1) has (1+inflationScale m*η) (upper_scale_slack m η hη).2.1
  have hbound := (tendsto_order.1 (hlim.add_const (fiberEnvelope m τ η))).2
    ((1+inflationScale m*η)*(periodicGrowth m (mechanicalWord t v 0 q)/(q : ℝ))+fiberEnvelope m τ η+ε)
    (by linarith)
  filter_upwards [h t v ht htM htr q hq a b d ha hd hratio τ hτ hτ1,hbound] with n hn hb
  exact hn.trans (by simpa only [upperLength,Nat.cast_add,Nat.cast_one] using hb.le)

end KroneckerIrrationalUpperBound
end

/- Original module: KroneckerIrrationalIntervals -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIrrationalIntervals
open KroneckerComparisonScales KroneckerPeriodicTail KroneckerMechanicalWords
open KroneckerFiberEnvelopeLimit KroneckerFrameObservables KroneckerLogic

noncomputable def runValue (m : ℕ) (x : FramePoint) : ℝ :=
  Real.log (KroneckerWordCounts.runCount m (KroneckerFrameBadDensity.frameWord x.a x.b x.d) 0 : ℝ)/((x.a : ℝ)+1)
noncomputable def periodRate (m : ℕ) (t : ℝ) (q : ℕ) : ℝ :=
  periodicGrowth m (mechanicalWord t 0 0 q)/(q : ℝ)

theorem irrational_intervals (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : Irrational r)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) (η : ℝ) (hη : 0 < η)
    (hsmall : inflationScale m*η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 1 ≤ t → t ≤ (m-2 : ℕ) → |t-r| < δ →
      ∀ p : ℤ, ∀ q : ℕ, 0 < q → (q : ℝ)*t=p →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ x : Approaching height slope r, ∀ᶠ n in atTop,
      (1-inflationScale m*η)*(periodRate m t q-fiberEnvelope m τ η)-ε ≤ runValue m (x.val n) ∧
      runValue m (x.val n) ≤ (1+inflationScale m*η)*periodRate m t q+fiberEnvelope m τ η+ε := by
  obtain ⟨δu,hδu,hu⟩ := KroneckerIrrationalUpperBound.irrational_upper_bound m hm r hr hr1 hrM η hη
  obtain ⟨δl,hδl,hl⟩ := KroneckerIrrationalLowerBound.irrational_lower_bound m hm r hr hr1 hrM η hη hsmall
  refine ⟨min δu δl,lt_min hδu hδl,?_⟩
  intro t ht htM htr p q hq hp τ hτ hτ1 ε hε x
  have hu' := hu t 0 ht htM (lt_of_lt_of_le htr (min_le_left _ _)) p q hq hp
    (fun n => (x.val n).a) (fun n => (x.val n).b) (fun n => (x.val n).d)
    x.property.1 (fun n => (x.val n).hd) x.property.2 τ hτ hτ1 ε hε
  have hl' := hl t 0 ht htM (lt_of_lt_of_le htr (min_le_right _ _)) p q hq hp
    (fun n => (x.val n).a) (fun n => (x.val n).b) (fun n => (x.val n).d)
    x.property.1 (fun n => (x.val n).hd) x.property.2 τ hτ hτ1 ε hε
  exact hl'.and hu'

end KroneckerIrrationalIntervals
end
end

