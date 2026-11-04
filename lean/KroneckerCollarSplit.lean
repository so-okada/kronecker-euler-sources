import KroneckerNormalizedFiberBound
import KroneckerNormalizationPrograms
import KroneckerIntegerComparisonLengths

/- Original module: KroneckerFiberBudgetMonotone -/
section
/-! Enlarging the deletion allowance enlarges the exact fiber budget. -/
set_option autoImplicit false
namespace KroneckerFiberBudgetMonotone
open KroneckerFiberBudget KroneckerNormalizedFiberBound

theorem additive_choose_mono_deletions (n D E : ℕ) (h : D ≤ E) :
    (n+D).choose D ≤ (n+E).choose E := by
  calc
    (n+D).choose D = (n+D).choose n := Nat.choose_symm_add.symm
    _ ≤ (n+E).choose n := Nat.choose_le_choose n (by omega)
    _ = (n+E).choose E := Nat.choose_symm_add

theorem fiberBudget_mono_deletions (m n D E : ℕ) (h : D ≤ E) :
    fiberBudget m n D ≤ fiberBudget m n E := by
  apply Nat.mul_le_mul (additive_choose_mono_deletions n D E h)
  exact pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (Nat.mul_le_mul_left (2*m) h)


end KroneckerFiberBudgetMonotone
end

/- Original module: KroneckerIntegerWordComparison -/
section
/-! Actual finite comparisons with constant run words, using the absolute edit cost. -/
set_option autoImplicit false
namespace KroneckerIntegerWordComparison
open KroneckerWordCounts KroneckerFiberBudget KroneckerFiberBudgetMonotone
open KroneckerWordEditCost KroneckerNormalizationCosts KroneckerNormalizationPrograms
open KroneckerPrescribedMixedRuns

theorem constant_collar_word (k n P : ℕ) :
    List.replicate P k++(k::List.replicate n k++[k])++List.replicate P k =
      List.replicate (n+2*P+2) k := by
  have h : k::List.replicate n k++[k]=List.replicate (n+2) k := by
    change k::(List.replicate n k++[k])=List.replicate (n+2) k
    rw [← List.replicate_succ',← List.replicate_succ]
  rw [h,List.replicate_append_replicate,List.replicate_append_replicate]
  congr 1
  omega

theorem word_to_constant_count {m k P : ℕ} (hm : 4 ≤ m)
    (hk : 1 ≤ k ∧ k ≤ m-2) (X : List ℕ)
    (hP : (m+1)*wordEditCost X k ≤ P) :
    runCount m X 0 ≤ fiberBudget m X.length (wordEditCost X k)*
      runCount m (List.replicate (X.length+2*P+2) k) 0 := by
  obtain ⟨⟨p⟩,_⟩ := normalization_programs m X k []
  simp only [List.nil_append] at p
  have hl : ∀ r ∈ List.replicate P k,1 ≤ r ∧ r ≤ m-2 := by
    intro r hr
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp hr
    exact hk
  have hb : 0+raiseCost X k+(m+1)*lowerCost X k ≤ P := by
    have h := (normalization_cost_budget m X k).1
    omega
  have h := prescribed_mixed_run_count hm hk hk X (List.replicate X.length k)
    (List.replicate P k) (List.replicate P k) p hl hl (by simp) (by simp) hb
  rw [constant_collar_word] at h
  have hd : lowerCost X k ≤ wordEditCost X k := by
    have he := normalization_cost_identity X k
    omega
  exact h.trans (Nat.mul_le_mul_right _ (fiberBudget_mono_deletions m X.length
    (lowerCost X k) (wordEditCost X k) hd))

theorem constant_to_word_count {m k u v P : ℕ} (hm : 4 ≤ m)
    (hu : 1 ≤ u ∧ u ≤ m-2) (hv : 1 ≤ v ∧ v ≤ m-2) (X left right : List ℕ)
    (hl : ∀ r ∈ left,1 ≤ r ∧ r ≤ m-2) (hr : ∀ r ∈ right,1 ≤ r ∧ r ≤ m-2)
    (hll : left.length=P) (hrl : right.length=P)
    (hP : (m+1)*wordEditCost X k ≤ P) :
    runCount m (List.replicate X.length k) 0 ≤
      fiberBudget m X.length (wordEditCost X k)*runCount m (left++(u::X++[v])++right) 0 := by
  obtain ⟨_,⟨p⟩⟩ := normalization_programs m X k []
  simp only [List.nil_append] at p
  have hb : 0+lowerCost X k+(m+1)*raiseCost X k ≤ P := by
    have h := (normalization_cost_budget m X k).2
    omega
  have h := prescribed_mixed_run_count hm hu hv (List.replicate X.length k) X left right
    p hl hr hll hrl hb
  simp only [List.length_replicate] at h
  have hd : raiseCost X k ≤ wordEditCost X k := by
    have he := normalization_cost_identity X k
    omega
  exact h.trans (Nat.mul_le_mul_right _ (fiberBudget_mono_deletions m X.length
    (raiseCost X k) (wordEditCost X k) hd))

end KroneckerIntegerWordComparison
end

/- Original module: KroneckerSingletonPeriod -/
section
/-! Identify a one-run period with the literal constant run list. -/
set_option autoImplicit false
namespace KroneckerSingletonPeriod
open KroneckerWordCounts KroneckerPeriodicWords

theorem repeatRuns_singleton (k n : ℕ) : repeatRuns [k] n=List.replicate n k := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repeatRuns,ih,← List.replicate_succ']

theorem periodicCount_singleton (m k n : ℕ) :
    periodicCount m [k] n=runCount m (List.replicate n k) 0 := by
  rw [periodicCount,repeatRuns_singleton]

end KroneckerSingletonPeriod
end

/- Original module: KroneckerSurgeryBudget -/
section
/-! The manuscript padding dominates the actual normalization-layer budget. -/
set_option autoImplicit false
namespace KroneckerSurgeryBudget
open KroneckerSurgeryPadding

theorem surgeryPadding_budget (m D : ℕ) : (m+1)*D ≤ surgeryPadding m D := by
  unfold surgeryPadding
  nlinarith


end KroneckerSurgeryBudget
end

/- Original module: KroneckerPeriodicIntegerUpper -/
section
/-! The actual finite upper comparison in the periodic-count notation. -/
set_option autoImplicit false
namespace KroneckerPeriodicIntegerUpper
open KroneckerWordCounts KroneckerPeriodicWords KroneckerSingletonPeriod
open KroneckerFiberBudget KroneckerWordEditCost KroneckerIntegerWordComparison

theorem periodic_integer_upper {m k P : ℕ} (hm : 4 ≤ m)
    (hk : 1 ≤ k ∧ k ≤ m-2) (X : List ℕ) (hP : (m+1)*wordEditCost X k ≤ P) :
    runCount m X 0 ≤ periodicCount m [k] (X.length+2*P+2)*fiberBudget m X.length (wordEditCost X k) := by
  simpa only [periodicCount_singleton,Nat.mul_comm] using word_to_constant_count hm hk X hP

end KroneckerPeriodicIntegerUpper
end

/- Original module: KroneckerFrameIntegerUpper -/
section
/-! The literal frame satisfies the exact finite upper comparison. -/
set_option autoImplicit false
namespace KroneckerFrameIntegerUpper
open KroneckerWordCounts KroneckerPeriodicWords KroneckerFiberBudget KroneckerWordEditCost
open KroneckerFrameBadDensity KroneckerFrameWord KroneckerSurgeryPadding KroneckerSurgeryBudget
open KroneckerIntegerComparisonLengths KroneckerPeriodicIntegerUpper

theorem frame_integer_upper {m k : ℕ} (hm : 4 ≤ m) (hk : 1 ≤ k ∧ k ≤ m-2) (a b d : ℕ) :
    runCount m (frameWord a b d) 0 ≤
      periodicCount m [k] (paddedLength a (surgeryPadding m (wordEditCost (frameWord a b d) k)))*
        fiberBudget m (a+1) (wordEditCost (frameWord a b d) k) := by
  have h := periodic_integer_upper (P:=surgeryPadding m (wordEditCost (frameWord a b d) k))
    hm hk (frameWord a b d) (surgeryPadding_budget m (wordEditCost (frameWord a b d) k))
  have hlen : (frameWord a b d).length+2*surgeryPadding m (wordEditCost (frameWord a b d) k)+2=
      paddedLength a (surgeryPadding m (wordEditCost (frameWord a b d) k)) := by
    rw [frameWord_length]
    unfold paddedLength
    omega
  rw [hlen,frameWord_length] at h
  exact h

end KroneckerFrameIntegerUpper
end

/- Original module: KroneckerEditCostSublist -/
section
/-! Removing runs cannot increase the absolute normalization edit cost. -/
set_option autoImplicit false
namespace KroneckerEditCostSublist
open KroneckerWordEditCost


end KroneckerEditCostSublist
end

/- Original module: KroneckerEditCostSlices -/
section
/-! Prefix, suffix and middle edit costs are bounded by the complete word cost. -/
set_option autoImplicit false
namespace KroneckerEditCostSlices
open KroneckerWordEditCost KroneckerEditCostSublist



theorem editCost_middle (left X right : List ℕ) (k : ℕ) :
    wordEditCost X k ≤ wordEditCost (left++X++right) k := by
  rw [wordEditCost_append,wordEditCost_append]
  omega

end KroneckerEditCostSlices
end

/- Original module: KroneckerCollarSplit -/
section
/-! Split an actual target into two collars, two buffers and the exact middle. -/
set_option autoImplicit false
namespace KroneckerCollarSplit

theorem split_three (X : List ℕ) (a b c : ℕ) (h : X.length=a+1+b+1+c) :
    ∃ L u Y v R, X=L++(u::Y++[v])++R ∧ L.length=a ∧ Y.length=b ∧ R.length=c := by
  cases ht : X.drop a with
  | nil =>
    have hh := congrArg List.length ht
    simp only [List.length_drop,List.length_nil] at hh
    omega
  | cons u T =>
    have htlen : T.length=b+1+c := by
      have hh := congrArg List.length ht
      simp only [List.length_drop,List.length_cons] at hh
      omega
    cases hs : T.drop b with
    | nil =>
      have hh := congrArg List.length hs
      simp only [List.length_drop,List.length_nil] at hh
      omega
    | cons v R =>
      have hrlen : R.length=c := by
        have hh := congrArg List.length hs
        simp only [List.length_drop,List.length_cons] at hh
        omega
      have hT : T=T.take b++v::R := by rw [← hs,List.take_append_drop]
      have hX : X=X.take a++u::T := by rw [← ht,List.take_append_drop]
      refine ⟨X.take a,u,T.take b,v,R,?_,?_,?_,hrlen⟩
      · calc
          X=X.take a++u::T := hX
          _=X.take a++u::(T.take b++v::R) := congrArg (fun Z => X.take a++u::Z) hT
          _=X.take a++(u::T.take b++[v])++R := by
            simp only [List.cons_append,List.append_assoc,List.nil_append]
      · simp only [List.length_take]
        omega
      · simp only [List.length_take]
        omega

theorem collar_split (X : List ℕ) (P : ℕ) (h : 2*P+2 ≤ X.length) :
    ∃ L u Y v R, X=L++(u::Y++[v])++R ∧
      L.length=P ∧ Y.length=X.length-2*P-2 ∧ R.length=P :=
  split_three X P (X.length-2*P-2) P (by omega)

end KroneckerCollarSplit
end
