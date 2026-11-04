import KroneckerMechanicalWordSums
import KroneckerRationalPeriodAlphabet
import KroneckerMechanicalWordShift
import KroneckerPeriodicLimit

section

/- Original module: KroneckerMechanicalRepetition -/
section
/-! The literal natural mechanical words agree with repetitions of their
rational period, not merely with a periodic sequence of formal grades. -/
set_option autoImplicit false
namespace KroneckerMechanicalRepetition
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalWordSums
open KroneckerMechanicalPeriodicity KroneckerPeriodicWords

theorem word_period_shift (s u : ℝ) (p : ℤ) (q start n : ℕ) (hp : (q : ℝ)*s = (p : ℝ)) :
    mechanicalWord s u (start+q) n = mechanicalWord s u start n := by
  unfold mechanicalWord
  congr 1
  funext i
  unfold natRun
  rw [show start+q+i.val = (start+i.val)+q by omega, mechanical_period s u p q _ hp]

theorem word_shift_multiple (s u : ℝ) (p : ℤ) (q start k n : ℕ) (hp : (q : ℝ)*s = (p : ℝ)) :
    mechanicalWord s u (start+k*q) n = mechanicalWord s u start n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, word_period_shift s u p q _ n hp, ih]

theorem mechanicalWord_repetition (s u : ℝ) (p : ℤ) (q j : ℕ) (hp : (q : ℝ)*s = (p : ℝ)) :
    mechanicalWord s u 0 (j*q) = repeatRuns (mechanicalWord s u 0 q) j := by
  induction j with
  | zero => simp [mechanicalWord, repeatRuns]
  | succ j ih =>
    rw [Nat.succ_mul, mechanicalWord_append, ih]
    have h := word_shift_multiple s u p q 0 j q hp
    simpa only [Nat.zero_add, repeatRuns] using congrArg (fun w => repeatRuns (mechanicalWord s u 0 q) j ++ w) h


end KroneckerMechanicalRepetition
end

/- Original module: KroneckerRationalPeriodRepetition -/
section
/-! Nonprimitive rational periods are literal repetitions, also at shifted intercepts. -/
set_option autoImplicit false
namespace KroneckerRationalPeriodRepetition
open KroneckerMechanicalWords KroneckerMechanicalRepetition KroneckerMechanicalWordShift
open KroneckerPeriodicWords KroneckerRationalWordRotation

theorem mechanical_repetition_start (s u : ℝ) (p : ℤ) (q start k : ℕ)
    (hp : (q : ℝ)*s=(p : ℝ)) :
    mechanicalWord s u start (k*q)=repeatRuns (mechanicalWord s u start q) k := by
  rw [word_shift,mechanicalWord_repetition s (u+(start : ℝ)*s) p q k hp]
  rw [word_shift s u start q]

theorem rational_period_scaled (p q k : ℕ) (hq : 0 < q) (hk : 0 < k) :
    rationalPeriod (p*k) (q*k)=repeatRuns (rationalPeriod p q) k := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hs : ((p*k : ℕ) : ℝ)/((q*k : ℕ) : ℝ)=(p : ℝ)/(q : ℝ) := by
    push_cast
    field_simp
  unfold rationalPeriod
  rw [hs,Nat.mul_comm q k]
  apply mechanicalWord_repetition _ _ (p : ℤ)
  simp only [Int.cast_natCast]
  field_simp

end KroneckerRationalPeriodRepetition
end
end

section

/- Original module: KroneckerCommonRationalPeriod -/
section
/-! Equal rational slopes have an identical common-multiple mechanical period. -/
set_option autoImplicit false
namespace KroneckerCommonRationalPeriod
open KroneckerMechanicalWords KroneckerMechanicalRepetition KroneckerPeriodicWords
open KroneckerRationalWordRotation

theorem common_rational_period (p q a b : ℕ) (hq : 0 < q) (hb : 0 < b)
    (hs : (p : ℝ)/(q : ℝ)=(a : ℝ)/(b : ℝ)) :
    repeatRuns (rationalPeriod p q) b=repeatRuns (rationalPeriod a b) q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hp : (q : ℝ)*((p : ℝ)/(q : ℝ))=((p : ℤ) : ℝ) := by
    simp only [Int.cast_natCast]; field_simp
  have ha : (b : ℝ)*((a : ℝ)/(b : ℝ))=((a : ℤ) : ℝ) := by
    simp only [Int.cast_natCast]; field_simp
  unfold rationalPeriod
  rw [←mechanicalWord_repetition _ _ (p : ℤ) q b hp,
    ←mechanicalWord_repetition _ _ (a : ℤ) b q ha,hs,Nat.mul_comm b q]

end KroneckerCommonRationalPeriod
end

/- Original module: KroneckerRepeatedPeriods -/
section
/-! A repeated period has the same literal word as the corresponding sampled index. -/
set_option autoImplicit false
namespace KroneckerRepeatedPeriods
open KroneckerPeriodicWords

theorem repeatRuns_mul (W : List ℕ) (k n : ℕ) :
    repeatRuns (repeatRuns W k) n=repeatRuns W (k*n) := by
  induction n with
  | zero => simp [repeatRuns]
  | succ n ih => simp only [repeatRuns,ih,Nat.mul_succ,repeatRuns_add]

theorem periodicCount_repeated (m : ℕ) (W : List ℕ) (k n : ℕ) :
    periodicCount m (repeatRuns W k) n=periodicCount m W (k*n) := by
  simp only [periodicCount,repeatRuns_mul]

end KroneckerRepeatedPeriods
end

/- Original module: KroneckerScaledPeriodLimit -/
section
/-! Sampling every kth period multiplies the growth per sampled index by k. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerScaledPeriodLimit
open KroneckerPeriodicWords KroneckerPeriodicLog KroneckerPeriodicTail KroneckerPeriodicLimit

theorem scaled_period_limit (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => periodicLog m W (k*n)/(n : ℝ)) atTop
      (𝓝 ((k : ℝ)*periodicGrowth m W)) := by
  have ht : Tendsto (fun n : ℕ => k*n) atTop atTop := by
    apply tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id
  have h := ((periodicLog_limit m hm W hne hW).comp ht).const_mul (k : ℝ)
  apply h.congr'
  apply Eventually.of_forall
  intro n
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [Function.comp_def,Nat.cast_mul]
  field_simp

end KroneckerScaledPeriodLimit
end

/- Original module: KroneckerRepeatedGrowth -/
section
/-! Growth scales exactly with repetition of the literal period. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerRepeatedGrowth
open KroneckerPeriodicWords KroneckerPeriodicLog KroneckerPeriodicTail KroneckerPeriodicLimit
open KroneckerRepeatedPeriods KroneckerScaledPeriodLimit

theorem repeated_growth (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (k : ℕ) (hk : 0 < k) :
    periodicGrowth m (repeatRuns W k)=(k : ℝ)*periodicGrowth m W := by
  have hne' := repeatRuns_ne_nil W hne k hk
  have hlegal : ∀ r ∈ repeatRuns W k, 1 ≤ r ∧ r ≤ m-1 :=
    fun r hr => hW r (mem_repeatRuns W k hr)
  have h₁ := periodicLog_limit m hm (repeatRuns W k) hne' hlegal
  have h₂ := scaled_period_limit m hm W hne hW k hk
  apply tendsto_nhds_unique h₁
  simpa only [periodicLog,periodicCount_repeated] using h₂

end KroneckerRepeatedGrowth
end

/- Original module: KroneckerRationalRateInvariant -/
section
/-! Normalized periodic growth depends on the rational slope, not its fraction. -/
set_option autoImplicit false
namespace KroneckerRationalRateInvariant
open KroneckerPeriodicTail KroneckerRationalWordRotation KroneckerRationalPeriodAlphabet
open KroneckerRepeatedGrowth KroneckerCommonRationalPeriod

theorem rational_rate_invariant (m p q a b : ℕ) (hm : 3 ≤ m) (hq : 0 < q) (hb : 0 < b)
    (hlo : 1 ≤ (p : ℝ)/(q : ℝ)) (hhi : (p : ℝ)/(q : ℝ) ≤ (m-1 : ℕ))
    (hs : (p : ℝ)/(q : ℝ)=(a : ℝ)/(b : ℝ)) :
    periodicGrowth m (rationalPeriod p q)/(q : ℝ)=
      periodicGrowth m (rationalPeriod a b)/(b : ℝ) := by
  have hlo' : 1 ≤ (a : ℝ)/(b : ℝ) := by rwa [←hs]
  have hhi' : (a : ℝ)/(b : ℝ) ≤ (m-1 : ℕ) := by rwa [←hs]
  have h := congrArg (periodicGrowth m) (common_rational_period p q a b hq hb hs)
  rw [repeated_growth m hm (rationalPeriod p q) (rationalPeriod_nonempty p q hq)
    (rationalPeriod_legal p q (m-1) hlo hhi) b hb,
    repeated_growth m hm (rationalPeriod a b) (rationalPeriod_nonempty a b hb)
    (rationalPeriod_legal a b (m-1) hlo' hhi') q hq] at h
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  apply (div_eq_div_iff hq0 hb0).mpr
  simpa only [mul_comm] using h

end KroneckerRationalRateInvariant
end

/- Original module: KroneckerRationalReduction -/
section
/-! A nonintegral natural fraction has a coprime reduction with denominator at least two. -/
set_option autoImplicit false
namespace KroneckerRationalReduction

theorem rational_reduction (p q : ℕ) (hq : 0 < q) (hn : ¬q ∣ p) :
    ∃ a b k, 0 < k ∧ 1 < b ∧ a.Coprime b ∧ p=a*k ∧ q=b*k ∧
      (p : ℝ)/(q : ℝ)=(a : ℝ)/(b : ℝ) := by
  obtain ⟨a,b,hc,hp,hqb⟩ := Nat.exists_coprime p q
  let k := p.gcd q
  have hk : 0 < k := Nat.gcd_pos_of_pos_right p hq
  change p=a*k at hp
  change q=b*k at hqb
  have hb0 : b ≠ 0 := by intro h; rw [h,Nat.zero_mul] at hqb; omega
  have hb1 : b ≠ 1 := by
    intro h
    apply hn
    refine ⟨a,?_⟩
    rw [hp,hqb,h,Nat.one_mul]
    exact Nat.mul_comm _ _
  have hb : 1 < b := by omega
  refine ⟨a,b,k,hk,hb,hc,hp,hqb,?_⟩
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hb0' : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
  rw [hp,hqb]
  push_cast
  field_simp

end KroneckerRationalReduction
end
end

