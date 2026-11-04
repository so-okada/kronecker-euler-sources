import KroneckerReflectedPairSlotCounts

set_option autoImplicit false

namespace KroneckerActualPairClosedCounts
open KroneckerQuarticRationalExtraction KroneckerPairTreeClassCount KroneckerQuarticPowerCoefficients
attribute [local instance] Classical.propDecidable
open PowerSeries KroneckerTwoMarkRationalSeries KroneckerActualPairCountSeries
open KroneckerActualQuarticCounts KroneckerTwoMarkResponseSystem

theorem different_mark_closed_coefficient (n : ℕ) :
    coeff (n+2) differentMark=
      ((4*n+6).choose (n+1) : ℚ)-((4*n+6).choose n : ℚ) := by
  have h := quartic_cleared_coefficient differentMark _ substituted_pair_cleared.2 (n+1)
  have he : 4*(n+1)+2=4*n+6 := by omega
  rw [he,show n+1+1=n+2 by omega] at h
  rw [show (X : PowerSeries ℚ)*(1-X)*(1+X)^(4*n+6)=
    X*(1+X)^(4*n+6)-X^2*(1+X)^(4*n+6) by ring,
    map_sub,coeff_succ_X_mul,coeff_X_pow_mul,coeff_one_add_X_pow,coeff_one_add_X_pow] at h
  exact h
theorem actual_different_pair_count (n : ℕ) {d e : Fin 3} (hde : d≠e) :
    Fintype.card (PairClass (Fin (n+2)) (Fin (2*(n+2)+1)) d e)+
      (4*n+6).choose n=(4*n+6).choose (n+1) := by
  have h := different_mark_closed_coefficient n
  change coeff (n+2) (KroneckerActualBranchLinearization.sourceMark 0 1)=_ at h
  rw [←source_mark_distinct_uniform hde (show (1:Fin 3)≠0 by decide),source_mark_pair_count] at h
  have h' : (Fintype.card (PairClass (Fin (n+2)) (Fin (2*(n+2)+1)) d e) : ℚ)+
      ((4*n+6).choose n : ℚ)=((4*n+6).choose (n+1) : ℚ) := by linarith
  exact_mod_cast h'
end KroneckerActualPairClosedCounts

namespace KroneckerActualSourceEulerEquation
open KroneckerActualBranchLinearization KroneckerActualQuarticCounts
open KroneckerActualBranchSeries KroneckerFiniteBranchClasses

theorem actual_source_euler_equation :
    (1-3*branchT)*PowerSeries.X*PowerSeries.derivative (R := ℚ) branchT=branchT*(1+branchT) := by
  have hq : branchT=PowerSeries.X*(1+branchT)^4 := actual_source_quartic 0
  have hd := congrArg (PowerSeries.derivative (R := ℚ)) hq
  simp only [Derivation.leibniz,PowerSeries.derivative_X,smul_eq_mul,Derivation.leibniz_pow,
    map_add,Derivation.map_one_eq_zero,zero_add,nsmul_eq_mul] at hd
  norm_num only [Nat.reduceSub] at hd
  linear_combination PowerSeries.X*(1+branchT)*hd-
    (1+branchT+4*PowerSeries.X*PowerSeries.derivative (R := ℚ) branchT)*hq

theorem actual_source_euler_coeff (n : ℕ) :
    PowerSeries.coeff (n+1) (PowerSeries.X*PowerSeries.derivative (R := ℚ) branchT)=
      (Fintype.card (SourceDegreeClass (n+1) 0) : ℚ)*(n+1) := by
  rw [PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_derivative]
  exact congrArg (fun c : ℚ => c*(n+1)) (source_series_counts 0 (n+1))
end KroneckerActualSourceEulerEquation

namespace KroneckerActualPairCoefficientRatio
open KroneckerActualPairComparison KroneckerActualSourceEulerEquation KroneckerTwoMarkRationalSeries
open KroneckerTwoMarkResponseSystem KroneckerActualBranchLinearization KroneckerActualQuarticCounts
open KroneckerActualPairCountSeries KroneckerPairTreeClassCount
attribute [local instance] Classical.propDecidable
theorem difference_series_euler_equation :
    (PowerSeries.X*PowerSeries.derivative (R := ℚ) differenceSeries)*(1-3*branchT)=differenceSeries := by
  dsimp only [differenceSeries]
  simp only [Derivation.leibniz,PowerSeries.derivative_X,smul_eq_mul,Derivation.leibniz_pow,
    map_add,Derivation.map_one_eq_zero,zero_add,nsmul_eq_mul]
  norm_num only [Nat.reduceSub]
  linear_combination 3*PowerSeries.X*(1+branchT)^2*actual_source_euler_equation

theorem pair_series_differential_relation :
    PowerSeries.C 2*(PowerSeries.X*PowerSeries.derivative (R := ℚ) (differentMark-sameMark))=
      PowerSeries.C 2*differentMark+sameMark := by
  norm_num only [map_ofNat]
  apply mul_right_cancel₀ response_denominator_ne_zero
  rw [pair_response_difference]
  change (2*(PowerSeries.X*PowerSeries.derivative (R := ℚ) differenceSeries))*responseDenominator=_
  have hc : differenceSeries*(1+branchT)=branchT := by
    have hq : branchT=PowerSeries.X*(1+branchT)^4 := actual_source_quartic 0
    dsimp only [differenceSeries]
    linear_combination -hq
  have hE : (PowerSeries.X*PowerSeries.derivative (R := ℚ) differenceSeries)*responseDenominator=branchT := by
    dsimp only [responseDenominator]
    linear_combination (1+branchT)*difference_series_euler_equation+hc
  linear_combination 2*hE-2*two_mark_cleared_formulas.2-two_mark_cleared_formulas.1

theorem response_coefficient_ratio (n : ℕ) :
    (2*n : ℚ)*PowerSeries.coeff (n+1) differentMark=
      (2*n+3 : ℚ)*PowerSeries.coeff (n+1) sameMark := by
  have h := congrArg (PowerSeries.coeff (n+1)) pair_series_differential_relation
  simp only [map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_derivative,map_sub] at h
  linear_combination h

theorem actual_pair_count_ratio (n : ℕ) {d e : Fin 3} (hde : d≠e) :
    2*n*Fintype.card (PairClass (Fin (n+1)) (Fin (2*(n+1)+1)) d e)=
      (2*n+3)*Fintype.card (PairClass (Fin (n+1)) (Fin (2*(n+1)+1)) d d) := by
  have h := response_coefficient_ratio n
  have hs : sourceMark d d=sameMark := source_mark_diagonal_uniform d 0
  have ht : sourceMark e d=differentMark := source_mark_distinct_uniform hde (by decide)
  rw [←hs,←ht,source_mark_pair_count,source_mark_pair_count] at h
  exact_mod_cast h
end KroneckerActualPairCoefficientRatio

namespace KroneckerReflectedSingleSlotCounts
open KroneckerActualSourceClosedCounts

theorem reflected_single_slot_closed_count (j : ℕ) (d : Fin 3) :
    (Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d) : ℚ)=
      ((4*j+4).choose (j+1) : ℚ)/(3*j+4) := by
  have hc := single_slot_cardinality (I:=Fin (j+1)) (J:=Fin (2*(j+1)+1)) d
  have h := actual_single_marked_count j d
  simp only [←Nat.card_eq_fintype_card] at hc h ⊢
  rw [hc]
  exact h
end KroneckerReflectedSingleSlotCounts

namespace KroneckerReflectedPairSlotCounts
open KroneckerActualPairClosedCounts

theorem reflected_same_slot_count (n : ℕ) (d : Fin 3) :
    Fintype.card (PairSlotClass (Fin (n+2)) (Fin (2*(n+2)+1)) d d)=2*(4*n+6).choose n := by
  have hc := pair_slot_cardinality (I:=Fin (n+2)) (J:=Fin (2*(n+2)+1)) d d
  have h := actual_same_pair_count n d
  simp only [←Nat.card_eq_fintype_card] at hc h ⊢
  rw [hc]
  exact h

theorem reflected_different_slot_count (n : ℕ) {d e : Fin 3} (hde : d≠e) :
    Fintype.card (PairSlotClass (Fin (n+2)) (Fin (2*(n+2)+1)) d e)+
      (4*n+6).choose n=(4*n+6).choose (n+1) := by
  have hc := pair_slot_cardinality (I:=Fin (n+2)) (J:=Fin (2*(n+2)+1)) d e
  have h := actual_different_pair_count n hde
  simp only [←Nat.card_eq_fintype_card] at hc h ⊢
  rw [hc]
  exact h

theorem reflected_slot_pair_ratio (j : ℕ) {d e : Fin 3} (hde : d≠e) :
    2*j*Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d e)=
      (2*j+3)*Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d d) := by
  have hc := pair_slot_cardinality (I:=Fin (j+1)) (J:=Fin (2*(j+1)+1)) d e
  have hd := pair_slot_cardinality (I:=Fin (j+1)) (J:=Fin (2*(j+1)+1)) d d
  have h := KroneckerActualPairCoefficientRatio.actual_pair_count_ratio j hde
  simp only [←Nat.card_eq_fintype_card] at hc hd h ⊢
  rw [hc,hd]
  exact h

theorem reflected_slot_pair_comparison (j : ℕ) {d e : Fin 3} (hde : d≠e) :
    Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d d)≤
      Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d e) := by
  have hc := pair_slot_cardinality (I:=Fin (j+1)) (J:=Fin (2*(j+1)+1)) d e
  have hd := pair_slot_cardinality (I:=Fin (j+1)) (J:=Fin (2*(j+1)+1)) d d
  have h := KroneckerActualPairComparison.actual_pair_count_comparison (j+1) hde
  simp only [←Nat.card_eq_fintype_card] at hc hd h ⊢
  rw [hc,hd]
  exact h
end KroneckerReflectedPairSlotCounts
