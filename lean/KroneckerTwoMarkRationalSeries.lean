import KroneckerActualBranchLinearization
import Mathlib.RingTheory.PowerSeries.Inverse

/- Original module: KroneckerLeafDeletionProfile -/
section
set_option autoImplicit false
namespace KroneckerLeafDeletionProfile
open KroneckerFiniteColoredTables KroneckerColoredTableRestrictions KroneckerTableLeafMarks
open KroneckerLeafDeletedColors
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I]

theorem leaf_mark_color_unique (T : ColoredTable I J) {d e : Fin 3} {l : J}
    (hd : LeafMark T d l) (he : LeafMark T e l) : e=d := by
  obtain ⟨i,hi⟩ := he.2
  have ho : i=leafOwner T hd := (leaf_incidence_iff_owner T hd i).mp ⟨e,hi⟩
  exact Option.some.inj (hi.symm.trans (by rw [ho]; exact leaf_owner_code T hd))

def remainingLeafEquiv (T : ColoredTable I J) (e : Fin 3) (l : J) :
    {j // LeafMark (restrictSinkTable T (fun j => j≠l)) e j} ≃
      {j : {j // LeafMark T e j} // j.1≠l} where
  toFun j := ⟨⟨j.1.1,j.2⟩,j.1.2⟩
  invFun j := ⟨⟨j.1.1,j.2⟩,j.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem removed_leaf_color_card [Fintype J] (T : ColoredTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T d l) (e : Fin 3) :
    Fintype.card {j : {j // LeafMark T e j} // j.1=l}=if e=d then 1 else 0 := by
  classical
  by_cases he : e=d
  · subst e
    let : Unique {j : {j // LeafMark T d j} // j.1=l} :=
      { default := ⟨⟨l,hl⟩,rfl⟩,
        uniq := by rintro ⟨j,hj⟩; apply Subtype.ext; exact Subtype.ext hj }
    simp
  · let : IsEmpty {j : {j // LeafMark T e j} // j.1=l} :=
      ⟨fun j => he (leaf_mark_color_unique T hl (by simpa only [j.2] using j.1.2))⟩
    simp [he]

/-- Leaf deletion preserves the full color profile, except for the one specified parent leaf. -/
theorem leaf_deleted_profile [Fintype J] (T : ColoredTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T d l) (e : Fin 3) :
    Fintype.card {j // LeafMark (restrictSinkTable T (fun j => j≠l)) e j}+
      (if e=d then 1 else 0)=Fintype.card {j // LeafMark T e j} := by
  classical
  have hc := Fintype.card_congr (Equiv.sumCompl (fun j : {j // LeafMark T e j} => j.1=l))
  rw [Fintype.card_sum,removed_leaf_color_card T hl e] at hc
  rw [Fintype.card_congr (remainingLeafEquiv T e l)]
  simp only [←Nat.card_eq_fintype_card] at hc ⊢
  exact (Nat.add_comm _ _).trans hc

end KroneckerLeafDeletionProfile
end

/- Original module: KroneckerCompletionLeafWeights -/
section
set_option autoImplicit false
namespace KroneckerCompletionLeafWeights
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerSourceCompletionObjects
open KroneckerLeafDeletionProfile KroneckerLeafCompletionInverse KroneckerTableLeafMarks
open KroneckerSourceBranchCompletion KroneckerBranchWeights KroneckerGradedProfileWeights
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

theorem completed_object_leaf_profile (S : SourceObject I J d) (e : Fin 3) :
    Fintype.card {j // LeafMark (completeSourceObject S).1.1.1 e j}=
      Fintype.card {j // LeafMark S.1.1 e j}+(if e=d then 1 else 0) := by
  have h := leaf_deleted_profile (completeBranch S.1.1 S.1.2 d S.2).1
    (completed_parent_leaf S.1.1 S.1.2 d S.2) e
  have hc := leaf_mark_count_invariant (deleteCompletedIso S.1.1 S.1.2 d S.2) e
  simp only [←Nat.card_eq_fintype_card] at h hc ⊢
  rw [hc] at h
  exact h.symm

/-- Completion multiplies the genuine leaf monomial by precisely the parent-color variable. -/
theorem completed_object_weight {R : Type*} [CommSemiring R]
    (S : SourceObject I J d) (x : R) (y : Fin 3 → R) :
    sourceWeight (completeSourceObject S).1.1.1 x y=y d*sourceWeight S.1.1 x y := by
  unfold sourceWeight
  simp only [completed_object_leaf_profile]
  have h := graded_weight_add x y (Fintype.card I) 0
    (fun e => Fintype.card {j // LeafMark S.1.1 e j}) (fun e => if e=d then 1 else 0)
  simp only [Nat.add_zero,graded_weight_leaf] at h
  rw [h,mul_comm]

end KroneckerCompletionLeafWeights
end

/- Original module: KroneckerMarkedClassWeights -/
section
set_option autoImplicit false
namespace KroneckerMarkedClassWeights
open KroneckerMarkedTableAction KroneckerMarkedTreeClassCount KroneckerMarkedClassIsomorphisms
open KroneckerBranchWeights KroneckerGradedProfileWeights
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}
variable {R : Type*} [CommSemiring R]

/-- The marked-class weight retains the whole tree's actual leaf profile. -/
noncomputable def markedClassWeight (x : R) (y : Fin 3 → R) : MarkedClass I J d → R :=
  Quotient.lift (fun M => sourceWeight M.1.1.1 x y) (by
    intro M N h
    obtain ⟨e,_⟩ := (marked_class_eq_iff M N).mp (Quotient.sound h)
    exact source_weight_iso e x y)

theorem marked_class_weight_at_one (q : MarkedClass I J d) :
    markedClassWeight (1 : R) (fun _ => 1) q=1 := by
  induction q using Quotient.inductionOn with | _ M =>
    simp [markedClassWeight,sourceWeight,gradedWeight]

theorem marked_class_weight_sum_at_one :
    (∑ q : MarkedClass I J d,markedClassWeight (1 : R) (fun _ => 1) q)=
      (Fintype.card (MarkedClass I J d) : R) := by simp [marked_class_weight_at_one]

end KroneckerMarkedClassWeights
end

/- Original module: KroneckerWeightedCompletionClassSum -/
section
set_option autoImplicit false
namespace KroneckerWeightedCompletionClassSum
open KroneckerBranchClassRelations KroneckerFiniteBranchClasses KroneckerCompletionClassInjection
open KroneckerCompletionClassEquivalence KroneckerMarkedTreeClassCount KroneckerMarkedClassWeights
open KroneckerBranchClassWeights KroneckerCompletionLeafWeights
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}
variable {R : Type*} [CommSemiring R]

theorem completed_class_weight (q : SourceClass I J d) (x : R) (y : Fin 3 → R) :
    markedClassWeight x y (completeOnClasses q)=y d*sourceClassWeight x y q := by
  induction q using Quotient.inductionOn with | _ S =>
    exact completed_object_weight S x y

/-- The exact weighted marking dictionary holds on finite isomorphism classes, with no stabilizer factor. -/
theorem weighted_completion_class_sum (x : R) (y : Fin 3 → R) :
    (∑ q : MarkedClass I (Option J) d,markedClassWeight x y q)=
      y d*∑ q : SourceClass I J d,sourceClassWeight x y q := by
  calc
    _ = ∑ q : SourceClass I J d,markedClassWeight x y (completionClassEquiv q) :=
      (Equiv.sum_comp (completionClassEquiv (I:=I) (J:=J) (d:=d)) (markedClassWeight x y)).symm
    _ = _ := by
      change (∑ q : SourceClass I J d,markedClassWeight x y (completeOnClasses q))=_
      simp only [completed_class_weight,Finset.mul_sum]

end KroneckerWeightedCompletionClassSum
end

/- Original module: KroneckerWeightedMarkingFibers -/
section
set_option autoImplicit false
namespace KroneckerWeightedMarkingFibers
open KroneckerLabelledTreeClassCount KroneckerMarkedTreeClassCount KroneckerMarkedClassWeights
open KroneckerBranchWeights KroneckerTreeLeafEnumerator KroneckerTableLeafMarks
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}
variable {R : Type*} [CommSemiring R]

noncomputable def treeClassWeight (x : R) (y : Fin 3 → R) : TreeClass I J → R :=
  Quotient.lift (fun T => sourceWeight T.1 x y) (by
    intro T U h
    obtain ⟨e⟩ := (class_eq_iff I J T U).mp (Quotient.sound h)
    exact source_weight_iso e x y)

theorem marked_weight_forget (q : MarkedClass I J d) (x : R) (y : Fin 3 → R) :
    markedClassWeight x y q=treeClassWeight x y (forgetOnClasses I J d q) := by
  induction q using Quotient.inductionOn with | _ M => rfl

theorem tree_weight_representative (q : TreeClass I J) (x : R) (y : Fin 3 → R) :
    treeClassWeight x y q=sourceWeight q.out.1 x y := by
  have h := congrArg (treeClassWeight x y) (Quotient.out_eq' q)
  exact h.symm

/-- The full polynomial marking weight is constant on every actual forgetting fiber. -/
theorem weighted_marked_class_sum (x : R) (y : Fin 3 → R) :
    (∑ q : MarkedClass I J d,markedClassWeight x y q)=
      ∑ q : TreeClass I J,(leafProfile I J q d : R)*treeClassWeight x y q := by
  calc
    _ = ∑ p : (Σ q : TreeClass I J,{u : MarkedClass I J d // forgetOnClasses I J d u=q}),
        markedClassWeight x y p.2.1 :=
      (Equiv.sum_comp (Equiv.sigmaFiberEquiv (forgetOnClasses I J d)) _).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      have hc : Fintype.card {u : MarkedClass I J d // forgetOnClasses I J d u=q}=
          leafProfile I J q d := by
        simpa only [Quotient.out_eq',leafProfile] using marked_class_fiber_count I J d q.out
      calc
        _ = ∑ _u : {u : MarkedClass I J d // forgetOnClasses I J d u=q},treeClassWeight x y q := by
          apply Finset.sum_congr rfl
          intro u _
          rw [marked_weight_forget,u.2]
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc]

end KroneckerWeightedMarkingFibers
end

/- Original module: KroneckerActualLeafDerivative -/
section
set_option autoImplicit false
namespace KroneckerActualLeafDerivative
open KroneckerWeightedMarkingFibers KroneckerWeightedCompletionClassSum
open KroneckerMarkedClassWeights KroneckerMarkedTreeClassCount KroneckerMarkedCarrierTransport
open KroneckerGradedMarkedBranchCounts KroneckerTreeLeafEnumerator KroneckerFiniteMarkingPolynomial
open KroneckerBranchWeights KroneckerGradedProfileWeights KroneckerActualBranchSeries
open KroneckerColoredTableTransport KroneckerFiniteBranchClasses MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem profile_monomial (N : Fin 3 → ℕ) :
    (∏ d,(X d : MvPolynomial (Fin 3) ℚ)^(N d))=
      monomial (Finsupp.equivFunOnFinite.symm N) 1 := by
  rw [monomial_eq,map_one,one_mul,Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

variable {I J I' J' : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J'] {d : Fin 3}

theorem weighted_marked_carrier (s : I ≃ I') (t : J ≃ J') {R : Type*} [CommSemiring R]
    (x : R) (y : Fin 3 → R) :
    (∑ q : MarkedClass I J d,markedClassWeight x y q)=
      ∑ q : MarkedClass I' J' d,markedClassWeight x y q := by
  rw [←Equiv.sum_comp (markedCarrierEquiv (d:=d) s t) (markedClassWeight x y)]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with | _ M =>
    exact source_weight_iso (transportIso M.1.1.1 s t) x y

omit [Fintype I'] [Fintype J'] in
theorem actual_leaf_euler_derivative :
    X d*pderiv d (leafEnumerator I J)=
      ∑ q : MarkedClass I J d,markedClassWeight (1 : MvPolynomial (Fin 3) ℚ) X q := by
  rw [weighted_marked_class_sum]
  simp only [leafEnumerator,profilePolynomial,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [X_mul_pderiv_monomial,nsmul_eq_mul,tree_weight_representative]
  simp only [sourceWeight,gradedWeight,one_pow,one_mul,profile_monomial]
  rfl

/-- Marking and deleting a leaf is the actual polynomial derivative, before evaluation at one. -/
theorem actual_leaf_derivative (n : ℕ) (e : Fin 3) :
    pderiv e (leafEnumerator (Fin n) (Fin (2*n+1)))=
      PowerSeries.coeff n (sourceSeries (X : Fin 3 → MvPolynomial (Fin 3) ℚ) e) := by
  have h := actual_leaf_euler_derivative (I:=Fin n) (J:=Fin (2*n+1)) (d:=e)
  have ht := weighted_marked_carrier (d:=e) (Equiv.refl (Fin n)) (optionFinSinkEquiv n)
    (1 : MvPolynomial (Fin 3) ℚ) X
  rw [←ht,weighted_completion_class_sum] at h
  rw [source_series_coeff]
  exact mul_left_cancel₀ (X_ne_zero e) h

end KroneckerActualLeafDerivative
end

/- Original module: KroneckerActualPairCountSeries -/
section
set_option autoImplicit false
namespace KroneckerActualPairCountSeries
open KroneckerActualLeafDerivative KroneckerActualBranchLinearization KroneckerCoefficientMarkDerivative
open KroneckerPairTreeClassCount KroneckerTreeLeafEnumerator KroneckerMarkedClassColorSymmetry
attribute [local instance] Classical.propDecidable

/-- The derivative series counts ordered distinct marked leaves in the actual unrooted tree classes. -/
theorem source_mark_pair_count (d e : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (sourceMark e d)=
      (Fintype.card (PairClass (Fin n) (Fin (2*n+1)) d e) : ℚ) := by
  rw [sourceMark,mark_derivative_coeff,←actual_leaf_derivative]
  by_cases h : d=e
  · subst e
    simpa only [←Nat.card_eq_fintype_card] using
      repeated_marked_enumerator_count (Fin n) (Fin (2*n+1)) d
  · simpa only [←Nat.card_eq_fintype_card] using
      mixed_marked_enumerator_count (Fin n) (Fin (2*n+1)) h

theorem source_mark_diagonal_uniform (d e : Fin 3) : sourceMark d d=sourceMark e e := by
  apply PowerSeries.ext
  intro n
  rw [source_mark_pair_count,source_mark_pair_count]
  have h := equal_color_count_uniform (I:=Fin n) (J:=Fin (2*n+1)) d e
  simp only [←Nat.card_eq_fintype_card] at h ⊢
  exact congrArg (fun x : ℕ => (x : ℚ)) h

theorem source_mark_distinct_uniform {d e a b : Fin 3} (hde : d≠e) (hab : a≠b) :
    sourceMark e d=sourceMark b a := by
  apply PowerSeries.ext
  intro n
  rw [source_mark_pair_count,source_mark_pair_count]
  have h := distinct_color_count_uniform (I:=Fin n) (J:=Fin (2*n+1)) hde hab
  simp only [←Nat.card_eq_fintype_card] at h ⊢
  exact congrArg (fun x : ℕ => (x : ℚ)) h


end KroneckerActualPairCountSeries
end

/- Original module: KroneckerTwoMarkResponseSystem -/
section
set_option autoImplicit false
namespace KroneckerTwoMarkResponseSystem
open KroneckerActualBranchLinearization KroneckerActualPairCountSeries KroneckerThreeColorBranchGrammar
open KroneckerActualQuarticCounts

noncomputable def sameMark : PowerSeries ℚ := sourceMark 0 0
noncomputable def differentMark : PowerSeries ℚ := sourceMark 0 1

theorem off_diagonal_color_two : sourceMark 0 2=differentMark :=
  source_mark_distinct_uniform (by decide) (by decide)

theorem sink_zero_response : sinkMark 0 0=1+2*(1+branchT)*differentMark := by
  rw [sink_mark_equation]
  norm_num only [nextColor,lastColor,Fin.reduceAdd,ite_true,map_one]
  change 1+(1+branchT)*(sourceMark 0 1+sourceMark 0 2)=_
  rw [off_diagonal_color_two]
  change 1+(1+branchT)*(differentMark+differentMark)=_
  ring

theorem sink_one_response : sinkMark 0 1=(1+branchT)*(sameMark+differentMark) := by
  rw [sink_mark_equation]
  norm_num only [nextColor,lastColor,Fin.reduceAdd,Fin.zero_ne_one,ite_false,map_zero,zero_add]
  change (1+branchT)*(sourceMark 0 2+sourceMark 0 0)=_
  rw [off_diagonal_color_two]
  change (1+branchT)*(differentMark+sameMark)=_
  ring

theorem sink_two_response : sinkMark 0 2=(1+branchT)*(sameMark+differentMark) := by
  rw [sink_mark_equation]
  rw [ite_eq_right (show (0 : Fin 3)≠2 by decide),map_zero,zero_add]
  rfl

/-- The three colored response equations reduce to two actual pair-count series. -/
theorem two_mark_response_system :
    sameMark=2*PowerSeries.X*(1+branchT)^3*(sameMark+differentMark) ∧
    differentMark=PowerSeries.X*(1+branchT)^2+
      PowerSeries.X*(1+branchT)^3*(sameMark+3*differentMark) := by
  constructor
  · have h := source_mark_equation 0 0
    norm_num only [nextColor,lastColor,Fin.reduceAdd] at h
    change sameMark=PowerSeries.X*(sinkMark 0 1*(1+branchT)^2+(1+branchT)^2*sinkMark 0 2) at h
    rw [sink_one_response,sink_two_response] at h
    change sameMark=_ at h
    linear_combination h
  · have h := source_mark_equation 0 1
    norm_num only [nextColor,lastColor,Fin.reduceAdd] at h
    change differentMark=PowerSeries.X*(sinkMark 0 2*(1+branchT)^2+(1+branchT)^2*sinkMark 0 0) at h
    rw [sink_two_response,sink_zero_response] at h
    change differentMark=_ at h
    linear_combination h

end KroneckerTwoMarkResponseSystem
end

/- Original module: KroneckerTwoMarkRationalSeries -/
section
set_option autoImplicit false
namespace KroneckerTwoMarkRationalSeries
open KroneckerTwoMarkResponseSystem KroneckerActualBranchLinearization KroneckerActualQuarticCounts
open KroneckerActualBranchSeries

noncomputable def responseDenominator : PowerSeries ℚ := (1+branchT)*(1-3*branchT)

theorem response_denominator_constant : PowerSeries.constantCoeff responseDenominator=1 := by
  simp [responseDenominator,branchT,source_series_constant]

/-- Exact elimination of the two response equations in the power-series ring. -/
theorem two_mark_cleared_formulas :
    sameMark*responseDenominator=2*branchT^2 ∧
    differentMark*responseDenominator=branchT*(1-branchT) := by
  obtain ⟨ha,hb⟩ := two_mark_response_system
  have hq : branchT=PowerSeries.X*(1+branchT)^4 := actual_source_quartic 0
  let c := PowerSeries.X*(1+branchT)^3
  have hc : c*(1+branchT)=branchT := by
    calc
      _ = PowerSeries.X*(1+branchT)^4 := by dsimp [c]; ring
      _ = _ := hq.symm
  have h1 : (1-branchT)*sameMark=2*branchT*differentMark := by
    linear_combination (1+branchT)*ha-2*(sameMark+differentMark)*hq
  have h2 : (1-2*branchT)*differentMark-branchT*sameMark=c := by
    dsimp only [c]
    linear_combination (1+branchT)*hb-(sameMark+3*differentMark)*hq
  dsimp only [responseDenominator]
  constructor
  · linear_combination (1+branchT)*(1-2*branchT)*h1+
      2*branchT*(1+branchT)*h2+2*branchT*hc
  · linear_combination (1+branchT)*branchT*h1+
      (1+branchT)*(1-branchT)*h2+(1-branchT)*hc


theorem different_mark_rational_series :
    differentMark=branchT*(1-branchT)*PowerSeries.invOfUnit responseDenominator 1 := by
  calc
    _ = (differentMark*responseDenominator)*PowerSeries.invOfUnit responseDenominator 1 := by
      rw [mul_assoc,PowerSeries.mul_invOfUnit _ _ response_denominator_constant,mul_one]
    _ = _ := by rw [two_mark_cleared_formulas.2]

end KroneckerTwoMarkRationalSeries
end
