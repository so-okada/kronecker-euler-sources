import KroneckerReflectedSingleSlotCounts

/- Original module: KroneckerActualPairComparison -/
section
set_option autoImplicit false
namespace KroneckerActualPairComparison
open KroneckerTwoMarkRationalSeries KroneckerTwoMarkResponseSystem KroneckerActualBranchLinearization
open KroneckerActualQuarticCounts KroneckerActualPairCountSeries KroneckerActualBranchSeries
open KroneckerBranchWeightNaturality KroneckerPairTreeClassCount
attribute [local instance] Classical.propDecidable

theorem response_denominator_ne_zero : responseDenominator≠0 := by
  intro h
  have hc := response_denominator_constant
  rw [h,map_zero] at hc
  norm_num at hc

/-- The difference between unlike and like leaf pairs is itself a nonnegative counting series. -/
theorem pair_response_difference :
    differentMark-sameMark=PowerSeries.X*(1+branchT)^3 := by
  apply mul_right_cancel₀ response_denominator_ne_zero
  rw [sub_mul,two_mark_cleared_formulas.1,two_mark_cleared_formulas.2]
  dsimp only [responseDenominator]
  have hq : branchT=PowerSeries.X*(1+branchT)^4 := actual_source_quartic 0
  linear_combination (1-3*branchT)*hq

theorem pair_difference_natural_series :
    differentMark-sameMark=PowerSeries.map (Nat.castRingHom ℚ)
      (PowerSeries.X*(1+sourceSeries (fun _ => (1 : ℕ)) 0)^3) := by
  rw [pair_response_difference]
  simp only [map_mul,PowerSeries.map_X,map_pow,map_add,map_one,source_series_map]
  rfl

theorem pair_response_coefficient_comparison (n : ℕ) :
    PowerSeries.coeff n sameMark≤PowerSeries.coeff n differentMark := by
  have h := congrArg (PowerSeries.coeff n) pair_difference_natural_series
  rw [map_sub,PowerSeries.coeff_map] at h
  have hn : (0 : ℚ)≤(PowerSeries.coeff n
      (PowerSeries.X*(1+sourceSeries (fun _ => (1 : ℕ)) 0)^3) : ℕ) := Nat.cast_nonneg _
  change (0 : ℚ)≤(Nat.castRingHom ℚ) _ at hn
  rw [←h] at hn
  exact sub_nonneg.mp hn

/-- The manuscript's same-color versus different-color inequality holds for the actual class sets. -/
theorem actual_pair_count_comparison (n : ℕ) {d e : Fin 3} (hde : d≠e) :
    Fintype.card (PairClass (Fin n) (Fin (2*n+1)) d d)≤
      Fintype.card (PairClass (Fin n) (Fin (2*n+1)) d e) := by
  have h := pair_response_coefficient_comparison n
  have hs : sourceMark d d=sameMark := source_mark_diagonal_uniform d 0
  have ht : sourceMark e d=differentMark := source_mark_distinct_uniform hde (by decide)
  rw [←hs,←ht,source_mark_pair_count,source_mark_pair_count] at h
  exact_mod_cast h

end KroneckerActualPairComparison
end

/- Original module: KroneckerActualSourceEulerEquation -/
section
set_option autoImplicit false
namespace KroneckerActualSourceEulerEquation
open KroneckerActualBranchLinearization KroneckerActualQuarticCounts
open KroneckerActualBranchSeries KroneckerFiniteBranchClasses



end KroneckerActualSourceEulerEquation
end

/- Original module: KroneckerActualPairCoefficientRatio -/
section
set_option autoImplicit false
namespace KroneckerActualPairCoefficientRatio
open KroneckerActualPairComparison KroneckerActualSourceEulerEquation KroneckerTwoMarkRationalSeries
open KroneckerTwoMarkResponseSystem KroneckerActualBranchLinearization KroneckerActualQuarticCounts
open KroneckerActualPairCountSeries KroneckerPairTreeClassCount
attribute [local instance] Classical.propDecidable

noncomputable def differenceSeries : PowerSeries ℚ := PowerSeries.X*(1+branchT)^3





end KroneckerActualPairCoefficientRatio
end

/- Original module: KroneckerPairMarkedLowerBound -/
section
set_option autoImplicit false
namespace KroneckerPairMarkedLowerBound
open KroneckerQuarticBinomialLower KroneckerSlotBinomialComparison KroneckerActualPairClosedCounts
open KroneckerPairTreeClassCount KroneckerActualPairComparison
attribute [local instance] Classical.propDecidable

theorem same_pair_sqrt_lower (j : ℕ) (hj : 0<j) (d : Fin 3) :
    (binomialLowerConstant/2)*(256/27:ℝ)^j/Real.sqrt j≤
      (Fintype.card (PairClass (Fin (j+1)) (Fin (2*(j+1)+1)) d d) : ℝ) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  have hc : (Fintype.card (PairClass (Fin (n+2)) (Fin (2*(n+2)+1)) d d) : ℝ)=
      2*((4*n+6).choose n : ℝ) := by exact_mod_cast actual_same_pair_count n d
  have hb := quartic_binomial_lower (n+1) (by omega)
  rw [show 4*(n+1)=4*n+4 by omega] at hb
  have hs := shifted_pair_binomial_lower n
  simp only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] at hb ⊢
  change (binomialLowerConstant/2)*(256/27:ℝ)^(n+1)/Real.sqrt (n+1)≤
    (Fintype.card (PairClass (Fin (n+2)) (Fin (2*(n+2)+1)) d d):ℝ)
  rw [hc]
  have he : (binomialLowerConstant/2)*(256/27:ℝ)^(n+1)/Real.sqrt (n+1)=
      (binomialLowerConstant*(256/27:ℝ)^(n+1)/Real.sqrt (n+1))/2 := by ring
  rw [he]
  linarith

/-- Both ordered pair-color choices satisfy the uniform j^(-1/2) lower scale. -/
theorem actual_pair_marked_uniform_lower : ∃ B : ℝ,0<B ∧
    ∀ j : ℕ,0<j → ∀ d e : Fin 3,
      B*(256/27:ℝ)^j*(j:ℝ)^(-1/2:ℝ)≤
        (Fintype.card (PairClass (Fin (j+1)) (Fin (2*(j+1)+1)) d e) : ℝ) := by
  refine ⟨binomialLowerConstant/2,div_pos binomial_lower_constant_pos (by norm_num),?_⟩
  intro j hj d e
  have hjR : (0:ℝ)<j := by exact_mod_cast hj
  have hp : (j:ℝ)^(-1/2:ℝ)=(Real.sqrt j)⁻¹ := by
    rw [show (-1/2:ℝ)=-(1/2) by norm_num,Real.rpow_neg hjR.le,←Real.sqrt_eq_rpow]
  rw [hp,←div_eq_mul_inv]
  apply (same_pair_sqrt_lower j hj d).trans
  by_cases hde : d=e
  · subst e; exact le_rfl
  · exact_mod_cast actual_pair_count_comparison (j+1) hde

end KroneckerPairMarkedLowerBound
end

/- Original module: KroneckerReflectedPairSlotCounts -/
section
set_option autoImplicit false
namespace KroneckerReflectedPairSlotCounts
open KroneckerReflectedSingleSlotCounts KroneckerFiniteColoredTables KroneckerSaturatedTableAction
open KroneckerRetainedVacantSlots KroneckerRetainedBlockSupport KroneckerSlotIsoTransport
open KroneckerTablePairMarks KroneckerMarkedSlotPairs KroneckerPairTreeClassCount
open KroneckerColoredIncidenceIso KroneckerTableRelabeling KroneckerTableIsomorphisms
open KroneckerMarkedReflectionClasses KroneckerReflectedMarkedIsomorphisms
open KroneckerSaturatedTreeDimensions KroneckerActualPairClosedCounts KroneckerPairMarkedLowerBound
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I] [Fintype J]

noncomputable def slotPairMarkEquiv (T : SaturatedTable I J) (d e : Fin 3) :
    OrderedMarks (fun p : ReflectedSlot T => p.1.2) d e ≃ {p // PairMark T.1 d e p} :=
  (markedSlotLeafEquiv (coloring T.1) T.2.2 d e).trans (pairMarkEquiv T.1 d e).symm

abbrev PairSlotObject (I J : Type) [Fintype I] [Fintype J] (d e : Fin 3) :=
  Σ T : SaturatedTable I J,OrderedMarks (fun p : ReflectedSlot T => p.1.2) d e

noncomputable def pairSlotObjectEquiv (d e : Fin 3) : PairSlotObject I J d e ≃ PairTable I J d e where
  toFun M := ⟨(M.1,(slotPairMarkEquiv M.1 d e M.2).1),(slotPairMarkEquiv M.1 d e M.2).2⟩
  invFun N := ⟨N.1.1,(slotPairMarkEquiv N.1.1 d e).symm ⟨N.1.2,N.2⟩⟩
  left_inv M := by
    rcases M with ⟨T,p⟩
    exact congrArg (fun q => (⟨T,q⟩ : PairSlotObject I J d e))
      ((slotPairMarkEquiv T d e).symm_apply_apply p)
  right_inv N := by
    apply Subtype.ext
    change (N.1.1,((slotPairMarkEquiv N.1.1 d e) ((slotPairMarkEquiv N.1.1 d e).symm ⟨N.1.2,N.2⟩)).1)=N.1
    rw [Equiv.apply_symm_apply]

def pairSlotSetoid (I J : Type) [Fintype I] [Fintype J] (d e : Fin 3) :
    Setoid (PairSlotObject I J d e) where
  r M N := ∃ f : ColoredIso (retainedColoring (coloring M.1.1))
      (retainedColoring (coloring N.1.1)),
      slotEquiv f M.2.1.1=N.2.1.1 ∧ slotEquiv f M.2.1.2=N.2.1.2
  iseqv := by
    constructor
    · intro M; exact ⟨1,rfl,rfl⟩
    · rintro M N ⟨f,hf,hg⟩
      refine ⟨f.symm,?_,?_⟩
      · rw [←hf]
        apply Subtype.ext
        exact Prod.ext (f.sink.symm_apply_apply _) rfl
      · rw [←hg]
        apply Subtype.ext
        exact Prod.ext (f.sink.symm_apply_apply _) rfl
    · rintro M N P ⟨f,hf,hf'⟩ ⟨g,hg,hg'⟩
      refine ⟨f.trans g,?_,?_⟩
      · change slotEquiv g (slotEquiv f M.2.1.1)=P.2.1.1
        rw [hf,hg]
      · change slotEquiv g (slotEquiv f M.2.1.2)=P.2.1.2
        rw [hf',hg']

abbrev PairSlotClass (I J : Type) [Fintype I] [Fintype J] (d e : Fin 3) :=
  Quotient (pairSlotSetoid I J d e)

noncomputable instance (d e : Fin 3) : Fintype (PairSlotClass I J d e) := Fintype.ofFinite _

theorem pair_orbit_iff_pointed (d e : Fin 3) (M N : PairTable I J d e) :
    (∃ p : Equiv.Perm I × Equiv.Perm J,p • M=N) ↔
    ∃ f : ColoredIso (coloring M.1.1.1) (coloring N.1.1.1),
      f.sink M.1.2.1=N.1.2.1 ∧ f.sink M.1.2.2=N.1.2.2 := by
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨relabelIso p M.1.1.1,rfl,rfl⟩
  · rintro ⟨f,hf,hg⟩
    refine ⟨(f.source,f.sink),Subtype.ext (Prod.ext ?_ (Prod.ext hf hg))⟩
    exact Subtype.ext ((relabel_eq_iff _ _ _).mpr (iso_preserves_code _ _ f))

theorem pair_class_eq_iff (d e : Fin 3) (M N : PairTable I J d e) :
    (Quotient.mk'' M : PairClass I J d e)=Quotient.mk'' N ↔
    ∃ f : ColoredIso (coloring M.1.1.1) (coloring N.1.1.1),
      f.sink M.1.2.1=N.1.2.1 ∧ f.sink M.1.2.2=N.1.2.2 := by
  rw [Quotient.eq]
  change (∃ p : Equiv.Perm I × Equiv.Perm J,p • N=M) ↔ _
  rw [pair_orbit_iff_pointed]
  constructor
  · rintro ⟨f,hf,hg⟩
    exact ⟨f.symm,by change f.sink.symm M.1.2.1=N.1.2.1; rw [←hf,Equiv.symm_apply_apply],
      by change f.sink.symm M.1.2.2=N.1.2.2; rw [←hg,Equiv.symm_apply_apply]⟩
  · rintro ⟨f,hf,hg⟩
    exact ⟨f.symm,by change f.sink.symm N.1.2.1=M.1.2.1; rw [←hf,Equiv.symm_apply_apply],
      by change f.sink.symm N.1.2.2=M.1.2.2; rw [←hg,Equiv.symm_apply_apply]⟩

variable [Nonempty I] [Nonempty J]

theorem pair_slot_relation_iff (d e : Fin 3) (M N : PairSlotObject I J d e) :
    pairSlotSetoid I J d e M N ↔
      (Quotient.mk'' (pairSlotObjectEquiv d e M) : PairClass I J d e)=
        Quotient.mk'' (pairSlotObjectEquiv d e N) := by
  rw [pair_class_eq_iff]
  have h := marked_reflection_isomorphism_iff M.1.2.2 N.1.2.2
    (saturated_sink_degree_positive _ M.1.2.1) (saturated_sink_degree_positive _ N.1.2.1)
    (fun b : Bool => Bool.rec M.2.1.1 M.2.1.2 b)
    (fun b : Bool => Bool.rec N.2.1.1 N.2.1.2 b)
  constructor
  · rintro ⟨f,hf,hg⟩
    obtain ⟨g,hg'⟩ := h.mp ⟨f,by intro b; cases b; exact hf; exact hg⟩
    exact ⟨g,hg' false,hg' true⟩
  · rintro ⟨f,hf,hg⟩
    obtain ⟨g,hg'⟩ := h.mpr ⟨f,by intro b; cases b; exact hf; exact hg⟩
    exact ⟨g,hg' false,hg' true⟩

/-- Ordered, distinct, color-prescribed pairs survive reflection with exactly the same quotient. -/
noncomputable def pairSlotClassEquiv (d e : Fin 3) :
    PairSlotClass I J d e ≃ PairClass I J d e :=
  Quotient.congr (pairSlotObjectEquiv d e) (fun M N =>
    (pair_slot_relation_iff d e M N).trans Quotient.eq)

theorem pair_slot_cardinality (d e : Fin 3) :
    Fintype.card (PairSlotClass I J d e)=Fintype.card (PairClass I J d e) := by
  simp only [←Nat.card_eq_fintype_card]
  exact Nat.card_congr (pairSlotClassEquiv d e)





theorem reflected_pair_slot_uniform_lower : ∃ B : ℝ,0<B ∧
    ∀ j : ℕ,0<j → ∀ d e : Fin 3,
      B*(256/27:ℝ)^j*(j:ℝ)^(-1/2:ℝ)≤
        (Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d e) : ℝ) := by
  obtain ⟨B,hB,h⟩ := actual_pair_marked_uniform_lower
  refine ⟨B,hB,?_⟩
  intro j hj d e
  have hc := pair_slot_cardinality (I:=Fin (j+1)) (J:=Fin (2*(j+1)+1)) d e
  have h' := h j hj d e
  simp only [←Nat.card_eq_fintype_card] at hc h' ⊢
  rw [hc]
  exact h'

end KroneckerReflectedPairSlotCounts
end
