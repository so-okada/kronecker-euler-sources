import KroneckerActualBranchSeries
import KroneckerGradedMarkedBranchCounts

section

set_option autoImplicit false
namespace KroneckerTreeColorPermutations
open KroneckerFiniteColoredTables KroneckerSaturatedTableAction KroneckerBipartiteIncidence
open KroneckerTableLeafMarks KroneckerTablePairMarks KroneckerTableRelabeling
attribute [local instance] Classical.propDecidable

variable {I J : Type}

def recolor (s : Equiv.Perm (Fin 3)) (T : ColoredTable I J) : ColoredTable I J where
  code i j := (T.code i j).map s
  atSource := by
    intro i j k d hj hk
    have hh := Option.map_injective s.injective (hj.trans hk.symm)
    cases hc : T.code i j with
    | none => simp [hc] at hj
    | some c => exact T.atSource i j k c hc (hh.symm.trans hc)
  atSink := by
    intro i k j d hi hk
    have hh := Option.map_injective s.injective (hi.trans hk.symm)
    cases hc : T.code i j with
    | none => simp [hc] at hi
    | some c => exact T.atSink i k j c hc (hh.symm.trans hc)

theorem recolor_incidence (s : Equiv.Perm (Fin 3)) (T : ColoredTable I J) (i : I) (j : J) :
    Incidence (recolor s T) i j ↔ Incidence T i j := by
  cases h : T.code i j <;> simp [Incidence,recolor,h]

theorem recolor_graph (s : Equiv.Perm (Fin 3)) (T : ColoredTable I J) :
    incidenceGraph (Incidence (recolor s T))=incidenceGraph (Incidence T) := by
  congr 1
  funext i j
  exact propext (recolor_incidence s T i j)

theorem recolor_inverse (s : Equiv.Perm (Fin 3)) (T : ColoredTable I J) :
    recolor s.symm (recolor s T)=T := by
  apply table_ext
  funext i j
  cases h : T.code i j <;> simp [recolor,h]

theorem recolor_relabel (s : Equiv.Perm (Fin 3)) (p : Equiv.Perm I × Equiv.Perm J)
    (T : ColoredTable I J) : recolor s (relabel p T)=relabel p (recolor s T) := table_ext rfl

variable [Fintype I] [Fintype J]

def recolorTree (s : Equiv.Perm (Fin 3)) (T : SaturatedTable I J) : SaturatedTable I J :=
  ⟨recolor s T.1,by rw [recolor_graph]; exact T.2.1,by
    intro i
    have he : {j // Incidence (recolor s T.1) i j} ≃ {j // Incidence T.1 i j} :=
      Equiv.subtypeEquiv (Equiv.refl J) (fun j => recolor_incidence s T.1 i j)
    exact (Fintype.card_congr he).trans (T.2.2 i)⟩

def recolorTreeEquiv (s : Equiv.Perm (Fin 3)) : SaturatedTable I J ≃ SaturatedTable I J where
  toFun := recolorTree s
  invFun := recolorTree s.symm
  left_inv T := Subtype.ext (recolor_inverse s T.1)
  right_inv T := Subtype.ext (recolor_inverse s.symm T.1)

omit [Fintype I] in
theorem recolor_tree_equivariant (s : Equiv.Perm (Fin 3))
    (p : Equiv.Perm I × Equiv.Perm J) (T : SaturatedTable I J) :
    recolorTree s (p • T)=p • recolorTree s T := Subtype.ext (recolor_relabel s p T.1)

omit [Fintype J] in
theorem recolor_leaf_mark (s : Equiv.Perm (Fin 3)) (T : ColoredTable I J) (d : Fin 3) (j : J) :
    LeafMark (recolor s T) (s d) j ↔ LeafMark T d j := by
  have hc : Fintype.card {i // Incidence (recolor s T) i j}=Fintype.card {i // Incidence T i j} :=
    Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl I) (fun i => recolor_incidence s T i j))
  unfold LeafMark
  rw [hc]
  apply and_congr Iff.rfl
  apply exists_congr
  intro i
  change (T.code i j).map s=(some d).map s ↔ T.code i j=some d
  exact (Option.map_injective s.injective).eq_iff

omit [Fintype J] in
theorem recolor_pair_mark (s : Equiv.Perm (Fin 3)) (T : ColoredTable I J) (d e : Fin 3) (p : J × J) :
    PairMark (recolor s T) (s d) (s e) p ↔ PairMark T d e p := by
  simp only [PairMark,recolor_leaf_mark]

end KroneckerTreeColorPermutations
end

section

/- Original module: KroneckerMarkedClassColorSymmetry -/
section
set_option autoImplicit false
namespace KroneckerMarkedClassColorSymmetry
open KroneckerTreeColorPermutations KroneckerTableLeafMarks KroneckerTablePairMarks
open KroneckerMarkedTableAction KroneckerMarkedTreeClassCount KroneckerPairTreeClassCount
attribute [local instance] Classical.propDecidable

def equivariantOrbitEquiv {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (e : X ≃ Y) (he : ∀ (g : G) (x : X),e (g • x)=g • e x) :
    Quotient (MulAction.orbitRel G X) ≃ Quotient (MulAction.orbitRel G Y) :=
  Quotient.congr e (by
    intro a b
    constructor
    · rintro ⟨g,hg⟩
      exact ⟨g,(he g b).symm.trans (congrArg e hg)⟩
    · rintro ⟨g,hg⟩
      exact ⟨g,e.injective ((he g b).trans hg)⟩)

variable {I J : Type} [Fintype I] [Fintype J]

def markedColorEquiv (s : Equiv.Perm (Fin 3)) (d : Fin 3) :
    MarkedTable I J d ≃ MarkedTable I J (s d) :=
  Equiv.subtypeEquiv (Equiv.prodCongr (recolorTreeEquiv s) (Equiv.refl J))
    (fun M => (recolor_leaf_mark s M.1.1 d M.2).symm)

noncomputable def markedClassColorEquiv (s : Equiv.Perm (Fin 3)) (d : Fin 3) :
    MarkedClass I J d ≃ MarkedClass I J (s d) :=
  equivariantOrbitEquiv (markedColorEquiv s d) (by
    intro p M
    apply Subtype.ext
    exact Prod.ext (recolor_tree_equivariant s p M.1.1) rfl)

def pairColorEquiv (s : Equiv.Perm (Fin 3)) (d e : Fin 3) :
    PairTable I J d e ≃ PairTable I J (s d) (s e) :=
  Equiv.subtypeEquiv (Equiv.prodCongr (recolorTreeEquiv s) (Equiv.refl (J × J)))
    (fun M => (recolor_pair_mark s M.1.1 d e M.2).symm)

noncomputable def pairClassColorEquiv (s : Equiv.Perm (Fin 3)) (d e : Fin 3) :
    PairClass I J d e ≃ PairClass I J (s d) (s e) :=
  equivariantOrbitEquiv (pairColorEquiv s d e) (by
    intro p M
    apply Subtype.ext
    exact Prod.ext (recolor_tree_equivariant s p M.1.1) rfl)

theorem single_color_count_uniform (d e : Fin 3) :
    Fintype.card (MarkedClass I J d)=Fintype.card (MarkedClass I J e) := by
  simpa using Fintype.card_congr (markedClassColorEquiv (I:=I) (J:=J) (Equiv.swap d e) d)

theorem equal_color_count_uniform (d e : Fin 3) :
    Fintype.card (PairClass I J d d)=Fintype.card (PairClass I J e e) := by
  simpa using Fintype.card_congr (pairClassColorEquiv (I:=I) (J:=J) (Equiv.swap d e) d d)

theorem two_color_permutation {d e a b : Fin 3} (hde : d≠e) (hab : a≠b) :
    ∃ s : Equiv.Perm (Fin 3),s d=a ∧ s e=b := by
  let s := Equiv.swap d a
  have hs : s d=a := Equiv.swap_apply_left d a
  have hsa : s e≠a := by
    intro h
    exact hde (s.injective (hs.trans h.symm))
  refine ⟨s.trans (Equiv.swap (s e) b),?_,?_⟩
  · change Equiv.swap (s e) b (s d)=a
    rw [hs]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hsa) hab
  · exact Equiv.swap_apply_left _ _

theorem distinct_color_count_uniform {d e a b : Fin 3} (hde : d≠e) (hab : a≠b) :
    Fintype.card (PairClass I J d e)=Fintype.card (PairClass I J a b) := by
  obtain ⟨s,hs,ht⟩ := two_color_permutation hde hab
  simpa only [hs,ht] using Fintype.card_congr (pairClassColorEquiv (I:=I) (J:=J) s d e)

end KroneckerMarkedClassColorSymmetry
end

/- Original module: KroneckerSinkSeriesEquation -/
section
set_option autoImplicit false
namespace KroneckerSinkSeriesEquation
open KroneckerFiniteBranchClasses KroneckerFiniteDegreePartitions KroneckerBranchClassWeights
open KroneckerSinkClassConvolution KroneckerSinkClassAssembly KroneckerSourceClassAssembly
open KroneckerPartitionCauchyProduct KroneckerActualBranchSeries
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {R : Type*} [CommSemiring R]

theorem sink_weight_subset_convolution (d : Fin 3) (n : ℕ) (y : Fin 3 → R) :
    (∑ q : SinkDegreeClass n d,sinkClassWeight 1 y q)=
      ∑ s : Finset (OtherColors d),(if IsEmpty s then y d else 1)*
        ∑ a : DegreePartition s n,∏ k,∑ q : SourceDegreeClass (a.1 k) (occupiedColor s k),
          sourceClassWeight 1 y q := by
  rw [sink_class_weight_convolution]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : IsEmpty s
  · let := hs
    simp
  · simp only [ite_eq_right hs,one_mul]

/-- The empty sink has weight y_d; every nonempty occupied subset has the product weight. -/
theorem sink_series_subset_equation (y : Fin 3 → R) (d : Fin 3) :
    sinkSeries y d=∑ s : Finset (OtherColors d),
      PowerSeries.C (if IsEmpty s then y d else 1) *
        ∏ k : s,sourceSeries y (occupiedColor s k) := by
  apply PowerSeries.ext
  intro n
  rw [sink_series_coeff,sink_weight_subset_convolution,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [PowerSeries.coeff_C_mul,coeff_product_partitions]
  simp only [source_series_coeff]

end KroneckerSinkSeriesEquation
end

/- Original module: KroneckerOccupiedSubsetExpansion -/
section
set_option autoImplicit false
namespace KroneckerOccupiedSubsetExpansion
open KroneckerActualBranchSeries KroneckerSinkSeriesEquation KroneckerSourceClassAssembly
open KroneckerSinkClassAssembly
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K : Type} [Fintype K] {R : Type*} [CommSemiring R]

theorem finite_subset_expansion (f : K → R) :
    (∑ s : Finset K,∏ k : s,f k.1)=∏ k,(1+f k) := by
  classical
  have hu : (Finset.univ : Finset K).powerset=Finset.univ := by ext; simp
  rw [Finset.prod_one_add,hu]
  apply Finset.sum_congr rfl
  intro s _
  exact Finset.prod_coe_sort s f

theorem occupied_subset_expansion (a : R) (f : K → R) :
    (∑ s : Finset K,if IsEmpty s then a else ∏ k : s,f k.1)+1=
      a+∏ k,(1+f k) := by
  classical
  simp only [Finset.isEmpty_coe_sort]
  calc
    _ = ∑ s : Finset K,((if s=∅ then a else ∏ k : s,f k.1)+(if s=∅ then 1 else 0)) := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    _ = ∑ s : Finset K,((∏ k : s,f k.1)+(if s=∅ then a else 0)) := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : s=∅
      · subst s; simp [add_comm]
      · simp [hs]
    _ = a+∏ k,(1+f k) := by
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
        finite_subset_expansion,add_comm]

/-- The corrected empty-root weight yields the full sink grammar over any commutative semiring. -/
theorem sink_series_product_equation (y : Fin 3 → R) (d : Fin 3) :
    sinkSeries y d+1=PowerSeries.C (y d)+∏ k : OtherColors d,(1+sourceSeries y k.1) := by
  rw [sink_series_subset_equation]
  have h : (∑ s : Finset (OtherColors d),
      PowerSeries.C (if IsEmpty s then y d else 1)*∏ k : s,sourceSeries y (occupiedColor s k))=
      ∑ s : Finset (OtherColors d),if IsEmpty s then PowerSeries.C (y d)
        else ∏ k : s,sourceSeries y k.1.1 := by
    classical
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : IsEmpty s
    · let := hs
      simp only [ite_eq_left hs]
      simp
    · simp only [ite_eq_right hs,map_one,one_mul,occupiedColor]
  rw [h]
  exact occupied_subset_expansion (PowerSeries.C (y d)) (fun k : OtherColors d => sourceSeries y k.1)

theorem sink_series_at_one_equation (d : Fin 3) :
    sinkSeries (fun _ => (1 : R)) d=∏ k : OtherColors d,(1+sourceSeries (fun _ => (1 : R)) k.1) := by
  rw [sink_series_subset_equation]
  simp only [ite_self,map_one,one_mul,occupiedColor]
  exact finite_subset_expansion (fun k : OtherColors d => sourceSeries (fun _ => (1 : R)) k.1)

end KroneckerOccupiedSubsetExpansion
end

/- Original module: KroneckerThreeColorBranchGrammar -/
section
set_option autoImplicit false
namespace KroneckerThreeColorBranchGrammar
open KroneckerActualBranchSeries KroneckerSourceClassAssembly KroneckerOccupiedSubsetExpansion
open scoped BigOperators

def nextColor (d : Fin 3) : Fin 3 := d+1
def lastColor (d : Fin 3) : Fin 3 := d+2

theorem next_color_ne (d : Fin 3) : nextColor d≠d := by fin_cases d <;> decide
theorem last_color_ne (d : Fin 3) : lastColor d≠d := by fin_cases d <;> decide
theorem other_colors_distinct (d : Fin 3) : nextColor d≠lastColor d := by fin_cases d <;> decide

theorem other_colors_pair (d : Fin 3) :
    (Finset.univ : Finset (OtherColors d))=
      {⟨nextColor d,next_color_ne d⟩,⟨lastColor d,last_color_ne d⟩} := by
  fin_cases d <;> decide

theorem other_colors_product {R : Type*} [CommMonoid R] (g : Fin 3 → R) (d : Fin 3) :
    (∏ k : OtherColors d,g k.1)=g (nextColor d)*g (lastColor d) := by
  rw [other_colors_pair]
  have hn : (⟨nextColor d,next_color_ne d⟩ : OtherColors d)≠⟨lastColor d,last_color_ne d⟩ :=
    fun h => other_colors_distinct d (congrArg Subtype.val h)
  simp [hn]

variable {R : Type*} [CommRing R]

/-- The exact two-child source equation for the actual branch enumerators. -/
theorem actual_source_grammar (y : Fin 3 → R) (d : Fin 3) :
    sourceSeries y d=PowerSeries.X * sinkSeries y (nextColor d)*sinkSeries y (lastColor d) := by
  rw [source_series_equation,other_colors_product,mul_assoc]

/-- The empty, one-child and two-child sink cases, without an assumed counting formula. -/
theorem actual_sink_grammar (y : Fin 3 → R) (d : Fin 3) :
    sinkSeries y d=PowerSeries.C (y d)+sourceSeries y (nextColor d)+sourceSeries y (lastColor d)+
      sourceSeries y (nextColor d)*sourceSeries y (lastColor d) := by
  have h := sink_series_product_equation y d
  rw [other_colors_product (fun e => 1+sourceSeries y e) d] at h
  linear_combination h

end KroneckerThreeColorBranchGrammar
end

/- Original module: KroneckerActualQuarticCounts -/
section
set_option autoImplicit false
namespace KroneckerActualQuarticCounts
open KroneckerFiniteBranchClasses KroneckerGradedMarkedBranchCounts KroneckerMarkedClassColorSymmetry
open KroneckerActualBranchSeries KroneckerOccupiedSubsetExpansion KroneckerThreeColorBranchGrammar
open scoped BigOperators

theorem source_degree_count_uniform (n : ℕ) (d e : Fin 3) :
    Fintype.card (SourceDegreeClass n d)=Fintype.card (SourceDegreeClass n e) := by
  have hd := source_degree_marked_count n d
  have he := source_degree_marked_count n e
  have hc := single_color_count_uniform (I:=Fin n) (J:=Fin (2*n+1)) d e
  simp only [←Nat.card_eq_fintype_card] at hd he hc ⊢
  exact hd.trans (hc.trans he.symm)

variable {R : Type*} [CommSemiring R]

theorem source_series_at_one_uniform (d e : Fin 3) :
    sourceSeries (fun _ => (1 : R)) d=sourceSeries (fun _ => (1 : R)) e := by
  apply PowerSeries.ext
  intro n
  rw [source_series_counts,source_series_counts,source_degree_count_uniform n d e]

theorem sink_series_at_one_square (d e : Fin 3) :
    sinkSeries (fun _ => (1 : R)) d=(1+sourceSeries (fun _ => (1 : R)) e)^2 := by
  rw [sink_series_at_one_equation,other_colors_product (fun k => 1+sourceSeries (fun _ => (1 : R)) k) d,
    source_series_at_one_uniform (nextColor d) e,source_series_at_one_uniform (lastColor d) e,pow_two]

/-- The quartic equation is now proved for the genuine unweighted branch class enumerator. -/
theorem actual_source_quartic (d : Fin 3) :
    sourceSeries (fun _ => (1 : R)) d=PowerSeries.X*(1+sourceSeries (fun _ => (1 : R)) d)^4 := by
  calc
    _ = PowerSeries.X * ∏ k : KroneckerSourceClassAssembly.OtherColors d,
        sinkSeries (fun _ => (1 : R)) k.1 := source_series_equation _ d
    _ = _ := by
      rw [other_colors_product,sink_series_at_one_square (nextColor d) d,
        sink_series_at_one_square (lastColor d) d]
      ring

end KroneckerActualQuarticCounts
end

/- Original module: KroneckerBranchWeightNaturality -/
section
set_option autoImplicit false
namespace KroneckerBranchWeightNaturality
open KroneckerFiniteBranchClasses KroneckerBranchClassWeights KroneckerBranchWeights
open KroneckerGradedProfileWeights KroneckerActualBranchSeries
open scoped BigOperators

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

theorem source_class_weight_map (f : R →+* S) (x : R) (y : Fin 3 → R)
    (q : KroneckerBranchClassRelations.SourceClass I J d) :
    f (sourceClassWeight x y q)=sourceClassWeight (f x) (fun d => f (y d)) q := by
  induction q using Quotient.inductionOn with | _ T =>
    simp [sourceClassWeight,sourceWeight,gradedWeight]

theorem sink_class_weight_map (f : R →+* S) (x : R) (y : Fin 3 → R)
    (q : KroneckerBranchClassRelations.SinkClass I J d) :
    f (sinkClassWeight x y q)=sinkClassWeight (f x) (fun d => f (y d)) q := by
  induction q using Quotient.inductionOn with | _ T =>
    simp [sinkClassWeight,sinkWeight,gradedWeight]

/-- Evaluation and coefficient changes commute with the actual finite class enumerators. -/
theorem source_series_map (f : R →+* S) (y : Fin 3 → R) (e : Fin 3) :
    PowerSeries.map f (sourceSeries y e)=sourceSeries (fun d => f (y d)) e := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map,source_series_coeff,map_sum,source_class_weight_map,map_one]

theorem sink_series_map (f : R →+* S) (y : Fin 3 → R) (e : Fin 3) :
    PowerSeries.map f (sinkSeries y e)=sinkSeries (fun d => f (y d)) e := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map,sink_series_coeff,map_sum,sink_class_weight_map,map_one]

end KroneckerBranchWeightNaturality
end

/- Original module: KroneckerCoefficientMarkDerivative -/
section
set_option autoImplicit false
namespace KroneckerCoefficientMarkDerivative
open scoped BigOperators

abbrev LeafPoly := MvPolynomial (Fin 3) ℚ
noncomputable def evaluate : PowerSeries LeafPoly →+* PowerSeries ℚ :=
  PowerSeries.map (MvPolynomial.eval (fun _ => 1))

/-- Differentiate each finite leaf polynomial, then evaluate every leaf variable at one. -/
noncomputable def markDerivative (d : Fin 3) (F : PowerSeries LeafPoly) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => MvPolynomial.eval (fun _ => 1)
    (MvPolynomial.pderiv d (PowerSeries.coeff n F)))

theorem mark_derivative_coeff (d : Fin 3) (F : PowerSeries LeafPoly) (n : ℕ) :
    PowerSeries.coeff n (markDerivative d F)=
      MvPolynomial.eval (fun _ => 1) (MvPolynomial.pderiv d (PowerSeries.coeff n F)) :=
  PowerSeries.coeff_mk n _

theorem mark_derivative_add (d : Fin 3) (F G : PowerSeries LeafPoly) :
    markDerivative d (F+G)=markDerivative d F+markDerivative d G := by
  apply PowerSeries.ext
  intro n
  simp only [mark_derivative_coeff,map_add]

/-- Leibniz's rule commutes with the finite Cauchy coefficient sums. -/
theorem mark_derivative_mul (d : Fin 3) (F G : PowerSeries LeafPoly) :
    markDerivative d (F*G)=markDerivative d F*evaluate G+evaluate F*markDerivative d G := by
  apply PowerSeries.ext
  intro n
  simp only [mark_derivative_coeff,PowerSeries.coeff_mul,map_sum,Derivation.leibniz,map_add,
    smul_eq_mul,map_mul,Finset.sum_add_distrib,evaluate,PowerSeries.coeff_map]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact mul_comm _ _

theorem mark_derivative_C (d : Fin 3) (p : LeafPoly) :
    markDerivative d (PowerSeries.C p)=PowerSeries.C (MvPolynomial.eval (fun _ => 1) (MvPolynomial.pderiv d p)) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n=0
  · subst n
    simp only [mark_derivative_coeff,PowerSeries.coeff_zero_C]
  · simp [mark_derivative_coeff,PowerSeries.coeff_C,hn]

theorem mark_derivative_X_mul (d : Fin 3) (F : PowerSeries LeafPoly) :
    markDerivative d (PowerSeries.X*F)=PowerSeries.X*markDerivative d F := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [mark_derivative_coeff]
  | succ n => simp only [mark_derivative_coeff,PowerSeries.coeff_succ_X_mul]

end KroneckerCoefficientMarkDerivative
end

/- Original module: KroneckerActualBranchLinearization -/
section
set_option autoImplicit false
namespace KroneckerActualBranchLinearization
open KroneckerCoefficientMarkDerivative KroneckerBranchWeightNaturality KroneckerActualBranchSeries
open KroneckerActualQuarticCounts KroneckerThreeColorBranchGrammar

noncomputable def branchT : PowerSeries ℚ := sourceSeries (fun _ => 1) 0
noncomputable def sourceMark (e d : Fin 3) : PowerSeries ℚ :=
  markDerivative e (sourceSeries (MvPolynomial.X : Fin 3 → LeafPoly) d)
noncomputable def sinkMark (e d : Fin 3) : PowerSeries ℚ :=
  markDerivative e (sinkSeries (MvPolynomial.X : Fin 3 → LeafPoly) d)

theorem evaluate_source_branch (d : Fin 3) :
    evaluate (sourceSeries (MvPolynomial.X : Fin 3 → LeafPoly) d)=branchT := by
  rw [evaluate,source_series_map]
  simp only [MvPolynomial.eval_X]
  exact source_series_at_one_uniform d 0

theorem evaluate_sink_branch (d : Fin 3) :
    evaluate (sinkSeries (MvPolynomial.X : Fin 3 → LeafPoly) d)=(1+branchT)^2 := by
  rw [evaluate,sink_series_map]
  simp only [MvPolynomial.eval_X]
  exact sink_series_at_one_square d 0

theorem derivative_leaf_constant (e d : Fin 3) :
    markDerivative e (PowerSeries.C (MvPolynomial.X d : LeafPoly))=
      PowerSeries.C (if e=d then (1 : ℚ) else 0) := by
  rw [mark_derivative_C]
  by_cases h : e=d
  · subst d
    simp
  · simp [MvPolynomial.pderiv_X,h,Ne.symm h]

/-- Differentiation of the actual source grammar gives its full linear response. -/
theorem source_mark_equation (e d : Fin 3) :
    sourceMark e d=PowerSeries.X*((sinkMark e (nextColor d))*(1+branchT)^2+
      (1+branchT)^2*sinkMark e (lastColor d)) := by
  have h := actual_source_grammar (MvPolynomial.X : Fin 3 → LeafPoly) d
  rw [mul_assoc] at h
  have hd := congrArg (markDerivative e) h
  rw [mark_derivative_X_mul,mark_derivative_mul] at hd
  simpa only [evaluate_sink_branch,sourceMark,sinkMark] using hd

/-- The inhomogeneous term is one precisely when the marked leaf color is the parent color. -/
theorem sink_mark_equation (e d : Fin 3) :
    sinkMark e d=PowerSeries.C (if e=d then (1 : ℚ) else 0)+
      (1+branchT)*(sourceMark e (nextColor d)+sourceMark e (lastColor d)) := by
  have h := congrArg (markDerivative e) (actual_sink_grammar (MvPolynomial.X : Fin 3 → LeafPoly) d)
  simp only [mark_derivative_add,mark_derivative_mul,derivative_leaf_constant,
    evaluate_source_branch] at h
  change sinkMark e d=_ at h
  rw [h]
  change PowerSeries.C (if e=d then (1 : ℚ) else 0)+sourceMark e (nextColor d)+
    sourceMark e (lastColor d)+(sourceMark e (nextColor d)*branchT+branchT*sourceMark e (lastColor d))=_
  ring

end KroneckerActualBranchLinearization
end
end

