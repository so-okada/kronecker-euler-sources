import KroneckerExchangeColorCorrespondence

/-! Geometric domains, vertical ordinals, and boundary balances for the
literal repair definition. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerRepairGeometry
open KroneckerStack KroneckerMarkedDebtIndex KroneckerColoring KroneckerColoredEdges
open KroneckerColoredExchangeRelation KroneckerCanonicalExchange
open KroneckerExchangeIntermediateLemma KroneckerRepairIndexCorrespondence
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerExplicitShellCorrespondence
open KroneckerManuscriptExchangeDefinitions KroneckerExchangeRepairCorrespondence
open KroneckerExchangeTransport

def candidateOrdinals (d i : ℕ) (ys : List KroneckerStack.Edge) : Set ℕ :=
  {j | ∃ p q, i+2 ≤ p ∧ ys[p]? = some (.V q) ∧
    counter d ((ys.drop (i+2)).take (p-(i+2))) = 0 ∧
    j = verticalCount (ys.take (p+1))}

theorem position_vertical_ordinal {m i d : ℕ} {right : Bool}
    {xs ys : List (CEdge m)} {p : Palette m} (he : Exchange right i xs ys p d) :
    ∃ h, (swapEdges i (coloredWord xs))[repairPosition right i (coloredWord xs)]? = some (.V h) ∧
      verticalCount ((swapEdges i (coloredWord xs)).take
        (repairPosition right i (coloredWord xs)+1)) = changeIndex right i (coloredWord xs)+1 := by
  cases he with
  | right pre hc =>
      have hl : pre.length = (pre.map uncolor).length := by simp
      cases hc with
      | zero q es hx hq hcol =>
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true]
          rw [hl,swapEdges_pair (pre.map uncolor),repairPosition_right (pre.map uncolor)]
          simp only [hx,↓reduceIte]
          refine ⟨grade p,by simp,?_⟩
          rw [changeIndex_prefix]
          simp [changeIndex,List.take_append,verticalCount_append,verticalCount]
          rw [List.take_of_length_le (by simp)]
      | @positive y q es ds n j hx hy hi hr =>
          rename_i x y es ds
          have hj := KroneckerVerticalRepair.repair_original
            (KroneckerColoredRepair.colored_repair_word hr)
          simp only [coloredWord] at hi hj
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true]
          rw [hl,swapEdges_pair (pre.map uncolor),repairPosition_right (pre.map uncolor)]
          simp only [hx,Nat.add_sub_cancel,Nat.add_eq_zero_iff,one_ne_zero,and_false,
            ite_false,hi,Option.getD_some]
          refine ⟨grade p,?_,?_⟩
          · exact exchanged_get (pre.map uncolor) (grade y) (n+1) j (es.map uncolor) |>.trans hj
          · have hf := (markedIndex_iff_first_candidate n (es.map uncolor) j).mp hi
            rw [positive_changeIndex_ordinal (pre.map uncolor) (es.map uncolor) n (grade y) j hf.1 hf.2]
            exact exchanged_ordinal (pre.map uncolor) (grade y) (n+1) j (grade p) (es.map uncolor) hj
  | @left pre x y q es d hc =>
      have hl : pre.length = (pre.map uncolor).length := by simp
      simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
        Bool.false_eq_true,ite_false,ite_true]
      rw [hl,swapEdges_pair (pre.map uncolor)]
      simp only [repairPosition,Bool.false_eq_true,ite_false]
      refine ⟨grade p,by simp,?_⟩
      rw [changeIndex_prefix]
      simp [changeIndex,List.take_append,verticalCount_append,verticalCount,Nat.add_assoc]
      rw [List.take_of_length_le (by simp)]

theorem positive_index_least {m i d : ℕ} {xs ys : List (CEdge m)} {p : Palette m}
    (he : Exchange true i xs ys p d)
    (hg : 0 < ((coloredWord xs)[i]?.getD (.H 0)).grade) :
    IsLeast (candidateOrdinals (((coloredWord xs)[i]?.getD (.H 0)).grade-1) i
      (swapEdges i (coloredWord xs))) (changeIndex true i (coloredWord xs)+1) := by
  cases he with
  | right pre hc =>
      have hl : pre.length = (pre.map uncolor).length := by simp
      cases hc with
      | zero q es hx hq hcol =>
          simp [coloredWord,uncolor,paint,hx,KroneckerStack.Edge.grade] at hg
      | @positive y q es ds n j hx hy hi hr =>
          rename_i x y es ds
          simp only [coloredWord,List.map_append,List.map_cons,uncolor,paint,
            Bool.false_eq_true,ite_false,ite_true]
          rw [hl,swapEdges_pair (pre.map uncolor)]
          simp only [List.getElem?_append_right le_rfl,Nat.sub_self,
            List.getElem?_cons_zero,Option.getD_some,Edge.grade,hx,Nat.add_sub_cancel]
          change IsLeast (literalOrdinals n (pre.map uncolor) (grade y) (n+1) (es.map uncolor)) _
          rw [literal_eq_paperOrdinals]
          have hf := (markedIndex_iff_first_candidate n (es.map uncolor) j).mp hi
          exact positive_changeIndex_isLeast (pre.map uncolor) (es.map uncolor) n (grade y) j hf.1 hf.2

theorem wordList_credit (E : ℕ → KroneckerStack.Edge) (n : ℕ) :
    credit (KroneckerPaperConnected.wordList E n) = KroneckerCompatibility.balance E n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [KroneckerPaperConnected.wordList,List.range'_concat,credit,
        KroneckerCompatibility.balance,KroneckerCompatibility.walk] using
        congrArg (fun b => b+(E n).credit) ih

/-- The finite prefix sums in literalDelta are the paper's actual boundary balances. -/
theorem gradedWord_boundary (X : TNEPath) (f : Grading X) (i : Fin (X.steps.length+1)) :
    credit ((gradedWord X f).take i.val) = bBal f i := by
  rw [gradedWord_trace]
  unfold KroneckerPaperConnected.wordList
  rw [←List.map_take,List.take_range'_of_length_ge (by have := i.isLt; omega)]
  exact wordList_credit (geometricTrace f) i.val

/-- Every grading in the manuscript's admissible domain has a colored representative. -/
theorem colored_input (ξ : AdjShellExch) (f : Grading ξ.X)
    (hf : ConnectedGrading f) (hb : ∀ e, f e ≤ 3) :
    ∃ a : KroneckerAdjacentExchangeLemma.ColoredSet ξ.X, a.2.val.1 = f := by
  obtain ⟨c⟩ := (colorFiber_nonempty_iff f).mpr hb
  refine ⟨⟨(Surp ξ.X f).toNat,⟨⟨f,c⟩,hf,?_⟩⟩,rfl⟩
  exact (Int.toNat_of_nonneg (connected_surp_nonnegative hf)).symm

/-- The deterministic repaired grading is valid for every admissible uncolored input. -/
theorem RepGr_connected_bound (ξ : AdjShellExch) (f : Grading ξ.X)
    (hf : ConnectedGrading f) (hb : ∀ e, f e ≤ 3) :
    ConnectedGrading (RepGr ξ f) ∧ ∀ e, RepGr ξ f e ≤ 3 := by
  obtain ⟨a,rfl⟩ := colored_input ξ f hf hb
  rw [← exchange_eq_RepGr]
  exact ⟨(ξ.exchange a).2.property.1,color_grade_le (ξ.exchange a).2.val.2⟩

theorem verticalCount_geometric (X : TNEPath) (f : Grading X) (k : ℕ) :
    verticalCount ((gradedWord X f).take k) = (X.steps.take k).count false := by
  induction k with
  | zero => rfl
  | succ k ih =>
      by_cases hk : k < X.steps.length
      · have hw : k < (gradedWord X f).length := by simpa using hk
        rw [List.take_succ_eq_append_getElem hw,List.take_succ_eq_append_getElem hk,
          verticalCount_append,List.count_append,ih]
        simp only [gradedWord,List.getElem_ofFn]
        cases X.steps[k] <;> simp [verticalCount]
      · have h1 : X.steps.length ≤ k := by omega
        have h2 : X.steps.length ≤ k+1 := by omega
        have hw1 : (gradedWord X f).length ≤ k := by simpa using h1
        have hw2 : (gradedWord X f).length ≤ k+1 := by simpa using h2
        rw [List.take_of_length_le h1,List.take_of_length_le hw1] at ih
        rw [List.take_of_length_le h2,List.take_of_length_le hw2]
        exact ih

def J (ξ : AdjShellExch) (f : Grading ξ.X) : ℕ :=
  (ξ.Y'.steps.take (position ξ f+1)).count false

/-- The selected position is an actual vertical edge; its ordinal is one-based. -/
theorem geometric_position_ordinal (ξ : AdjShellExch)
    (a : KroneckerAdjacentExchangeLemma.ColoredSet ξ.X) :
    (∃ h, (gradedWord ξ.Y' (transportedShell ξ a.2.val.1))[position ξ a.2.val.1]? = some (.V h)) ∧
    J ξ a.2.val.1 = changeIndex ξ.right ξ.r (gradedWord ξ.Y (sourceGrading ξ a.2.val.1))+1 := by
  have hh := position_vertical_ordinal (KroneckerExchangeColorCorrespondence.geometric_relation ξ a)
  rw [uncolor_edges] at hh
  change ∃ h, (swapEdges ξ.r (gradedWord ξ.Y (sourceGrading ξ a.2.val.1)))[position ξ a.2.val.1]? = some (.V h) ∧
    verticalCount ((swapEdges ξ.r (gradedWord ξ.Y (sourceGrading ξ a.2.val.1))).take
      (position ξ a.2.val.1+1)) = _ at hh
  have ht := (shellPair ξ).transported_word_exact (sourceGrading ξ a.2.val.1)
  rw [shell_pair_position] at ht
  rw [←ht] at hh
  obtain ⟨h,hv,hj⟩ := hh
  rw [verticalCount_geometric] at hj
  exact ⟨⟨h,hv⟩,hj⟩

/-- The positive EN branch uses the minimum of the literal counter set on the
geometrically transported shell; no graded-word decomposition is assumed. -/
theorem geometric_index_least (ξ : AdjShellExch)
    (a : KroneckerAdjacentExchangeLemma.ColoredSet ξ.X) (hξ : ξ.right = true)
    (hs : 0 < ((gradedWord ξ.Y (sourceGrading ξ a.2.val.1))[ξ.r]?.getD (.H 0)).grade) :
    IsLeast (candidateOrdinals
      (((gradedWord ξ.Y (sourceGrading ξ a.2.val.1))[ξ.r]?.getD (.H 0)).grade-1) ξ.r
      (gradedWord ξ.Y' (transportedShell ξ a.2.val.1))) (J ξ a.2.val.1) := by
  have he := KroneckerExchangeColorCorrespondence.geometric_relation ξ a
  rw [hξ] at he
  have hs' : 0 < ((coloredWord (KroneckerAdjacentExchangeLemma.edges
      (KroneckerAdjacentExchangeLemma.shell ξ.spec a.2.val)))[ξ.r]?.getD (.H 0)).grade := by
    rw [uncolor_edges]
    exact hs
  have hh := positive_index_least he hs'
  rw [uncolor_edges] at hh
  have ht := (shellPair ξ).transported_word_exact (sourceGrading ξ a.2.val.1)
  rw [shell_pair_position] at ht
  change IsLeast (candidateOrdinals
      (((gradedWord ξ.Y (sourceGrading ξ a.2.val.1))[ξ.r]?.getD (.H 0)).grade-1) ξ.r
      (swapEdges ξ.r (gradedWord ξ.Y (sourceGrading ξ a.2.val.1))))
      (changeIndex true ξ.r (gradedWord ξ.Y (sourceGrading ξ a.2.val.1))+1) at hh
  rw [←ht] at hh
  have hj := (geometric_position_ordinal ξ a).2
  rw [hξ] at hj
  rw [hj]
  exact hh

theorem geometric_position_bound (ξ : AdjShellExch)
    (a : KroneckerAdjacentExchangeLemma.ColoredSet ξ.X) :
    position ξ a.2.val.1 < ξ.Y'.steps.length := by
  obtain ⟨h,hh⟩ := (geometric_position_ordinal ξ a).1
  by_contra hn
  have he : (gradedWord ξ.Y' (transportedShell ξ a.2.val.1))[position ξ a.2.val.1]? = none :=
    List.getElem?_eq_none (by simpa using (show ξ.Y'.steps.length ≤ position ξ a.2.val.1 by omega))
  rw [he] at hh
  contradiction


def selectedEdge (ξ : AdjShellExch) (a : KroneckerAdjacentExchangeLemma.ColoredSet ξ.X) :
    Edge ξ.Y' := ⟨position ξ a.2.val.1,geometric_position_bound ξ a⟩

/-- The recovery code is the original grade-color pair on the selected edge. -/
theorem geometric_recovery_code (ξ : AdjShellExch)
    (a : KroneckerAdjacentExchangeLemma.ColoredSet ξ.X) :
    KroneckerAdjacentExchangeLemma.code ξ.spec ξ.origin a =
      let e := edgeEquiv ξ.Y ((shellPair ξ).indices.symm (selectedEdge ξ a))
      ⟨(KroneckerAdjacentExchangeLemma.shell ξ.spec a.2.val).1 e,
        (KroneckerAdjacentExchangeLemma.shell ξ.spec a.2.val).2 e⟩ := by
  have hc := KroneckerExchangeColorCorrespondence.exchange_code_at
    (KroneckerExchangeColorCorrespondence.geometric_relation ξ a)
  rw [uncolor_edges] at hc
  change (KroneckerAdjacentExchangeLemma.edges (KroneckerAdjacentExchangeLemma.shell ξ.spec a.2.val))[swapPos ξ.r (position ξ a.2.val.1)]? = _ at hc
  let l := (shellPair ξ).indices.symm (selectedEdge ξ a)
  have hi : l.val = swapPos ξ.r (position ξ a.2.val.1) := by
    change swapPos (shellPair ξ).pre.length (position ξ a.2.val.1) = _
    rw [shell_pair_position]
  rw [←hi] at hc
  have hs := KroneckerExchangeColorCorrespondence.edges_get
    (KroneckerAdjacentExchangeLemma.shell ξ.spec a.2.val) l
  have hp := congrArg Prod.snd (Option.some.inj (hs.symm.trans hc))
  dsimp only at hp
  change KroneckerAdjacentExchangeLemma.gradeColor
    (KroneckerWrappedExchangeWitness.chosen ξ.spec
      (KroneckerAdjacentExchangeLemma.operational ξ.X a)).code = _
  rw [←hp]
  exact KroneckerAdjacentExchangeLemma.geometric_pair
    (KroneckerAdjacentExchangeLemma.shell ξ.spec a.2.val) l

/-- The literal reduction equals the reduction of the selected colored witness. -/
theorem reduction_eq_chosen (ξ : AdjShellExch)
    (a : KroneckerAdjacentExchangeLemma.ColoredSet ξ.X) :
    reduction ξ a.2.val.1 =
      (KroneckerWrappedExchangeWitness.chosen ξ.spec
        (KroneckerAdjacentExchangeLemma.operational ξ.X a)).delta := by
  let w := KroneckerWrappedExchangeWitness.chosen ξ.spec
    (KroneckerAdjacentExchangeLemma.operational ξ.X a)
  have hh := w.delta_exact.trans
    (repairDelta_context w.exchange
      (KroneckerEdgeShell.edgePrefix 3 ξ.spec.u ξ.spec.hu)
      (KroneckerEdgeShell.edgeSuffix 3 ξ.spec.v ξ.spec.hv ξ.spec.hm)).symm
  have hp : (KroneckerEdgeShell.edgePrefix 3 ξ.spec.u ξ.spec.hu).length +
      (ξ.spec.P.length+1) = ξ.r := by
    simp [KroneckerEdgeShell.edgePrefix,AdjShellExch.spec,
      KroneckerAdjacentExchangeLemma.spec,AdjShellExch.r]
    omega
  rw [hp] at hh
  simp only [List.append_assoc] at hh
  change w.delta = repairDelta ξ.right ξ.r
    (coloredWord (KroneckerEdgeShell.edgeShell ξ.spec.u ξ.spec.v
      ξ.spec.hu ξ.spec.hv ξ.spec.hm (KroneckerAdjacentExchangeLemma.edges a.2.val))) at hh
  rw [←KroneckerAdjacentExchangeLemma.shell_edges,uncolor_edges] at hh
  exact (geometric_reduction_eq ξ a).trans hh.symm

/-- The unique changed vertical grade is the manuscript's one-based index J. -/
theorem RepGr_vertical_decrease (ξ : AdjShellExch) (f : Grading ξ.X)
    (hf : ConnectedGrading f) (hb : ∀ e, f e ≤ 3) :
    0 < J ξ f ∧
    LowerAt (reduction ξ f) (J ξ f-1)
      (verticalGrades (gradedWord ξ.Y (sourceGrading ξ f)))
      (verticalGrades (gradedWord ξ.Y' (RepGr ξ f))) ∧
    reduction ξ f ≤ 3 := by
  obtain ⟨a,rfl⟩ := colored_input ξ f hf hb
  have he := KroneckerExchangeColorCorrespondence.geometric_relation ξ a
  have hd := exchange_decrease he
  rw [uncolor_edges,uncolor_edges,exchange_eq_RepGr,←reduction_eq_chosen ξ a] at hd
  have hj := (geometric_position_ordinal ξ a).2
  refine ⟨by omega,?_,?_⟩
  · rw [hj,Nat.add_sub_cancel]
    exact hd
  · rw [reduction_eq_chosen]
    exact exchange_budget he

/-- The repaired grading has the exact surplus stated in the uncolored lemma. -/
theorem RepGr_surplus (ξ : AdjShellExch) (f : Grading ξ.X)
    (hf : ConnectedGrading f) (hb : ∀ e, f e ≤ 3) :
    Surp ξ.Y' (RepGr ξ f) = Surp ξ.X f + (reduction ξ f : ℤ) := by
  obtain ⟨a,rfl⟩ := colored_input ξ f hf hb
  rw [←exchange_eq_RepGr ξ a]
  have hs := (ξ.exchange a).2.property.2
  have hi := a.2.property.2
  rw [hs,hi,reduction_eq_chosen]
  have he : (ξ.exchange a).1 = a.1 +
      (KroneckerWrappedExchangeWitness.chosen ξ.spec
        (KroneckerAdjacentExchangeLemma.operational ξ.X a)).delta := rfl
  rw [he,Nat.cast_add]

end KroneckerRepairGeometry

#print axioms KroneckerRepairGeometry.gradedWord_boundary
#print axioms KroneckerRepairGeometry.RepGr_connected_bound
#print axioms KroneckerRepairGeometry.geometric_position_ordinal
#print axioms KroneckerRepairGeometry.geometric_index_least
#print axioms KroneckerRepairGeometry.geometric_position_bound

#print axioms KroneckerRepairGeometry.geometric_recovery_code

#print axioms KroneckerRepairGeometry.reduction_eq_chosen
#print axioms KroneckerRepairGeometry.RepGr_vertical_decrease
#print axioms KroneckerRepairGeometry.RepGr_surplus
