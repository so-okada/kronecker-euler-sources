import KroneckerRegularHoleBudget
import KroneckerFrameCollarIdentity
import KroneckerRationalLowerReduction

/- Original module: KroneckerExtractedHoles -/
section
/-! Literal ordered hole words extracted from a run list. -/
set_option autoImplicit false
namespace KroneckerExtractedHoles
open KroneckerHoleGrammar KroneckerHoleChains KroneckerExtractedChain

def extractedHoles (L : ℕ) : ℕ → List ℕ → List (List ℕ)
  | 0, X => [X]
  | n+1, X => X.take L :: extractedHoles L n (X.drop (L+3))

theorem holes_extractChain (L n : ℕ) (X : List ℕ) :
    holes (extractChain L n X) = extractedHoles L n X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    change X.take L :: holes (extractChain L n (X.drop (L+3))) =
      X.take L :: extractedHoles L n (X.drop (L+3))
    rw [ih]

theorem extractedHoles_regular (L n j : ℕ) (X : List ℕ) (hj : j < n) :
    (extractedHoles L n X)[j]?.getD [] = (X.drop (j*(L+3))).take L := by
  induction n generalizing X j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [extractedHoles]
    | succ j =>
      simp only [extractedHoles, List.getElem?_cons_succ]
      rw [ih j (X.drop (L+3)) (by omega)]
      simp only [List.drop_drop, Nat.succ_mul]
      congr 2
      omega

end KroneckerExtractedHoles
end

/- Original module: KroneckerExtractedLegality -/
section
/-! Every extracted guard and every run in every extracted hole retains the
alphabet legality of the original word. -/
set_option autoImplicit false
namespace KroneckerExtractedLegality
open KroneckerHoleGrammar KroneckerHoleChains KroneckerExtractedChain KroneckerExtractedRecovery

theorem legal_of_expand (m : ℕ) (w : List Piece)
    (h : ∀ r ∈ expand w, 1 ≤ r ∧ r ≤ m-1) : Legal m w := by
  intro t ht
  cases t with
  | guard r =>
    apply h r
    exact List.mem_flatMap.mpr ⟨.guard r,ht,by simp [pieceWord]⟩
  | hole X => trivial

theorem holes_legal_of_expand (m : ℕ) (w : List Piece)
    (h : ∀ r ∈ expand w, 1 ≤ r ∧ r ≤ m-1) :
    ∀ X ∈ holes w, ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-1 := by
  intro X hX r hr
  obtain ⟨t,ht,hXt⟩ := List.mem_flatMap.mp hX
  cases t with
  | guard k => simp at hXt
  | hole Y =>
    have hXY : X = Y := by simpa using hXt
    subst X
    apply h r
    exact List.mem_flatMap.mpr ⟨.hole Y,ht,hr⟩

theorem extracted_legality (m L n : ℕ) (X : List ℕ) (hlen : n*(L+3) ≤ X.length)
    (h : ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-1) :
    Legal m (extractChain L n X) ∧
      ∀ Y ∈ holes (extractChain L n X), ∀ r ∈ Y, 1 ≤ r ∧ r ≤ m-1 := by
  have hx : ∀ r ∈ expand (extractChain L n X), 1 ≤ r ∧ r ≤ m-1 := by
    rw [extractChain_expand L n X hlen]
    exact h
  exact ⟨legal_of_expand m _ hx, holes_legal_of_expand m _ hx⟩

end KroneckerExtractedLegality
end

/- Original module: KroneckerExtractedCounts -/
section
/-! A literal word with six exterior guards dominates the product of the
counts of its extracted holes. -/
set_option autoImplicit false
namespace KroneckerExtractedCounts
open KroneckerWordCounts KroneckerHoleGrammar KroneckerHoleChains KroneckerScaffoldCounts
open KroneckerExtractedChain KroneckerExtractedHoles KroneckerExtractedRecovery KroneckerExtractedLegality

theorem extracted_scaffold_count (m L n : ℕ) (hm : 3 ≤ m) (X : List ℕ)
    (a b c d e f : ℕ) (hlen : n*(L+3) ≤ X.length)
    (hlegal : ∀ r ∈ a::b::c::X++[d,e,f], 1 ≤ r ∧ r ≤ m-1) :
    ((extractedHoles L n X).map (fun Y => runCount m Y 0)).prod ≤
      runCount m (a::b::c::X++[d,e,f]) 0 := by
  have hex : expand (.guard a :: .guard b :: .guard c :: extractChain L n X ++
      [.guard d, .guard e, .guard f]) = a::b::c::X++[d,e,f] := by
    simp only [expand, List.flatMap_append, List.flatMap_cons, pieceWord,
      List.flatMap_nil, List.singleton_append, List.append_nil]
    change a::b::c::expand (extractChain L n X)++[d,e,f] = a::b::c::X++[d,e,f]
    rw [extractChain_expand L n X hlen]
  have hl : Legal m (.guard a :: .guard b :: .guard c :: extractChain L n X ++
      [.guard d, .guard e, .guard f]) := by
    apply legal_of_expand
    rw [hex]
    exact hlegal
  have h := scaffold_product_bound m hm (extractChain_chain L n X) a b c d e f hl
  rw [holes_extractChain, extractChain_expand L n X hlen] at h
  exact h

end KroneckerExtractedCounts
end

/- Original module: KroneckerExtractedProduct -/
section
/-! Separate the regular indexed holes from the final remainder hole in the product. -/
set_option autoImplicit false
namespace KroneckerExtractedProduct
open KroneckerExtractedHoles

theorem extractedHoles_product (L n : ℕ) (X : List ℕ) (weight : List ℕ → ℕ) :
    ((extractedHoles L n X).map weight).prod =
      (∏ j ∈ Finset.range n, weight ((X.drop (j*(L+3))).take L))*weight (X.drop (n*(L+3))) := by
  induction n generalizing X with
  | zero => simp [extractedHoles]
  | succ n ih =>
    simp only [extractedHoles, List.map_cons, List.prod_cons, ih]
    rw [Finset.prod_range_succ']
    simp only [Nat.zero_mul, List.drop_zero]
    have hshift : (fun j => weight (((X.drop (L+3)).drop (j*(L+3))).take L)) =
        (fun j => weight ((X.drop ((j+1)*(L+3))).take L)) := by
      funext j
      simp only [List.drop_drop]
      congr 3
      ring
    rw [hshift]
    have htail : (X.drop (L+3)).drop (n*(L+3)) = X.drop ((n+1)*(L+3)) := by
      rw [List.drop_drop]
      congr 1
      ring
    rw [htail]
    ac_rfl

end KroneckerExtractedProduct
end

/- Original module: KroneckerIndexedProduct -/
section
/-! An indexed product lower bound that counts occurrences, including equal words. -/
set_option autoImplicit false
namespace KroneckerIndexedProduct

theorem indexed_selected_product (n A : ℕ) (weight : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hone : ∀ i < n, 1 ≤ weight i) (hgood : ∀ i < n, P i → A ≤ weight i) :
    A^((Finset.range n).filter P).card ≤ ∏ i ∈ Finset.range n, weight i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htail := ih (fun i hi => hone i (by omega)) (fun i hi => hgood i (by omega))
    have hn := hone n (by omega)
    by_cases hP : P n
    · have hnA := hgood n (by omega) hP
      have hmul := Nat.mul_le_mul htail hnA
      simpa [Finset.range_add_one, Finset.filter_insert, hP, pow_succ,
        Finset.prod_range_succ, Nat.mul_comm] using hmul
    · have hmul := Nat.mul_le_mul htail hn
      simpa [Finset.range_add_one, Finset.filter_insert, hP,
        Finset.prod_range_succ, Nat.mul_comm] using hmul

end KroneckerIndexedProduct
end

/- Original module: KroneckerIndexedBudget -/
section
/-! Convert an upper bound on bad indices into a power lower bound for the product. -/
set_option autoImplicit false
namespace KroneckerIndexedBudget
open KroneckerIndexedProduct

theorem indexed_product_bad_budget (n A D : ℕ) (weight : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hA : 1 ≤ A) (hone : ∀ i < n, 1 ≤ weight i)
    (hgood : ∀ i < n, P i → A ≤ weight i)
    (hbad : ((Finset.range n).filter (fun i => ¬P i)).card ≤ D) :
    A^(n-D) ≤ ∏ i ∈ Finset.range n, weight i := by
  have hc : ((Finset.range n).filter P).card+
      ((Finset.range n).filter (fun i => ¬P i)).card = n := by
    simpa only [Finset.card_range] using
      Finset.card_filter_add_card_filter_not (s := Finset.range n) P
  have he : n-D ≤ ((Finset.range n).filter P).card := by omega
  exact (Nat.pow_le_pow_right hA he).trans (indexed_selected_product n A weight P hone hgood)

end KroneckerIndexedBudget
end

/- Original module: KroneckerExtractedPower -/
section
/-! A power lower bound for a literal extracted scaffold, with all remaining
local count inputs stated explicitly. -/
set_option autoImplicit false
namespace KroneckerExtractedPower
open KroneckerWordCounts KroneckerExtractedHoles KroneckerExtractedCounts
open KroneckerExtractedProduct KroneckerIndexedBudget

theorem extracted_scaffold_power (m L n A D : ℕ) (hm : 3 ≤ m) (X : List ℕ)
    (a b c d e f : ℕ) (hlen : n*(L+3) ≤ X.length)
    (hlegal : ∀ r ∈ a::b::c::X++[d,e,f], 1 ≤ r ∧ r ≤ m-1)
    (P : ℕ → Prop) [DecidablePred P] (hA : 1 ≤ A)
    (hone : ∀ i < n, 1 ≤ runCount m ((X.drop (i*(L+3))).take L) 0)
    (hlast : 1 ≤ runCount m (X.drop (n*(L+3))) 0)
    (hgood : ∀ i < n, P i → A ≤ runCount m ((X.drop (i*(L+3))).take L) 0)
    (hbad : ((Finset.range n).filter (fun i => ¬P i)).card ≤ D) :
    A^(n-D) ≤ runCount m (a::b::c::X++[d,e,f]) 0 := by
  have hp := indexed_product_bad_budget n A D
    (fun i => runCount m ((X.drop (i*(L+3))).take L) 0) P hA hone hgood hbad
  have hmul : (∏ i ∈ Finset.range n, runCount m ((X.drop (i*(L+3))).take L) 0) ≤
      (∏ i ∈ Finset.range n, runCount m ((X.drop (i*(L+3))).take L) 0)*
        runCount m (X.drop (n*(L+3))) 0 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left
      (∏ i ∈ Finset.range n, runCount m ((X.drop (i*(L+3))).take L) 0) hlast
  have hsc := extracted_scaffold_count m L n hm X a b c d e f hlen hlegal
  rw [extractedHoles_product] at hsc
  exact hp.trans (hmul.trans hsc)

end KroneckerExtractedPower
end

/- Original module: KroneckerFrameScaffoldBudget -/
section
/-! Exact length budgets for the frame scaffold, including the remainder hole. -/
set_option autoImplicit false
open Filter
namespace KroneckerFrameScaffoldBudget

theorem hole_count_positive (a L : ℕ) (ha : L+5 ≤ a) : 1 ≤ (a-2)/(L+3) := by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  omega

theorem frame_scaffold_budget (a L : ℕ) (hL : 0 < L) (hH : 1 ≤ (a-2)/(L+3)) :
    6 ≤ a+1 ∧ (((a-2)/(L+3))-1)*(L+3)+1 ≤ a-5 := by
  let H := (a-2)/(L+3)
  have hH' : 1 ≤ H := hH
  have hdiv : H*(L+3) ≤ a-2 := Nat.div_mul_le_self (a-2) (L+3)
  have hbase : L+3 ≤ H*(L+3) := by nlinarith
  have ha : L+5 ≤ a := by omega
  have heq : (H-1)*(L+3)+(L+3) = H*(L+3) := by
    have h : H-1+1=H := by omega
    nlinarith
  change 6 ≤ a+1 ∧ (H-1)*(L+3)+1 ≤ a-5
  constructor <;> omega

theorem eventually_positive_hole_count (a : ℕ → ℕ) (L : ℕ) (ha : Tendsto a atTop atTop) :
    ∀ᶠ n in atTop, 1 ≤ (a n-2)/(L+3) := by
  filter_upwards [ha.eventually (eventually_ge_atTop (L+5))] with n hn
  exact hole_count_positive (a n) L hn

end KroneckerFrameScaffoldBudget
end

/- Original module: KroneckerGoodBlockCount -/
section
/-! Good-block count reduction. The classification of its first period as a
rational rotation is an explicit hypothesis, not a newly proved fact here. -/
set_option autoImplicit false
namespace KroneckerGoodBlockCount
open KroneckerWordCounts KroneckerPeriodicWords KroneckerRotatedCounts
open KroneckerMechanicalWords KroneckerMechanicalWindows KroneckerGoodIntervals KroneckerGoodWordRepetition

theorem good_block_count (m : ℕ) (hm : 3 ≤ m) (W : List ℕ)
    (hr : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (s u : ℝ) (p : ℤ) (start J : ℕ) (hJ : 4 ≤ J)
    (hgood : GoodWindows s u p W.length start (J*W.length))
    (hphase : ∀ i, windowSum s u W.length i = p →
      ∃ j, j ≤ W.length ∧ mechanicalWord s u i W.length = W.rotate j) :
    periodicCount m W (J-3) ≤ runCount m (mechanicalWord s u start (J*W.length)) 0 := by
  have hfirst : windowSum s u W.length start = p := by
    simpa only [Nat.add_zero] using hgood 0 (by nlinarith)
  obtain ⟨j,hj,hbase⟩ := hphase start hfirst
  rw [good_word_repetition s u p W.length start J hgood, hbase]
  exact periodic_hole_bound m hm W j J hj (by omega) hr

end KroneckerGoodBlockCount
end

/- Original module: KroneckerSliceCounts -/
section
/-! Canonical fillings supply positive counts on every nonempty legal slice. -/
set_option autoImplicit false
namespace KroneckerSliceCounts
open KroneckerWordCounts KroneckerWordBounds

theorem slice_count_positive (m : ℕ) (hm : 3 ≤ m) (X : List ℕ) (i L : ℕ)
    (hL : 0 < L) (hfit : i+L ≤ X.length)
    (hlegal : ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-1) :
    1 ≤ runCount m ((X.drop i).take L) 0 := by
  apply runCount_pos m hm
  · intro heq
    have hlen : ((X.drop i).take L).length = L := by
      simp only [List.length_take, List.length_drop]
      omega
    rw [heq] at hlen
    simp only [List.length_nil] at hlen
    omega
  · intro r hr
    exact hlegal r (List.mem_of_mem_drop (List.mem_of_mem_take hr))

theorem tail_count_positive (m : ℕ) (hm : 3 ≤ m) (X : List ℕ) (i : ℕ)
    (hi : i < X.length) (hlegal : ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-1) :
    1 ≤ runCount m (X.drop i) 0 := by
  apply runCount_pos m hm
  · intro heq
    have hlen : (X.drop i).length = X.length-i := List.length_drop
    rw [heq] at hlen
    simp only [List.length_nil] at hlen
    omega
  · intro r hr
    exact hlegal r (List.mem_of_mem_drop hr)

end KroneckerSliceCounts
end

/- Original module: KroneckerLegalScaffoldPower -/
section
/-! The extracted scaffold power bound needs no assumed canonical-count inputs:
they follow from legality and the nonempty remainder budget. -/
set_option autoImplicit false
namespace KroneckerLegalScaffoldPower
open KroneckerWordCounts KroneckerExtractedPower KroneckerSliceCounts

theorem legal_scaffold_power (m L n A D : ℕ) (hm : 3 ≤ m) (X : List ℕ)
    (a b c d e f : ℕ) (hL : 0 < L) (hlen : n*(L+3)+1 ≤ X.length)
    (hlegal : ∀ r ∈ a::b::c::X++[d,e,f], 1 ≤ r ∧ r ≤ m-1)
    (P : ℕ → Prop) [DecidablePred P] (hA : 1 ≤ A)
    (hgood : ∀ i < n, P i → A ≤ runCount m ((X.drop (i*(L+3))).take L) 0)
    (hbad : ((Finset.range n).filter (fun i => ¬P i)).card ≤ D) :
    A^(n-D) ≤ runCount m (a::b::c::X++[d,e,f]) 0 := by
  have hX : ∀ r ∈ X, 1 ≤ r ∧ r ≤ m-1 := by
    intro r hr
    exact hlegal r (by simp [hr])
  apply extracted_scaffold_power m L n A D hm X a b c d e f (by omega) hlegal P hA
  · intro i hi
    apply slice_count_positive m hm X (i*(L+3)) L hL _ hX
    have hmul : (i+1)*(L+3) ≤ n*(L+3) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · exact tail_count_positive m hm X (n*(L+3)) (by omega) hX
  · exact hgood
  · exact hbad

end KroneckerLegalScaffoldPower
end

/- Original module: KroneckerFrameScaffoldLower -/
section
/-! The finite rational scaffold bound for the exact frame. Only the rational
phase classification remains an explicit local word hypothesis. -/
set_option autoImplicit false
namespace KroneckerFrameScaffoldLower
open KroneckerWordCounts KroneckerPeriodicWords KroneckerPeriodicBounds
open KroneckerFrameSlope KroneckerFrameBadDensity KroneckerFrameWord KroneckerFrameSlices
open KroneckerMechanicalWords KroneckerMechanicalWindows KroneckerGoodIntervals KroneckerGoodBlockCount
open KroneckerSeparatedStarts KroneckerBadHoleWitness KroneckerBadHoleCount KroneckerRegularHoleBudget
open KroneckerBadWindowBounds KroneckerSixGuards KroneckerFrameScaffoldBudget KroneckerLegalScaffoldPower

theorem frame_scaffold_lower (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (a b d J : ℕ) (p : ℤ) (hJ : 4 ≤ J)
    (hH : 1 ≤ (a-2)/(J*W.length+3))
    (hlegal : ∀ r ∈ frameWord a b d, 1 ≤ r ∧ r ≤ m-1)
    (hphase : ∀ i, windowSum (frameSlope a b d) 0 W.length i = p →
      ∃ j, j ≤ W.length ∧ mechanicalWord (frameSlope a b d) 0 i W.length = W.rotate j) :
    (periodicCount m W (J-3))^((a-2)/(J*W.length+3)-
      (badWindows (frameSlope a b d) 0 p W.length (a+1-W.length)+1)) ≤
      runCount m (frameWord a b d) 0 := by
  classical
  let L := J*W.length
  let H := (a-2)/(L+3)
  let N := H-1
  let D := badWindows (frameSlope a b d) 0 p W.length (a+1-W.length)
  let A := periodicCount m W (J-3)
  let P := fun i => GoodWindows (frameSlope a b d) 0 p W.length (holeStart L i) L
  have hq : 0 < W.length := List.length_pos_iff.mpr hne
  have hL : 0 < L := Nat.mul_pos (by omega) hq
  obtain ⟨hsize,hbudget⟩ := frame_scaffold_budget a L hL hH
  obtain ⟨g0,g1,g2,g3,g4,g5,X,hZ,hX⟩ := exists_six_guards (frameWord a b d) (by
    rw [frameWord_length]
    exact hsize)
  have hXlen : X.length = a-5 := by rw [frameWord_length] at hX; omega
  have hlen : N*(L+3)+1 ≤ X.length := by rw [hXlen]; exact hbudget
  have hfit (i : ℕ) (hi : i < N) : i*(L+3)+L ≤ X.length := by
    have hm : (i+1)*(L+3) ≤ N*(L+3) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hframefit (i : ℕ) (hi : i < N) : holeStart L i+L ≤ a := by
    apply regular_hole_fits a L i
    change i < H
    dsimp only [N] at hi
    omega
  have hgood : ∀ i < N, P i → A ≤ runCount m ((X.drop (i*(L+3))).take L) 0 := by
    intro i hi hg
    have hslice : (X.drop (i*(L+3))).take L =
        mechanicalWord (frameSlope a b d) 0 (holeStart L i) L := by
      have hs := middle_slice (frameWord a b d) X g0 g1 g2 g3 g4 g5 (i*(L+3)) L hZ (hfit i hi)
      rw [frameWord_slice a b d (3+i*(L+3)) L (hframefit i hi)] at hs
      exact hs.symm
    rw [hslice]
    exact good_block_count m hm W hW (frameSlope a b d) 0 p (holeStart L i) J hJ hg hphase
  have hbad : ((Finset.range N).filter (fun i => ¬P i)).card ≤ D :=
    bad_holes_le_bad_windows (frameSlope a b d) 0 p W.length L N a hq hframefit
  have hA : 1 ≤ A := periodicCount_pos m hm W hne hW (J-3) (by omega)
  have hout := legal_scaffold_power m L N A D hm X g0 g1 g2 g3 g4 g5 hL hlen
    (by rw [← hZ]; exact hlegal) P hA hgood hbad
  rw [← hZ] at hout
  have hexp : N-D = H-(D+1) := by dsimp only [N]; omega
  rw [hexp] at hout
  exact hout

end KroneckerFrameScaffoldLower
end

/- Original module: KroneckerFrameScaffoldEventual -/
section
/-! Fixed-length scaffold inequalities hold eventually as the first dimension grows.
Rational phase classification and alphabet admissibility are explicit assumptions. -/
set_option autoImplicit false
open Filter
namespace KroneckerFrameScaffoldEventual
open KroneckerWordCounts KroneckerPeriodicWords KroneckerFrameSlope KroneckerFrameBadDensity
open KroneckerMechanicalWords KroneckerMechanicalWindows KroneckerBadWindowBounds
open KroneckerFrameScaffoldBudget KroneckerFrameScaffoldLower

theorem eventual_frame_scaffold_power (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (a b d : ℕ → ℕ) (p : ℤ) (J : ℕ) (hJ : 4 ≤ J)
    (ha : Tendsto a atTop atTop)
    (hlegal : ∀ᶠ n in atTop, ∀ r ∈ frameWord (a n) (b n) (d n), 1 ≤ r ∧ r ≤ m-1)
    (hphase : ∀ᶠ n in atTop, ∀ i, windowSum (frameSlope (a n) (b n) (d n)) 0 W.length i = p →
      ∃ j, j ≤ W.length ∧ mechanicalWord (frameSlope (a n) (b n) (d n)) 0 i W.length = W.rotate j) :
    ∀ᶠ n in atTop, (periodicCount m W (J-3))^((a n-2)/(J*W.length+3)-
      (badWindows (frameSlope (a n) (b n) (d n)) 0 p W.length (a n+1-W.length)+1)) ≤
      runCount m (frameWord (a n) (b n) (d n)) 0 := by
  filter_upwards [eventually_positive_hole_count a (J*W.length) ha, hlegal, hphase] with n hH hl hp
  exact frame_scaffold_lower m hm W hne hW (a n) (b n) (d n) J p hJ hH hl hp

end KroneckerFrameScaffoldEventual
end

/- Original module: KroneckerRationalFrameLower -/
section
/-! The rational lower limit for literal frame counts is reduced to the
single remaining local phase-classification input and alphabet admissibility. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerRationalFrameLower
open KroneckerWordCounts KroneckerPeriodicWords KroneckerPeriodicTail KroneckerFrameSlope
open KroneckerFrameBadDensity KroneckerFrameSlopeLimit KroneckerMechanicalWords KroneckerMechanicalWindows
open KroneckerBadWindowBounds KroneckerBadWindowDensity KroneckerFrameScaffoldEventual KroneckerRationalLowerReduction

theorem frame_internal_bad_density (a b d : ℕ → ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    Tendsto (fun n => (badWindows (frameSlope (a n) (b n) (d n)) 0 p q (a n+1-q) : ℝ)/
      (a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  exact bad_window_density (fun n => frameSlope (a n) (b n) (d n)) (fun _ => 0) a
    (fun n => a n+1-q) p q hq ha (frame_slope_limit a b d _ ha hd hr)
    (fun n => by omega)

theorem rational_frame_lower (m : ℕ) (hm : 3 ≤ m) (W : List ℕ) (hne : W ≠ [])
    (hW : ∀ r ∈ W, 1 ≤ r ∧ r ≤ m-1) (a b d : ℕ → ℕ) (p : ℤ)
    (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(W.length : ℝ))))
    (hlegal : ∀ᶠ n in atTop, ∀ r ∈ frameWord (a n) (b n) (d n), 1 ≤ r ∧ r ≤ m-1)
    (hphase : ∀ᶠ n in atTop, ∀ i, windowSum (frameSlope (a n) (b n) (d n)) 0 W.length i = p →
      ∃ j, j ≤ W.length ∧ mechanicalWord (frameSlope (a n) (b n) (d n)) 0 i W.length = W.rotate j) :
    ∀ ε > 0, ∀ᶠ n in atTop, periodicGrowth m W/(W.length : ℝ)-ε ≤
      Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/(a n : ℝ) := by
  have hq : 0 < W.length := List.length_pos_iff.mpr hne
  exact rational_lower_of_scaffold_bounds m hm W hne hW W.length hq a
    (fun n => badWindows (frameSlope (a n) (b n) (d n)) 0 p W.length (a n+1-W.length))
    (fun n => runCount m (frameWord (a n) (b n) (d n)) 0) ha
    (frame_internal_bad_density a b d p W.length hq ha hd hr)
    (fun J hJ => eventual_frame_scaffold_power m hm W hne hW a b d p J hJ ha hlegal hphase)

end KroneckerRationalFrameLower
end
