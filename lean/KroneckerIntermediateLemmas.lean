import KroneckerReflectedLinearBlock
import KroneckerTreeGluingCriterion
import KroneckerFiniteChainInputs
import KroneckerConnectedDeckNormalization
import KroneckerColoredTreeLift
import KroneckerBinaryMechanicalLemma
import KroneckerColoredExchangeRecovery

/-! Intermediate statements used by the ordered manuscript proofs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerIntermediateLemmas
attribute [local instance] Classical.propDecidable
open Module KroneckerBipartiteIncidence KroneckerReflectedSubrepresentations

theorem zero_sum_source_bound {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i, Fintype.card {j // R i j} = 3) (W : ReflectedSubrep R)
    (hn : 0 < (∑ j, finrank ℂ (W.source j)) + (∑ i, finrank ℂ (W.sink i))) :
    1 ≤ ∑ i, finrank ℂ (W.sink i) ∧
      (∑ j, finrank ℂ (W.source j)) + 1 ≤ ∑ i, finrank ℂ (W.sink i) := by
  have h := KroneckerReflectedBlockStability.reflected_subrepresentation_defect hT h3 W hn
  omega

open KroneckerBalancedVertexSpace KroneckerIncidenceDivergence
open KroneckerFlowEdgeExtension KroneckerTreeFlowUniqueness

theorem tree_flow_exists_unique {I J : Type} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (α : I → ℝ) (β : J → ℝ) (hbal : ∑ i, α i = ∑ j, β j) :
    ∃! f : Edge R → ℝ,
      (∀ i, ∑ j, extendFlow f i j = α i) ∧
      (∀ j, ∑ i, extendFlow f i j = β j) := by
  classical
  let d : I ⊕ J → ℝ := Sum.elim α (fun j => -β j)
  have hd : d ∈ Balanced (I ⊕ J) := by
    change (∑ v, d v) = 0
    simp [d, Fintype.sum_sum_type, Finset.sum_neg_distrib, hbal]
  have iffD (f : Edge R → ℝ) :
      ((∀ i, ∑ j, extendFlow f i j = α i) ∧
       (∀ j, ∑ i, extendFlow f i j = β j)) ↔ divergence R f = d := by
    constructor
    · rintro ⟨hr, hc⟩
      funext v
      cases v with
      | inl i => simpa [d, extended_row] using hr i
      | inr j =>
        have h := hc j
        rw [extended_column] at h
        dsimp [d]
        linarith
    · intro h
      constructor
      · intro i; rw [extended_row, h]; rfl
      · intro j; rw [extended_column, h]; simp [d]
  obtain ⟨f, hf, hu⟩ := unique_tree_flow R hT d hd
  exact ⟨f, (iffD f).mpr hf, fun g hg => hu g ((iffD g).mp hg)⟩

open KroneckerTreeCutComponents KroneckerTreeCutFlow KroneckerFlowBoundaryIdentity

theorem tree_flow_cut_formula {I J : Type} [Fintype I] [Fintype J]
    {R : I → J → Prop} (hT : (incidenceGraph R).IsTree)
    (f : I → J → ℝ) (hoff : ∀ i j, ¬R i j → f i j = 0)
    (α : I → ℝ) (β : J → ℝ)
    (hr : ∀ i, ∑ j, f i j = α i) (hc : ∀ j, ∑ i, f i j = β j)
    {i₀ : I} {j₀ : J} (h₀ : R i₀ j₀) :
    f i₀ j₀ = (∑ j ∈ cutBlocks R i₀ j₀, β j) -
      ∑ i ∈ cutConnectors R i₀ j₀, α i := by
  classical
  have hclosed : ∀ i ∈ cutConnectors R i₀ j₀, ∀ j ∉ cutBlocks R i₀ j₀,
      f i j = 0 := by
    intro i hi j hj
    exact hoff i j (fun h => hj (cut_is_connector_closed hT h₀ hi h))
  have h := boundary_demand_difference f (cutConnectors R i₀ j₀)
    (cutBlocks R i₀ j₀) hclosed
  rw [cut_boundary_flux hT f hoff h₀] at h
  simpa [hr, hc] using h.symm

open KroneckerRepairGrade

theorem exchange_repair_formula (h : ℕ) (b β : ℤ) (hb : β ≤ b) :
    (repairGrade h b β : ℤ) = min (h : ℤ) (b-β) ∧
      repairGrade h b β ≤ h ∧ β ≤ b-(repairGrade h b β : ℤ) := by
  refine ⟨?_, repair_grade_le h b β, repair_grade_guard h b β hb⟩
  have hz : ((b-β).toNat : ℤ) = b-β := Int.toNat_of_nonneg (by omega)
  simp only [repairGrade, min_def]
  split_ifs <;> omega

open KroneckerBinaryPrefixArea KroneckerBinaryPrefixSum KroneckerBinaryBalancedArea

theorem balanced_tail_triangular (d : ℤ) (xs ys : List Bool)
    (hl : xs.length = ys.length)
    (hb : d + (xs.count true : ℤ) - (ys.count true : ℤ) = 0) :
    prefixArea d xs ys ≤ xs.length.choose 2 := by
  induction xs generalizing d ys with
  | nil => simp [prefixArea]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      have hb' : d + bit x - bit y + (xs.count true : ℤ) - (ys.count true : ℤ) = 0 := by
        rw [count_cons_int, count_cons_int] at hb
        omega
      have h₁ := balanced_offset_bound _ xs ys hl' hb'
      have h₂ := ih _ ys hl' hb'
      simpa only [prefixArea, List.length_cons, Nat.choose_succ_succ,
        Nat.choose_one_right] using Nat.add_le_add h₁ h₂

open KroneckerBinaryAreaAppend KroneckerBinaryBalancingLetters

theorem binary_completion_cost (xs ys : List Bool)
    (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    swapDistance (xs ++ balancingLetters xs ys) ys ≤
      swapDistance xs (ys.take xs.length) + (ys.length-xs.length).choose 2 := by
  have hlen := balancing_length xs ys hc
  have hl : xs.length ≤ ys.length := by omega
  have hp : xs.length = (ys.take xs.length).length := by simp [List.length_take, hl]
  have ht : (balancingLetters xs ys).length = (ys.drop xs.length).length := by
    simp [balancing_length_sub xs ys hc]
  have hb : ((xs.count true : ℤ) - ((ys.take xs.length).count true : ℤ)) +
      ((balancingLetters xs ys).count true : ℤ) - ((ys.drop xs.length).count true : ℤ) = 0 := by
    have h := balancing_counts xs ys hc true
    have hsplit := List.count_append (l₁ := ys.take xs.length) (l₂ := ys.drop xs.length) (a := true)
    rw [List.take_append_drop] at hsplit
    simp only [List.count_append] at h
    omega
  have h := Nat.add_le_add_left
    (balanced_tail_triangular _ _ _ ht hb) (swapDistance xs (ys.take xs.length))
  rw [← swapDistance_append xs (ys.take xs.length) _ _ hp] at h
  simpa [List.take_append_drop, balancing_length_sub xs ys hc] using h

open KroneckerBinarySwapPrograms KroneckerBinaryGreedyExchange

/-- Lemma 9.14: a program and its length, with every prefix index displayed.
The constructor of `Swaps` permits only exchanges of unequal adjacent letters. -/
theorem binary_exchange_program (xs ys : List Bool)
    (hl : xs.length = ys.length) (hc : xs.count true = ys.count true) :
    ∃ ℓ : ℕ, Nonempty (Swaps xs ys ℓ) ∧
      ℓ = ∑ j ∈ Finset.range xs.length,
        (((xs.take (j + 1)).count true : ℤ) - (ys.take (j + 1)).count true).natAbs := by
  exact ⟨swapDistance xs ys, ⟨areaProgram xs ys hl hc⟩,
    swapDistance_prefix_sum xs ys hl⟩

/-- Lemma 9.15: the exchanges start after the balancing letters are appended.
The bound uses the first `xs.length` prefixes and the triangular tail cost. -/
theorem binary_completion_program (xs ys : List Bool)
    (hc : ∀ b : Bool, xs.count b ≤ ys.count b) :
    ∃ ℓ : ℕ, Nonempty (Swaps (xs ++ balancingLetters xs ys) ys ℓ) ∧
      ℓ ≤ (∑ j ∈ Finset.range xs.length,
        (((xs.take (j + 1)).count true : ℤ) - (ys.take (j + 1)).count true).natAbs) +
        (ys.length - xs.length).choose 2 := by
  have hlen := balancing_length xs ys hc
  have hl : (xs ++ balancingLetters xs ys).length = ys.length := by
    simpa only [List.length_append] using hlen
  refine ⟨swapDistance (xs ++ balancingLetters xs ys) ys,
    binary_area_program _ _ hl (balancing_counts xs ys hc), ?_⟩
  have hprefix : xs.length = (ys.take xs.length).length := by
    simp only [List.length_take]
    omega
  have hcost := binary_completion_cost xs ys hc
  rw [swapDistance_prefix_sum xs (ys.take xs.length) hprefix] at hcost
  have hsum : (∑ j ∈ Finset.range xs.length,
      (((xs.take (j + 1)).count true : ℤ) -
        ((ys.take xs.length).take (j + 1)).count true).natAbs) =
      ∑ j ∈ Finset.range xs.length,
        (((xs.take (j + 1)).count true : ℤ) - (ys.take (j + 1)).count true).natAbs := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlen : j + 1 ≤ xs.length := by
      have := Finset.mem_range.mp hj
      omega
    simp only [List.take_take, Nat.min_eq_left hjlen]
  simpa only [hsum] using hcost

end KroneckerIntermediateLemmas
