import KroneckerCollarSplit

/- Original module: KroneckerSplitLegality -/
section
/-! Every chosen collar and buffer inherits legality from the literal target. -/
set_option autoImplicit false
namespace KroneckerSplitLegality

theorem split_legal {m u v : ℕ} {X L Y R : List ℕ}
    (hX : X=L++(u::Y++[v])++R) (h : ∀ r ∈ X,1 ≤ r ∧ r ≤ m-2) :
    (∀ r ∈ L,1 ≤ r ∧ r ≤ m-2) ∧ (1 ≤ u ∧ u ≤ m-2) ∧
    (∀ r ∈ Y,1 ≤ r ∧ r ≤ m-2) ∧ (1 ≤ v ∧ v ≤ m-2) ∧
    (∀ r ∈ R,1 ≤ r ∧ r ≤ m-2) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r hr; apply h r; rw [hX]; simp [hr]
  · apply h u; rw [hX]; simp
  · intro r hr; apply h r; rw [hX]; simp [hr]
  · apply h v; rw [hX]; simp
  · intro r hr; apply h r; rw [hX]; simp [hr]

end KroneckerSplitLegality
end

/- Original module: KroneckerWordIntegerLower -/
section
/-! The actual lower comparison uses the exact target middle and whole-word edit allowance. -/
set_option autoImplicit false
namespace KroneckerWordIntegerLower
open KroneckerWordCounts KroneckerPeriodicWords KroneckerSingletonPeriod
open KroneckerFiberBudget KroneckerFiberBudgetMonotone KroneckerWordEditCost
open KroneckerIntegerWordComparison KroneckerEditCostSlices KroneckerCollarSplit KroneckerSplitLegality

theorem word_integer_lower {m k P : ℕ} (hm : 4 ≤ m) (X : List ℕ)
    (hlegal : ∀ r ∈ X,1 ≤ r ∧ r ≤ m-2) (hP : (m+1)*wordEditCost X k ≤ P) :
    periodicCount m [k] (X.length-2*P-2) ≤
      runCount m X 0*fiberBudget m (X.length-2*P-2) (wordEditCost X k) := by
  by_cases hroom : 2*P+2 ≤ X.length
  · obtain ⟨L,u,Y,v,R,hX,hL,hY,hR⟩ := collar_split X P hroom
    obtain ⟨hl,hu,_,hv,hr⟩ := split_legal hX hlegal
    have hcost : wordEditCost Y k ≤ wordEditCost X k := by
      rw [hX]
      simpa only [List.append_assoc,List.singleton_append] using editCost_middle (L++[u]) Y ([v]++R) k
    have hsmall : (m+1)*wordEditCost Y k ≤ P :=
      (Nat.mul_le_mul_left _ hcost).trans hP
    have hc := constant_to_word_count hm hu hv Y L R hl hr hL hR hsmall
    rw [← hX] at hc
    have hB := fiberBudget_mono_deletions m Y.length (wordEditCost Y k) (wordEditCost X k) hcost
    have hfinal := hc.trans (Nat.mul_le_mul_right (runCount m X 0) hB)
    simpa only [periodicCount_singleton,hY,Nat.mul_comm] using hfinal
  · have hz : X.length-2*P-2=0 := by omega
    simp only [hz,periodicCount_zero,Nat.zero_le]

end KroneckerWordIntegerLower
end

/- Original module: KroneckerFrameIntegerLower -/
section
/-! The literal frame satisfies the exact finite lower comparison, even for short frames. -/
set_option autoImplicit false
namespace KroneckerFrameIntegerLower
open KroneckerWordCounts KroneckerPeriodicWords KroneckerFiberBudget KroneckerWordEditCost
open KroneckerFrameBadDensity KroneckerFrameWord KroneckerSurgeryPadding KroneckerSurgeryBudget
open KroneckerIntegerComparisonLengths KroneckerWordIntegerLower

theorem frame_integer_lower {m k : ℕ} (hm : 4 ≤ m) (a b d : ℕ)
    (hlegal : ∀ r ∈ frameWord a b d,1 ≤ r ∧ r ≤ m-2) :
    periodicCount m [k] (middleLength a (surgeryPadding m (wordEditCost (frameWord a b d) k))) ≤
      runCount m (frameWord a b d) 0*
        fiberBudget m (middleLength a (surgeryPadding m (wordEditCost (frameWord a b d) k)))
          (wordEditCost (frameWord a b d) k) := by
  have h := word_integer_lower (k:=k) (P:=surgeryPadding m (wordEditCost (frameWord a b d) k))
    hm (frameWord a b d) hlegal (surgeryPadding_budget m (wordEditCost (frameWord a b d) k))
  simpa only [frameWord_length,← middleLength_eq] using h

end KroneckerFrameIntegerLower
end
