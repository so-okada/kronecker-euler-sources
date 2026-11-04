import KroneckerPaperNodeShadow

/-! Complete debt-sum identity for each prefix of a node. -/
set_option autoImplicit false
namespace KroneckerShadowDebtHelpers
noncomputable section
open KroneckerStack KroneckerPredecessor

def intervalLoad {n : ℕ} (U : Word n) (p : Fin n → Fin n)
    (a k : ℕ) (y : Fin n) : ℕ := by
  classical
  exact ∑ w ∈ intervalEdges a k, if ¬ IsHorizontal U w ∧ p w = y then 1 else 0

theorem intervalLoad_eq_load {n a k : ℕ} (U : Word n)
    (p : Fin n → Fin n) (hp : ValidThrough U p n)
    (y : Fin n) (hay : a ≤ y.val) :
    intervalLoad U p a k y = load U p k y := by
  classical
  unfold intervalLoad load
  apply Finset.sum_subset
  · intro w hw
    exact mem_prefix.mpr (mem_intervalEdges.mp hw).2
  · intro w hw hwout
    have hwk := mem_prefix.mp hw
    have hwa : w.val < a := by
      have := mt mem_intervalEdges.mpr hwout
      omega
    by_cases h : ¬ IsHorizontal U w ∧ p w = y
    · have hprior := (hp w w.isLt h.1).2.1
      rw [h.2] at hprior
      omega
    · simp [h]

theorem intervalLoad_zero_outside {n a k : ℕ} (U : Word n)
    (p : Fin n → Fin n) (hp : ValidThrough U p n)
    (hinternal : ∀ w, w ∈ intervalEdges a k → ¬ IsHorizontal U w → a ≤ (p w).val)
    (y : Fin n) (hy : y ∉ intervalEdges a k) :
    intervalLoad U p a k y = 0 := by
  classical
  unfold intervalLoad
  apply Finset.sum_eq_zero
  intro w hw
  by_cases h : ¬ IsHorizontal U w ∧ p w = y
  · have hbefore := (hp w w.isLt h.1).2.1
    have hafter := hinternal w hw h.1
    rw [h.2] at hbefore hafter
    have hwk := (mem_intervalEdges.mp hw).2
    have hymem : y ∈ intervalEdges a k := mem_intervalEdges.mpr ⟨hafter, by omega⟩
    exact False.elim (hy hymem)
  · simp [h]

/-- Internal assignment converts the vertical count into a sum of predecessor
loads over the same horizontal interval. -/
theorem interval_count_eq_sum_load {n a k : ℕ} (U : Word n)
    (p : Fin n → Fin n) (hp : ValidThrough U p n)
    (hinternal : ∀ w, w ∈ intervalEdges a k → ¬ IsHorizontal U w → a ≤ (p w).val) :
    intervalVerticalCount U a k = ∑ y ∈ intervalEdges a k, load U p k y := by
  classical
  have hsum : (∑ y, intervalLoad U p a k y) = intervalVerticalCount U a k := by
    unfold intervalLoad intervalVerticalCount
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : IsHorizontal U w <;> simp [hw, eq_comm]
  rw [← hsum]
  calc
    (∑ y, intervalLoad U p a k y) = ∑ y ∈ intervalEdges a k, intervalLoad U p a k y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      exact intervalLoad_zero_outside U p hp hinternal y hy
    _ = ∑ y ∈ intervalEdges a k, load U p k y := by
      apply Finset.sum_congr rfl
      intro y hy
      exact intervalLoad_eq_load U p hp y (mem_intervalEdges.mp hy).1

def horizontalInterval {n : ℕ} (U : Word n) (a k : ℕ) : Finset (Fin n) :=
  (intervalEdges a k).filter (IsHorizontal U)

theorem load_zero_vertical {n k : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) {y : Fin n} (hy : ¬ IsHorizontal U y) :
    load U p k y = 0 := by
  classical
  unfold load
  apply Finset.sum_eq_zero
  intro w _
  have hn : ¬ (¬ IsHorizontal U w ∧ p w = y) := by
    rintro ⟨hw, he⟩
    have hh := (hp w w.isLt hw).1
    exact hy (he ▸ hh)
  simp [hn]

theorem node_prefix_load {n k : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v : Fin n} (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hk : k ≤ v.val + 1) :
    intervalVerticalCount U x.val k =
      ∑ y ∈ horizontalInterval U x.val k, load U p k y := by
  classical
  have hi : ∀ w, w ∈ intervalEdges x.val k → ¬ IsHorizontal U w → x.val ≤ (p w).val := by
    intro w hw hwV
    obtain ⟨hl, hr⟩ := mem_intervalEdges.mp hw
    exact (h.internal_assignment hp (mem_nodeOccurrences.mpr ⟨hl, by omega⟩) hwV).2.1
  rw [interval_count_eq_sum_load U p hp hi, horizontalInterval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : IsHorizontal U y
  · simp [hy]
  · simp [hy, load_zero_vertical hp hy]

theorem node_debt_sum {n k : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v : Fin n} (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hk : k ≤ v.val + 1) :
    (intervalVerticalCount U x.val k : ℤ) - (intervalHorizontalGrade U x.val k : ℤ) =
      -(∑ y ∈ horizontalInterval U x.val k, (((U y).grade : ℤ) - (load U p k y : ℤ))) := by
  classical
  have hg : intervalHorizontalGrade U x.val k =
      ∑ y ∈ horizontalInterval U x.val k, (U y).grade := by
    simp [intervalHorizontalGrade, horizontalInterval, Finset.sum_filter]
  rw [node_prefix_load h hp hk, hg]
  push_cast
  rw [Finset.sum_sub_distrib]
  ring

theorem node_first_zero {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v : Fin n} (h : IsNode U p x v) (hp : ValidThrough U p n) :
    (∀ k, x.val < k → k ≤ v.val →
      (intervalVerticalCount U x.val k : ℤ) - (intervalHorizontalGrade U x.val k : ℤ) ≤ -1) ∧
    (intervalVerticalCount U x.val (v.val + 1) : ℤ) -
      (intervalHorizontalGrade U x.val (v.val + 1) : ℤ) = 0 := by
  constructor
  · intro k hxk hkv
    have hl := h.horizontal_shadow_prefix hp hxk hkv
    omega
  · rw [h.horizontal_shadow_equality hp]
    omega

#print axioms interval_count_eq_sum_load
#print axioms node_prefix_load
#print axioms node_debt_sum
#print axioms node_first_zero
end
end KroneckerShadowDebtHelpers

