import KroneckerPaperNodes
import KroneckerCompatibility

/-!
# A node ends at its first horizontal-shadow equality

The interval counts use edge occurrences, rather than equality of characters.
All conclusions follow from the literal h-precursor conditions and
the saturated predecessor fiber defining a node; no shadow identity is assumed.
-/
set_option autoImplicit false
namespace KroneckerPredecessor
noncomputable section
open KroneckerStack

/-- Occurrences at or after character boundary `a` and before boundary `k`. -/
def intervalEdges {n : ℕ} (a k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun w => a ≤ w.val ∧ w.val < k

@[simp] theorem mem_intervalEdges {n a k : ℕ} {w : Fin n} :
    w ∈ intervalEdges a k ↔ a ≤ w.val ∧ w.val < k := by
  simp [intervalEdges]

/-- The sum of horizontal grades in a subword. -/
def intervalHorizontalGrade {n : ℕ} (U : Word n) (a k : ℕ) : ℕ := by
  classical
  exact ∑ y ∈ intervalEdges a k, if IsHorizontal U y then (U y).grade else 0

/-- The number of vertical occurrences in a subword. -/
def intervalVerticalCount {n : ℕ} (U : Word n) (a k : ℕ) : ℕ := by
  classical
  exact ∑ w ∈ intervalEdges a k, if ¬ IsHorizontal U w then 1 else 0

private def intervalLoad {n : ℕ} (U : Word n) (p : Fin n → Fin n)
    (a k : ℕ) (y : Fin n) : ℕ := by
  classical
  exact ∑ w ∈ intervalEdges a k, if ¬ IsHorizontal U w ∧ p w = y then 1 else 0

private theorem intervalLoad_eq_load {n a k : ℕ} (U : Word n)
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

private theorem intervalLoad_zero_outside {n a k : ℕ} (U : Word n)
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
private theorem interval_count_eq_sum_load {n a k : ℕ} (U : Word n)
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

private theorem load_le_horizontal_grade {n k : ℕ} (U : Word n)
    (p : Fin n → Fin n) (hp : ValidThrough U p n) (hk : k ≤ n) (y : Fin n) :
    load U p k y ≤ if IsHorizontal U y then (U y).grade else 0 := by
  classical
  have h := load_le_capacity U p hk (valid_mono hp hk) y
  by_cases hy : IsHorizontal U y
  · simpa [hy] using load_le_grade U p hp hk y
  · simpa [capacity, hy] using h

private theorem IsNode.prefix_count_eq_sum_load {n k : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) (hk : k ≤ v.val + 1) :
    intervalVerticalCount U x.val k =
      ∑ y ∈ intervalEdges x.val k, load U p k y := by
  apply interval_count_eq_sum_load U p hp
  intro w hw hwV
  have hw' : w ∈ nodeOccurrences x v := by
    obtain ⟨hleft, hright⟩ := mem_intervalEdges.mp hw
    exact mem_nodeOccurrences.mpr ⟨hleft, by omega⟩
  exact (h.internal_assignment hp hw' hwV).2.1

private theorem IsNode.endpoint_load {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n} (h : IsNode U p x v) :
    load U p (v.val + 1) x = (U x).grade := by
  classical
  rw [← h.saturated]
  unfold load
  apply Finset.sum_subset
  · intro w hw
    exact mem_prefix.mpr w.isLt
  · intro w _ hwout
    by_cases hw : ¬ IsHorizontal U w ∧ p w = x
    · have hv := h.last_assigned w hw.1 hw.2
      have hnot := mt mem_prefix.mpr hwout
      omega
    · simp [hw]

/-- Every nonempty proper prefix of a node has horizontal grade strictly larger
than its number of vertical occurrences. -/
theorem IsNode.horizontal_shadow_prefix {n k : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hxk : x.val < k) (hkv : k ≤ v.val) :
    intervalVerticalCount U x.val k < intervalHorizontalGrade U x.val k := by
  classical
  rw [h.prefix_count_eq_sum_load hp (by omega)]
  unfold intervalHorizontalGrade
  apply Finset.sum_lt_sum
  · intro y _
    exact load_le_horizontal_grade U p hp (by omega) y
  · refine ⟨x, mem_intervalEdges.mpr ⟨le_rfl, hxk⟩, ?_⟩
    simpa [h.start_horizontal] using h.load_lt_before_end hp hkv

/-- At the ending edge of a node the horizontal grade equals the number of
vertical occurrences. Together with `horizontal_shadow_prefix`, this proves
that the ending edge is exactly the first horizontal-shadow equality. -/
theorem IsNode.horizontal_shadow_equality {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) :
    intervalVerticalCount U x.val (v.val + 1) =
      intervalHorizontalGrade U x.val (v.val + 1) := by
  classical
  rw [h.prefix_count_eq_sum_load hp le_rfl]
  unfold intervalHorizontalGrade
  apply Finset.sum_congr rfl
  intro y hy
  obtain ⟨hxy, hyv⟩ := mem_intervalEdges.mp hy
  by_cases hyH : IsHorizontal U y
  · simp only [hyH, ↓reduceIte]
    by_cases he : y = x
    · subst y
      exact h.endpoint_load
    · have hxy' : x.val < y.val := by
        have hne : x.val ≠ y.val := fun he' => he (Fin.ext he'.symm)
        omega
      have hs := h.interior_saturated hp hyH hxy' (by omega)
      have hm := load_mono U p (Nat.le_succ v.val) y
      have hb := load_le_grade (k := v.val + 1) U p hp (by omega) y
      apply Nat.le_antisymm hb
      rw [← hs]
      exact hm
  · have hb := load_le_horizontal_grade U p hp (show v.val + 1 ≤ n by omega) y
    simp only [hyH, ↓reduceIte] at hb ⊢
    omega

@[simp] theorem intervalEdges_zero {n k : ℕ} :
    @intervalEdges n 0 k = prefixEdges k := by
  ext w
  simp

@[simp] theorem intervalHorizontalGrade_zero {n : ℕ} (U : Word n) (k : ℕ) :
    intervalHorizontalGrade U 0 k = horizontalGrade U k := by
  simp [intervalHorizontalGrade, horizontalGrade_eq_sum]

@[simp] theorem intervalVerticalCount_zero {n : ℕ} (U : Word n) (k : ℕ) :
    intervalVerticalCount U 0 k = verticalCount U k := by
  simp [intervalVerticalCount, verticalCount]

/-- Conversion between the manuscript's finite occurrence counts and the
integer horizontal-shadow walk used by the cyclic compatibility theorem. -/
theorem debt_eq_prefix_counts (E : ℕ → Edge) (n k : ℕ) (hk : k ≤ n) :
    KroneckerCompatibility.debt E k =
      (horizontalGrade (fun i : Fin n => E i.val) k : ℤ) -
        (verticalCount (fun i : Fin n => E i.val) k : ℤ) := by
  classical
  induction k with
  | zero => simp [KroneckerCompatibility.debt, KroneckerCompatibility.walk,
      horizontalGrade, capacity]
  | succ k ih =>
    have hkn : k < n := by omega
    rw [KroneckerCompatibility.debt_step, horizontalGrade_succ _ hkn,
      verticalCount_succ _ hkn, ih (by omega)]
    cases he : E k <;> simp [IsHorizontal, he, Edge.grade, Edge.debtChange] <;> omega

/-- A node whose starting and ending occurrences are the first and last
occurrences of the word is the complete horizontal-shadow component required
by the cyclic witness theorem. -/
theorem full_node_root_component {n : ℕ} {E : ℕ → Edge}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode (fun i : Fin n => E i.val) p x v)
    (hp : ValidThrough (fun i : Fin n => E i.val) p n)
    (hx : x.val = 0) (hv : v.val + 1 = n) :
    KroneckerCompatibility.RootComponent E n := by
  have hn : 0 < n := by omega
  have hH := h.start_horizontal
  have hg := h.grade_pos hp
  have hpositive : KroneckerCompatibility.PositiveH E 0 := by
    change (match E x.val with | .H _ => True | .V _ => False) at hH
    change 0 < (E x.val).grade at hg
    rw [hx] at hH hg
    cases he : E 0 with
    | H g => exact ⟨g, by simpa [he, Edge.grade] using hg, he⟩
    | V g => simp [he] at hH
  refine ⟨hn, hpositive, ?_, ?_⟩
  · have heq := h.horizontal_shadow_equality hp
    rw [hx, hv, intervalHorizontalGrade_zero, intervalVerticalCount_zero] at heq
    rw [debt_eq_prefix_counts E n n le_rfl, heq]
    omega
  · intro k hk hkn
    have hlt := h.horizontal_shadow_prefix hp (show x.val < k by omega)
      (show k ≤ v.val by omega)
    rw [hx, intervalHorizontalGrade_zero, intervalVerticalCount_zero] at hlt
    rw [debt_eq_prefix_counts E n k (by omega)]
    omega

@[simp] theorem intervalEdges_self {n a : ℕ} : @intervalEdges n a a = ∅ := by
  ext w
  simp only [mem_intervalEdges, Finset.notMem_empty, iff_false, not_and]
  omega

private theorem intervalEdges_succ {n a k : ℕ} (hk : k < n) (ha : a ≤ k) :
    @intervalEdges n a (k + 1) = insert ⟨k, hk⟩ (intervalEdges a k) := by
  ext w
  simp only [mem_intervalEdges, Finset.mem_insert]
  constructor
  · rintro ⟨haw, hw⟩
    by_cases he : w.val = k
    · exact Or.inl (Fin.ext he)
    · exact Or.inr ⟨haw, by omega⟩
  · rintro (rfl | ⟨haw, hw⟩)
    · exact ⟨ha, Nat.lt_succ_self k⟩
    · exact ⟨haw, by omega⟩

private theorem intervalHorizontalGrade_succ {n a k : ℕ} (U : Word n)
    (hk : k < n) (ha : a ≤ k) :
    intervalHorizontalGrade U a (k + 1) = intervalHorizontalGrade U a k +
      if IsHorizontal U ⟨k, hk⟩ then (U ⟨k, hk⟩).grade else 0 := by
  classical
  simp [intervalHorizontalGrade, intervalEdges_succ hk ha, add_comm]

private theorem intervalVerticalCount_succ {n a k : ℕ} (U : Word n)
    (hk : k < n) (ha : a ≤ k) :
    intervalVerticalCount U a (k + 1) = intervalVerticalCount U a k +
      if ¬ IsHorizontal U ⟨k, hk⟩ then 1 else 0 := by
  classical
  simp [intervalVerticalCount, intervalEdges_succ hk ha, add_comm]

/-- Prefix capacity inequalities force every vertical occurrence in the
interval to have its predecessor in that interval. -/
theorem interval_assignments_internal {n a b : ℕ} (U : Word n)
    (p : Fin n → Fin n) (hp : ValidThrough U p n)
    (hprefix : ∀ k, a ≤ k → k ≤ b →
      intervalVerticalCount U a k ≤ intervalHorizontalGrade U a k) :
    ∀ w, w ∈ intervalEdges a b → ¬ IsHorizontal U w → a ≤ (p w).val := by
  classical
  have hind : ∀ t, ∀ w : Fin n, w.val = t → w ∈ intervalEdges a b →
      ¬ IsHorizontal U w → a ≤ (p w).val := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro w hwt hw hwV
      obtain ⟨haw, hwb⟩ := mem_intervalEdges.mp hw
      have hbefore : intervalVerticalCount U a w.val =
          ∑ y ∈ intervalEdges a w.val, load U p w.val y := by
        apply interval_count_eq_sum_load U p hp
        intro z hz hzV
        obtain ⟨haz, hzw⟩ := mem_intervalEdges.mp hz
        exact ih z.val (by omega) z rfl (mem_intervalEdges.mpr ⟨haz, by omega⟩) hzV
      have hafter := hprefix (w.val + 1) (by omega) (by omega)
      rw [intervalVerticalCount_succ U w.isLt haw,
        intervalHorizontalGrade_succ U w.isLt haw] at hafter
      have hsame : (⟨w.val, w.isLt⟩ : Fin n) = w := rfl
      simp only [hsame, hwV, not_false_eq_true, ↓reduceIte, add_zero] at hafter
      have hstrict : (∑ y ∈ intervalEdges a w.val, load U p w.val y) <
          ∑ y ∈ intervalEdges a w.val, if IsHorizontal U y then (U y).grade else 0 := by
        rw [← hbefore]
        change intervalVerticalCount U a w.val < intervalHorizontalGrade U a w.val
        omega
      have hex : ∃ y, y ∈ intervalEdges a w.val ∧
          load U p w.val y < if IsHorizontal U y then (U y).grade else 0 := by
        by_contra! hh
        have hge := Finset.sum_le_sum (s := intervalEdges a w.val)
          (fun y hy => hh y hy)
        omega
      obtain ⟨y, hy, hload⟩ := hex
      have hyH : IsHorizontal U y := by
        by_contra hh
        simp [hh] at hload
      simp only [hyH, ↓reduceIte] at hload
      have hyw := (mem_intervalEdges.mp hy).2
      have hlatest := (hp w w.isLt hwV).2.2.2 y hyH hyw hload
      have hay := (mem_intervalEdges.mp hy).1
      omega
  intro w hw hwV
  exact hind w.val w rfl hw hwV

/-- Conversely, a nonempty interval with positive proper horizontal-shadow
prefixes and zero final horizontal-shadow balance is exactly a node. -/
theorem isNode_of_first_horizontal_shadow {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n} (hp : ValidThrough U p n)
    (hxH : IsHorizontal U x) (_hvV : ¬ IsHorizontal U v) (hxv : x.val < v.val)
    (hfinal : intervalVerticalCount U x.val (v.val + 1) =
      intervalHorizontalGrade U x.val (v.val + 1))
    (hstrict : ∀ k, x.val < k → k ≤ v.val →
      intervalVerticalCount U x.val k < intervalHorizontalGrade U x.val k) :
    IsNode U p x v := by
  classical
  have hprefix : ∀ k, x.val ≤ k → k ≤ v.val + 1 →
      intervalVerticalCount U x.val k ≤ intervalHorizontalGrade U x.val k := by
    intro k hxk hkv
    by_cases he : k = x.val
    · subst k
      simp [intervalVerticalCount, intervalHorizontalGrade]
    · by_cases hk : k ≤ v.val
      · exact Nat.le_of_lt (hstrict k (by omega) hk)
      · have hk' : k = v.val + 1 := by omega
        simpa [hk'] using Nat.le_of_eq hfinal
  have hi := interval_assignments_internal U p hp hprefix
  have hcount := interval_count_eq_sum_load U p hp hi
  have hxmem : x ∈ intervalEdges x.val (v.val + 1) :=
    mem_intervalEdges.mpr ⟨le_rfl, by omega⟩
  have hs : load U p (v.val + 1) x = (U x).grade := by
    have hle := load_le_grade (k := v.val + 1) U p hp (by omega) x
    by_contra hne
    have hlt : (∑ y ∈ intervalEdges x.val (v.val + 1), load U p (v.val + 1) y) <
        ∑ y ∈ intervalEdges x.val (v.val + 1), if IsHorizontal U y then (U y).grade else 0 := by
      apply Finset.sum_lt_sum
      · intro y _
        exact load_le_horizontal_grade U p hp (by omega) y
      · refine ⟨x, hxmem, ?_⟩
        simp only [hxH, ↓reduceIte]
        omega
    rw [← hcount] at hlt
    change intervalVerticalCount U x.val (v.val + 1) <
      intervalHorizontalGrade U x.val (v.val + 1) at hlt
    omega
  have hfull : load U p n x = (U x).grade := by
    have hm := load_mono U p (show v.val + 1 ≤ n by omega) x
    have hb := load_le_grade U p hp le_rfl x
    omega
  have hg : 0 < (U x).grade := by
    have hfirst := hstrict (x.val + 1) (by omega) (by omega)
    rw [intervalVerticalCount_succ U x.isLt le_rfl,
      intervalHorizontalGrade_succ U x.isLt le_rfl] at hfirst
    simpa [hxH, intervalVerticalCount, intervalHorizontalGrade] using hfirst
  obtain ⟨w, hw⟩ := node_exists hxH hfull hg
  have hwv : w.val ≤ v.val := by
    have hb := assigned_lt_of_saturated_prefix hp hs hw.end_vertical hw.end_assigned
    omega
  have he : w = v := by
    apply Fin.ext
    by_contra hne
    have hlt := hstrict (w.val + 1) (by have := hw.start_lt_end hp; omega) (by omega)
    have heq := hw.horizontal_shadow_equality hp
    omega
  simpa [he] using hw

/-- The occurrence-based node definition and the first horizontal-shadow
equality describe the same subword. -/
theorem isNode_iff_first_horizontal_shadow {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n} (hp : ValidThrough U p n) :
    IsNode U p x v ↔ IsHorizontal U x ∧ ¬ IsHorizontal U v ∧ x.val < v.val ∧
      intervalVerticalCount U x.val (v.val + 1) =
        intervalHorizontalGrade U x.val (v.val + 1) ∧
      ∀ k, x.val < k → k ≤ v.val →
        intervalVerticalCount U x.val k < intervalHorizontalGrade U x.val k := by
  constructor
  · intro h
    exact ⟨h.start_horizontal, h.end_vertical, h.start_lt_end hp,
      h.horizontal_shadow_equality hp, fun _ hxk hkv => h.horizontal_shadow_prefix hp hxk hkv⟩
  · rintro ⟨hxH, hvV, hxv, heq, hstrict⟩
    exact isNode_of_first_horizontal_shadow hp hxH hvV hxv heq hstrict

/-- A complete horizontal-shadow component is the node from the first to the
last occurrence of its sampled finite word. -/
theorem root_component_full_node {n : ℕ} {E : ℕ → Edge}
    {p : Fin n → Fin n} (hr : KroneckerCompatibility.RootComponent E n)
    (hp : ValidThrough (fun i : Fin n => E i.val) p n) :
    ∃ x v : Fin n, IsNode (fun i : Fin n => E i.val) p x v ∧
      x.val = 0 ∧ v.val + 1 = n := by
  obtain ⟨g, hg, hzero⟩ := hr.2.1
  have hn : 2 ≤ n := by
    by_contra hsmall
    have hn1 : n = 1 := by have := hr.1; omega
    have hz := hr.2.2.1
    rw [hn1] at hz
    simp [KroneckerCompatibility.debt, KroneckerCompatibility.walk,
      hzero, Edge.debtChange] at hz
    omega
  let x : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨n - 1, by omega⟩
  have hv : v.val + 1 = n := by dsimp [v]; omega
  have hxH : IsHorizontal (fun i : Fin n => E i.val) x := by
    simp [IsHorizontal, x, hzero]
  have hvV : ¬ IsHorizontal (fun i : Fin n => E i.val) v := by
    have hpos := hr.2.2.2 v.val (by dsimp [v]; omega) v.isLt
    have hz : KroneckerCompatibility.debt E (v.val + 1) = 0 := by
      simpa [hv] using hr.2.2.1
    rw [KroneckerCompatibility.debt_step] at hz
    cases he : E v.val with
    | H j => simp [he, Edge.debtChange] at hz; omega
    | V j => simp [IsHorizontal, he]
  have hfinal : intervalVerticalCount (fun i : Fin n => E i.val) x.val (v.val + 1) =
      intervalHorizontalGrade (fun i : Fin n => E i.val) x.val (v.val + 1) := by
    change intervalVerticalCount (fun i : Fin n => E i.val) 0 (v.val + 1) = _
    rw [hv, intervalVerticalCount_zero, intervalHorizontalGrade_zero]
    have hz := hr.2.2.1
    rw [debt_eq_prefix_counts E n n le_rfl] at hz
    omega
  have hstrict : ∀ k, x.val < k → k ≤ v.val →
      intervalVerticalCount (fun i : Fin n => E i.val) x.val k <
        intervalHorizontalGrade (fun i : Fin n => E i.val) x.val k := by
    intro k hk hkv
    have hpref := hr.2.2.2 k hk (by omega)
    rw [debt_eq_prefix_counts E n k (by omega)] at hpref
    change intervalVerticalCount (fun i : Fin n => E i.val) 0 k <
      intervalHorizontalGrade (fun i : Fin n => E i.val) 0 k
    rw [intervalVerticalCount_zero, intervalHorizontalGrade_zero]
    omega
  refine ⟨x, v, isNode_of_first_horizontal_shadow hp hxH hvV ?_ hfinal hstrict, rfl, hv⟩
  dsimp [x, v]
  omega

end
end KroneckerPredecessor
