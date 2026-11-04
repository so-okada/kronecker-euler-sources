import KroneckerPaperPredecessor

/-!
# Nodes as literal subwords of a graded word

An endpoint is selected by the saturated fiber of the h-precursor
map. In particular, this definition imposes no balance inequality. The results
below prove the internal-assignment and nesting assertions directly from the
three defining predecessor conditions.
-/
set_option autoImplicit false
namespace KroneckerPredecessor
noncomputable section
open KroneckerStack

/-- The interval from horizontal occurrence `x` through its last assigned
vertical occurrence `v`. Its definition is independent of all vertical grades. -/
structure IsNode {n : ℕ} (U : Word n) (p : Fin n → Fin n)
    (x v : Fin n) : Prop where
  start_horizontal : IsHorizontal U x
  end_vertical : ¬ IsHorizontal U v
  end_assigned : p v = x
  saturated : load U p n x = (U x).grade
  last_assigned : ∀ w : Fin n, ¬ IsHorizontal U w → p w = x → w.val ≤ v.val

/-- A node retains the edge occurrences of the ambient word. -/
def nodeOccurrences {n : ℕ} (x v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w => x.val ≤ w.val ∧ w.val ≤ v.val

@[simp] theorem mem_nodeOccurrences {n : ℕ} {x v w : Fin n} :
    w ∈ nodeOccurrences x v ↔ x.val ≤ w.val ∧ w.val ≤ v.val := by
  simp [nodeOccurrences]

/-- The literal subword, with the grading inherited from the ambient word. -/
def nodeSubword {n : ℕ} (U : Word n) (x v : Fin n) : List Edge :=
  ((List.finRange n).filter fun w => x.val ≤ w.val ∧ w.val ≤ v.val).map U

theorem load_mono {n k l : ℕ} (U : Word n) (p : Fin n → Fin n)
    (hkl : k ≤ l) (x : Fin n) : load U p k x ≤ load U p l x := by
  classical
  unfold load
  apply Finset.sum_le_sum_of_subset
  intro w hw
  simp only [mem_prefix] at hw ⊢
  omega

theorem load_le_grade {n k : ℕ} (U : Word n) (p : Fin n → Fin n)
    (hp : ValidThrough U p n) (hk : k ≤ n) (x : Fin n) :
    load U p k x ≤ (U x).grade := by
  have h := load_le_capacity U p hk (valid_mono hp hk) x
  unfold capacity at h
  split_ifs at h <;> omega

theorem IsNode.start_lt_end {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v : Fin n} (h : IsNode U p x v) (hp : ValidThrough U p n) :
    x.val < v.val := by
  have hv := (hp v v.isLt h.end_vertical).2.1
  simpa [h.end_assigned] using hv

theorem IsNode.grade_pos {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v : Fin n} (h : IsNode U p x v) (hp : ValidThrough U p n) :
    0 < (U x).grade := by
  have hv := (hp v v.isLt h.end_vertical).2.2.1
  rw [h.end_assigned] at hv
  omega

theorem IsNode.load_lt_before_end {n k : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) (hk : k ≤ v.val) :
    load U p k x < (U x).grade := by
  have hv := (hp v v.isLt h.end_vertical).2.2.1
  rw [h.end_assigned] at hv
  exact lt_of_le_of_lt (load_mono U p hk x) hv

/-- Every vertical occurrence in a node is assigned within that interval. -/
theorem IsNode.internal_assignment {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v w : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hw : w ∈ nodeOccurrences x v) (hwV : ¬ IsHorizontal U w) :
    IsHorizontal U (p w) ∧ x.val ≤ (p w).val ∧ (p w).val < w.val := by
  obtain ⟨hxw, hwv⟩ := mem_nodeOccurrences.mp hw
  have hxne : x ≠ w := by intro he; exact hwV (he ▸ h.start_horizontal)
  have hxlt : x.val < w.val := by
    have hne : x.val ≠ w.val := fun he => hxne (Fin.ext he)
    omega
  obtain ⟨hH, hlt, _, hlast⟩ := hp w w.isLt hwV
  exact ⟨hH, hlast x h.start_horizontal hxlt (h.load_lt_before_end hp hwv), hlt⟩

/-- Once a horizontal occurrence has received its full grade, no subsequent
vertical occurrence can be assigned to it. -/
theorem assigned_lt_of_saturated_prefix {n k : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x w : Fin n} (hp : ValidThrough U p n)
    (hk : load U p k x = (U x).grade)
    (hwV : ¬ IsHorizontal U w) (hw : p w = x) : w.val < k := by
  have hrem := (hp w w.isLt hwV).2.2.1
  rw [hw] at hrem
  by_contra h
  have hm := load_mono U p (show k ≤ w.val by omega) x
  omega

/-- A positive horizontal occurrence inside a node has exhausted its capacity
before the ending edge of the containing node. -/
theorem IsNode.interior_saturated {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v y : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hyH : IsHorizontal U y) (hxy : x.val < y.val) (hyv : y.val ≤ v.val) :
    load U p v.val y = (U y).grade := by
  have hyne : y ≠ v := by intro he; exact h.end_vertical (he ▸ hyH)
  have hylt : y.val < v.val := by
    have hne : y.val ≠ v.val := fun he => hyne (Fin.ext he)
    omega
  have hle := load_le_grade U p hp (Nat.le_of_lt v.isLt) y
  by_contra hne
  have hlt : load U p v.val y < (U y).grade := by omega
  have hlast := (hp v v.isLt h.end_vertical).2.2.2 y hyH hylt hlt
  rw [h.end_assigned] at hlast
  omega

/-- The fiber of a horizontal occurrence, as a set of vertical occurrences. -/
def assignedEdges {n : ℕ} (U : Word n) (p : Fin n → Fin n) (x : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun w => ¬ IsHorizontal U w ∧ p w = x

@[simp] theorem mem_assignedEdges {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x w : Fin n} : w ∈ assignedEdges U p x ↔ ¬ IsHorizontal U w ∧ p w = x := by
  classical
  simp [assignedEdges]

theorem load_eq_card_assigned {n : ℕ} (U : Word n) (p : Fin n → Fin n) (x : Fin n) :
    load U p n x = (assignedEdges U p x).card := by
  classical
  have hp : @prefixEdges n n = Finset.univ := by ext i; simp [i.isLt]
  simp [load, hp, assignedEdges]

/-- Saturation and positive grade determine an ending occurrence, without a
balance assumption. -/
theorem node_exists {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x : Fin n}
    (hxH : IsHorizontal U x) (hs : load U p n x = (U x).grade)
    (hg : 0 < (U x).grade) : ∃ v, IsNode U p x v := by
  classical
  have ha : (assignedEdges U p x).Nonempty := by
    apply Finset.card_pos.mp
    rw [← load_eq_card_assigned, hs]
    exact hg
  let v := (assignedEdges U p x).max' ha
  have hv := mem_assignedEdges.mp (Finset.max'_mem _ ha)
  refine ⟨v, hxH, hv.1, hv.2, hs, ?_⟩
  intro w hwV hw
  exact Finset.le_max' _ w (mem_assignedEdges.mpr ⟨hwV, hw⟩)

/-- The endpoint selected by a saturated predecessor fiber is unique. -/
theorem IsNode.end_unique {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v w : Fin n} (hv : IsNode U p x v) (hw : IsNode U p x w) : v = w := by
  apply Fin.ext
  have h1 := hv.last_assigned w hw.end_vertical hw.end_assigned
  have h2 := hw.last_assigned v hv.end_vertical hv.end_assigned
  omega

/-- Every positive horizontal occurrence strictly inside a node has its own
completed node, ending strictly before the containing node. -/
theorem IsNode.interior_node {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v y : Fin n} (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hyH : IsHorizontal U y) (hxy : x.val < y.val) (hyv : y.val ≤ v.val)
    (hyg : 0 < (U y).grade) : ∃ z, IsNode U p y z ∧ z.val < v.val := by
  have hs := h.interior_saturated hp hyH hxy hyv
  have hsfull : load U p n y = (U y).grade := by
    have hm := load_mono U p (Nat.le_of_lt v.isLt) y
    have hb := load_le_grade U p hp le_rfl y
    omega
  obtain ⟨z, hz⟩ := node_exists hyH hsfull hyg
  exact ⟨z, hz, assigned_lt_of_saturated_prefix hp hs hz.end_vertical hz.end_assigned⟩

/-- Two nodes have disjoint intervals, or one interval contains the other. -/
theorem IsNode.disjoint_or_nested {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v y w : Fin n} (hx : IsNode U p x v) (hy : IsNode U p y w)
    (hp : ValidThrough U p n) :
    v.val < y.val ∨ w.val < x.val ∨
      (x.val ≤ y.val ∧ w.val ≤ v.val) ∨ (y.val ≤ x.val ∧ v.val ≤ w.val) := by
  by_cases he : x = y
  · subst y
    have hvw := hx.end_unique hy
    subst w
    exact Or.inr (Or.inr (Or.inl ⟨le_rfl, le_rfl⟩))
  have hne : x.val ≠ y.val := fun h => he (Fin.ext h)
  by_cases hxy : x.val < y.val
  · by_cases hyv : y.val ≤ v.val
    · obtain ⟨z, hz, hzv⟩ := hx.interior_node hp hy.start_horizontal hxy hyv (hy.grade_pos hp)
      have hew := hz.end_unique hy
      subst z
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · exact Or.inl (by omega)
  · have hyx : y.val < x.val := by omega
    by_cases hxw : x.val ≤ w.val
    · obtain ⟨z, hz, hzw⟩ := hy.interior_node hp hx.start_horizontal hyx hxw (hx.grade_pos hp)
      have hev := hz.end_unique hx
      subst z
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · exact Or.inr (Or.inl (by omega))

/-- Balance at a character boundary, using the grades in the ambient word. -/
def balance {n : ℕ} (U : Word n) (k : ℕ) : ℤ :=
  ∑ w ∈ prefixEdges k, (U w).credit

/-- The balance immediately after a horizontal starting occurrence. -/
def baseline {n : ℕ} (U : Word n) (x : Fin n) : ℤ := balance U (x.val + 1)

/-- The manuscript's inequality at every vertical edge owned by a node. -/
def OwnedBalance {n : ℕ} (U : Word n) (p : Fin n → Fin n) : Prop :=
  ∀ x v : Fin n, IsNode U p x v → ∀ w : Fin n,
    ¬ IsHorizontal U w → p w = x → baseline U x ≤ balance U (w.val + 1)

@[simp] theorem balance_zero {n : ℕ} (U : Word n) : balance U 0 = 0 := by
  simp [balance]

theorem balance_succ {n k : ℕ} (U : Word n) (hk : k < n) :
    balance U (k + 1) = balance U k + (U ⟨k, hk⟩).credit := by
  simp [balance, prefix_succ hk, add_comm]

theorem credit_horizontal {n : ℕ} {U : Word n} {x : Fin n}
    (hx : IsHorizontal U x) : (U x).credit = 1 := by
  cases he : U x with
  | H g => rfl
  | V g => simp [IsHorizontal, he] at hx

/-- Under the owned-edge inequalities, balance is bounded below by the node's
baseline at every character boundary within that node. -/
theorem IsNode.balance_lower_bound {n i : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) (hb : OwnedBalance U p)
    (hxi : x.val + 1 ≤ i) (hiv : i ≤ v.val + 1) :
    baseline U x ≤ balance U i := by
  have hind : ∀ j : ℕ, x.val + 1 ≤ j → j ≤ v.val + 1 →
      baseline U x ≤ balance U j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hxj hjv
      by_cases he : j = x.val + 1
      · simp [he, baseline]
      · have hjpos : 0 < j := by omega
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
        have hkn : k < n := by omega
        let w : Fin n := ⟨k, hkn⟩
        have hprev : baseline U x ≤ balance U k :=
          ih k (by omega) (by omega) (by omega)
        by_cases hwH : IsHorizontal U w
        · rw [balance_succ U hkn]
          have hc : (U ⟨k, hkn⟩).credit = 1 := credit_horizontal hwH
          rw [hc]
          omega
        · have hwm : w ∈ nodeOccurrences x v := mem_nodeOccurrences.mpr ⟨by dsimp [w]; omega, by dsimp [w]; omega⟩
          obtain ⟨hyH, hxy, hyw⟩ := h.internal_assignment hp hwm hwH
          change (p w).val < k at hyw
          by_cases hyx : p w = x
          · simpa [w] using hb x v h w hwH hyx
          · have hxylt : x.val < (p w).val := by
              have hne : x.val ≠ (p w).val := fun he => hyx (Fin.ext he.symm)
              omega
            have hyg : 0 < (U (p w)).grade := by
              have hrem := (hp w w.isLt hwH).2.2.1
              omega
            obtain ⟨z, hz, _⟩ := h.interior_node hp hyH hxylt (by omega) hyg
            have hbowner := hb (p w) z hz w hwH rfl
            have hbstart : baseline U x ≤ baseline U (p w) := by
              exact ih ((p w).val + 1) (by omega) (by omega) (by omega)
            exact hbstart.trans (by simpa [w] using hbowner)
  exact hind i hxi hiv

/-- A node starting strictly inside another node has a strictly larger baseline.
The hypothesis is precisely the owned-edge balance condition. -/
theorem IsNode.interior_baseline_lt {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v y : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) (hb : OwnedBalance U p)
    (hyH : IsHorizontal U y) (hxy : x.val < y.val) (hyv : y.val ≤ v.val) :
    baseline U x < baseline U y := by
  have hlower := h.balance_lower_bound hp hb (show x.val + 1 ≤ y.val by omega)
    (show y.val ≤ v.val + 1 by omega)
  unfold baseline
  have he : balance U (y.val + 1) = balance U y.val + 1 := by
    rw [balance_succ U y.isLt]
    simpa using credit_horizontal hyH
  rw [he]
  unfold baseline at hlower
  omega

/-- The number of horizontal occurrences in a literal node interval. -/
def nodeHorizontalCount {n : ℕ} (U : Word n) (x v : Fin n) : ℕ :=
  ((nodeOccurrences x v).filter (IsHorizontal U)).card

/-- The sum of vertical grades in a literal node interval. -/
def nodeVerticalGrade {n : ℕ} (U : Word n) (x v : Fin n) : ℕ :=
  ∑ w ∈ nodeOccurrences x v, if IsHorizontal U w then 0 else (U w).grade

/-- The surplus is the number of horizontal occurrences minus one minus the
sum of vertical grades. -/
def nodeSurplus {n : ℕ} (U : Word n) (x v : Fin n) : ℤ :=
  (nodeHorizontalCount U x v : ℤ) - 1 - (nodeVerticalGrade U x v : ℤ)

theorem node_balance_difference {n : ℕ} (U : Word n) (x v : Fin n)
    (hxv : x.val ≤ v.val) :
    balance U (v.val + 1) - balance U x.val = nodeSurplus U x v + 1 := by
  classical
  have hsub : @prefixEdges n x.val ⊆ prefixEdges (v.val + 1) := by
    intro w hw
    have hwx := mem_prefix.mp hw
    exact mem_prefix.mpr (by omega)
  have he : nodeOccurrences x v = prefixEdges (v.val + 1) \ prefixEdges x.val := by
    ext w
    simp only [mem_nodeOccurrences, Finset.mem_sdiff, mem_prefix]
    omega
  have hsum : balance U (v.val + 1) - balance U x.val =
      ∑ w ∈ nodeOccurrences x v, (U w).credit := by
    rw [he]
    exact (Finset.sum_sdiff_eq_sub hsub).symm
  rw [hsum]
  have hcredit : ∀ w : Fin n, (U w).credit =
      (if IsHorizontal U w then (1 : ℤ) else 0) -
      (if IsHorizontal U w then (0 : ℤ) else ((U w).grade : ℤ)) := by
    intro w
    cases hew : U w <;> simp [IsHorizontal, hew, Edge.credit, Edge.grade]
  simp_rw [hcredit]
  rw [Finset.sum_sub_distrib]
  have hH : (∑ w ∈ nodeOccurrences x v, if IsHorizontal U w then (1 : ℤ) else 0) =
      (nodeHorizontalCount U x v : ℤ) := by
    simp [nodeHorizontalCount]
  have hV : (∑ w ∈ nodeOccurrences x v, if IsHorizontal U w then (0 : ℤ) else ((U w).grade : ℤ)) =
      (nodeVerticalGrade U x v : ℤ) := by
    simp [nodeVerticalGrade]
  rw [hH, hV]
  unfold nodeSurplus
  omega

/-- The node surplus is nonnegative under the manuscript's owned-edge balance
inequalities; the displayed difference formula uses its literal edge counts. -/
theorem IsNode.surplus_nonnegative {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) (hb : OwnedBalance U p) :
    0 ≤ nodeSurplus U x v := by
  have hv := hb x v h v h.end_vertical h.end_assigned
  have hd := node_balance_difference U x v (Nat.le_of_lt (h.start_lt_end hp))
  have hx : baseline U x = balance U x.val + 1 := by
    unfold baseline
    rw [balance_succ U x.isLt]
    simpa using credit_horizontal h.start_horizontal
  rw [hx] at hv
  omega

/-- Choosing the unique saturated-fiber endpoint makes the node a literal
subword. Proof arguments certify its domain of definition. -/
def nodeEnding {n : ℕ} (U : Word n) (p : Fin n → Fin n) (x : Fin n)
    (hxH : IsHorizontal U x) (hs : load U p n x = (U x).grade)
    (hg : 0 < (U x).grade) : Fin n := (node_exists hxH hs hg).choose

theorem nodeEnding_spec {n : ℕ} (U : Word n) (p : Fin n → Fin n) (x : Fin n)
    (hxH : IsHorizontal U x) (hs : load U p n x = (U x).grade)
    (hg : 0 < (U x).grade) : IsNode U p x (nodeEnding U p x hxH hs hg) :=
  (node_exists hxH hs hg).choose_spec

/-- `Node` is defined by the predecessor fiber, without a balance hypothesis. -/
def Node {n : ℕ} (U : Word n) (p : Fin n → Fin n) (x : Fin n)
    (hxH : IsHorizontal U x) (hs : load U p n x = (U x).grade)
    (hg : 0 < (U x).grade) : List Edge :=
  nodeSubword U x (nodeEnding U p x hxH hs hg)

#print axioms KroneckerPredecessor.node_exists
#print axioms KroneckerPredecessor.IsNode.disjoint_or_nested
#print axioms KroneckerPredecessor.IsNode.balance_lower_bound

end
end KroneckerPredecessor
