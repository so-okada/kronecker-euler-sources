import KroneckerPaperConnected

/-!
# Restricting a grading to a node

The subword is indexed through an explicit order-preserving embedding into the
ambient word. Its predecessor is the pullback of the ambient predecessor, not
a separately assumed assignment. The load and balance transport identities
justify the restriction of the connectedness conditions.
-/
set_option autoImplicit false
namespace KroneckerPredecessor
noncomputable section
open KroneckerStack

def restrictionLength {n : ℕ} (x v : Fin n) : ℕ := v.val + 1 - x.val

/-- This embedding retains the identity and order of every edge occurrence. -/
def restrictionEmbed {n : ℕ} (x v : Fin n)
    (i : Fin (restrictionLength x v)) : Fin n :=
  ⟨x.val + i.val, by have hi := i.isLt; unfold restrictionLength at hi; omega⟩

@[simp] theorem restrictionEmbed_val {n : ℕ} (x v : Fin n)
    (i : Fin (restrictionLength x v)) : (restrictionEmbed x v i).val = x.val + i.val := rfl

theorem restrictionEmbed_injective {n : ℕ} (x v : Fin n) :
    Function.Injective (restrictionEmbed x v) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [restrictionEmbed_val] at hv
  omega

theorem restrictionEmbed_mem {n : ℕ} (x v : Fin n)
    (i : Fin (restrictionLength x v)) : restrictionEmbed x v i ∈ nodeOccurrences x v := by
  have hi := i.isLt
  unfold restrictionLength at hi
  apply mem_nodeOccurrences.mpr
  simp only [restrictionEmbed_val]
  omega

/-- The subword inherits exactly the ambient grades. -/
def restrictionWord {n : ℕ} (U : Word n) (x v : Fin n) : Word (restrictionLength x v) :=
  fun i => U (restrictionEmbed x v i)

@[simp] theorem restrictionWord_apply {n : ℕ} (U : Word n) (x v : Fin n)
    (i : Fin (restrictionLength x v)) : restrictionWord U x v i = U (restrictionEmbed x v i) := rfl

@[simp] theorem restriction_isHorizontal {n : ℕ} (U : Word n) (x v : Fin n)
    (i : Fin (restrictionLength x v)) :
    IsHorizontal (restrictionWord U x v) i ↔ IsHorizontal U (restrictionEmbed x v i) := Iff.rfl

/-- The restricted predecessor keeps the ambient predecessor of every vertical
occurrence. Its values at horizontal occurrences are immaterial. -/
def restrictionMap {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) :
    Fin (restrictionLength x v) → Fin (restrictionLength x v) := fun i =>
  if hi : IsHorizontal (restrictionWord U x v) i then i else
    ⟨(p (restrictionEmbed x v i)).val - x.val, by
      have hV : ¬ IsHorizontal U (restrictionEmbed x v i) := hi
      obtain ⟨_, hleft, hright⟩ := h.internal_assignment hp (restrictionEmbed_mem x v i) hV
      have hmem := mem_nodeOccurrences.mp (restrictionEmbed_mem x v i)
      unfold restrictionLength
      omega⟩

theorem restrictionMap_embed {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n)
    (i : Fin (restrictionLength x v)) (hi : ¬ IsHorizontal (restrictionWord U x v) i) :
    restrictionEmbed x v (restrictionMap h hp i) = p (restrictionEmbed x v i) := by
  apply Fin.ext
  have hleft := (h.internal_assignment hp (restrictionEmbed_mem x v i) hi).2.1
  simp only [restrictionMap, dite_eq_right hi, restrictionEmbed_val]
  omega

/-- Loads are transported by the occurrence embedding. Assignments to an
occurrence of the subword cannot come from an earlier ambient prefix. -/
theorem restriction_load {n k : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hk : k ≤ restrictionLength x v) (j : Fin (restrictionLength x v)) :
    load (restrictionWord U x v) (restrictionMap h hp) k j =
      load U p (x.val + k) (restrictionEmbed x v j) := by
  classical
  let A := (prefixEdges k).filter fun i : Fin (restrictionLength x v) =>
    ¬ IsHorizontal (restrictionWord U x v) i ∧ restrictionMap h hp i = j
  let B := (prefixEdges (x.val + k)).filter fun w : Fin n =>
    ¬ IsHorizontal U w ∧ p w = restrictionEmbed x v j
  have hA : load (restrictionWord U x v) (restrictionMap h hp) k j = A.card := by
    simp [A, load]
  have hB : load U p (x.val + k) (restrictionEmbed x v j) = B.card := by
    simp [B, load]
  rw [hA, hB]
  apply Finset.card_bij (fun i _ => restrictionEmbed x v i)
  · intro i hi
    obtain ⟨hipre, hiV, hiq⟩ := Finset.mem_filter.mp hi
    have hip := mem_prefix.mp hipre
    have he := restrictionMap_embed h hp i hiV
    rw [hiq] at he
    apply Finset.mem_filter.mpr
    exact ⟨mem_prefix.mpr (by simp only [restrictionEmbed_val]; omega), hiV, he.symm⟩
  · intro i _ j _ hij
    exact restrictionEmbed_injective x v hij
  · intro w hw
    obtain ⟨hwpre, hwV, hwp⟩ := Finset.mem_filter.mp hw
    have hwk := mem_prefix.mp hwpre
    have hbefore := (hp w w.isLt hwV).2.1
    rw [hwp] at hbefore
    simp only [restrictionEmbed_val] at hbefore
    have hwx : x.val ≤ w.val := by omega
    let i : Fin (restrictionLength x v) := ⟨w.val - x.val, by omega⟩
    have hei : restrictionEmbed x v i = w := by
      apply Fin.ext
      change x.val + (w.val - x.val) = w.val
      omega
    have hiV : ¬ IsHorizontal (restrictionWord U x v) i := by
      simpa only [restriction_isHorizontal, hei] using hwV
    have hiq : restrictionMap h hp i = j := by
      apply restrictionEmbed_injective x v
      rw [restrictionMap_embed h hp i hiV, hei, hwp]
    refine ⟨i, Finset.mem_filter.mpr ⟨mem_prefix.mpr ?_, hiV, hiq⟩, hei⟩
    change w.val - x.val < k
    omega

/-- The pulled-back map satisfies all three predecessor conditions. -/
theorem restriction_valid {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) :
    ValidThrough (restrictionWord U x v) (restrictionMap h hp) (restrictionLength x v) := by
  intro i _ hiV
  let w := restrictionEmbed x v i
  have hwV : ¬ IsHorizontal U w := hiV
  obtain ⟨hwH, hwprior, hwrem, hwlast⟩ := hp w w.isLt hwV
  have he := restrictionMap_embed h hp i hiV
  have hpH : IsHorizontal (restrictionWord U x v) (restrictionMap h hp i) := by
    simpa only [restriction_isHorizontal, he] using hwH
  have hprior : (restrictionMap h hp i).val < i.val := by
    have hev := congrArg Fin.val he
    simp only [restrictionEmbed_val] at hev
    change (p (restrictionEmbed x v i)).val < x.val + i.val at hwprior
    omega
  refine ⟨hpH, hprior, ?_, ?_⟩
  · rw [restriction_load h hp (Nat.le_of_lt i.isLt), restrictionWord_apply, he]
    exact hwrem
  · intro j hjH hjprior hjrem
    rw [restriction_load h hp (Nat.le_of_lt i.isLt)] at hjrem
    have hjw : (restrictionEmbed x v j).val < w.val := by
      simp only [w, restrictionEmbed_val]
      omega
    have hb := hwlast (restrictionEmbed x v j) hjH hjw hjrem
    have hev := congrArg Fin.val he
    simp only [restrictionEmbed_val] at hev hb
    change x.val + j.val ≤ (p (restrictionEmbed x v i)).val at hb
    omega

/-- Restriction subtracts the balance at the starting character boundary. -/
theorem restriction_balance {n k : ℕ} (U : Word n) (x v : Fin n)
    (hk : k ≤ restrictionLength x v) :
    balance (restrictionWord U x v) k = balance U (x.val + k) - balance U x.val := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkl : k < restrictionLength x v := by omega
    have hkn : x.val + k < n := by
      unfold restrictionLength at hk
      omega
    rw [balance_succ (restrictionWord U x v) hkl, ih (by omega),
      Nat.add_succ, balance_succ U hkn]
    have he : restrictionWord U x v ⟨k, hkl⟩ = U ⟨x.val + k, hkn⟩ := rfl
    rw [he]
    omega

/-- All node baselines receive exactly the same translation under restriction. -/
theorem restriction_baseline {n : ℕ} (U : Word n) (x v : Fin n)
    (y : Fin (restrictionLength x v)) :
    baseline (restrictionWord U x v) y =
      baseline U (restrictionEmbed x v y) - balance U x.val := by
  unfold baseline
  rw [restriction_balance U x v (by omega)]
  rfl

/-- The owned-edge balance inequality is invariant under restriction. -/
theorem restriction_balance_inequality_iff {n : ℕ} (U : Word n) (x v : Fin n)
    (y w : Fin (restrictionLength x v)) :
    baseline (restrictionWord U x v) y ≤ balance (restrictionWord U x v) (w.val + 1) ↔
      baseline U (restrictionEmbed x v y) ≤ balance U ((restrictionEmbed x v w).val + 1) := by
  rw [restriction_baseline, restriction_balance U x v (by omega)]
  change baseline U (restrictionEmbed x v y) - balance U x.val ≤
    balance U ((restrictionEmbed x v w).val + 1) - balance U x.val ↔ _
  omega


/-- A node of the restricted grading is exactly the same interval of ambient
edge occurrences, with the same saturated predecessor fiber. -/
theorem restriction_node_ambient {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n)
    {y z : Fin (restrictionLength x v)}
    (hs : IsNode (restrictionWord U x v) (restrictionMap h hp) y z) :
    IsNode U p (restrictionEmbed x v y) (restrictionEmbed x v z) := by
  have he := restrictionMap_embed h hp z hs.end_vertical
  rw [hs.end_assigned] at he
  have hsaturate : load U p (x.val + restrictionLength x v) (restrictionEmbed x v y) =
      (U (restrictionEmbed x v y)).grade := by
    rw [← restriction_load h hp le_rfl]
    exact hs.saturated
  have hlen : x.val + restrictionLength x v ≤ n := by
    have hxv := h.start_lt_end hp
    unfold restrictionLength
    omega
  have hfull : load U p n (restrictionEmbed x v y) = (U (restrictionEmbed x v y)).grade := by
    have hm := load_mono U p hlen (restrictionEmbed x v y)
    have hb := load_le_grade U p hp le_rfl (restrictionEmbed x v y)
    omega
  refine ⟨hs.start_horizontal, hs.end_vertical, he.symm, hfull, ?_⟩
  intro w hwV hw
  have hwlast := assigned_lt_of_saturated_prefix hp hsaturate hwV hw
  have hwprior := (hp w w.isLt hwV).2.1
  rw [hw] at hwprior
  simp only [restrictionEmbed_val] at hwprior
  let i : Fin (restrictionLength x v) := ⟨w.val - x.val, by omega⟩
  have hei : restrictionEmbed x v i = w := by
    apply Fin.ext
    change x.val + (w.val - x.val) = w.val
    omega
  have hiV : ¬ IsHorizontal (restrictionWord U x v) i := by
    simpa only [restriction_isHorizontal, hei] using hwV
  have hiq : restrictionMap h hp i = y := by
    apply restrictionEmbed_injective x v
    rw [restrictionMap_embed h hp i hiV, hei, hw]
  have hz := hs.last_assigned i hiV hiq
  change w.val - x.val ≤ z.val at hz
  simp only [restrictionEmbed_val]
  omega

/-- Each owned-edge inequality pulls back along the occurrence embedding. -/
theorem restriction_ownedBalance {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) (hb : OwnedBalance U p) :
    OwnedBalance (restrictionWord U x v) (restrictionMap h hp) := by
  intro y z hs w hwV hw
  apply (restriction_balance_inequality_iff U x v y w).mpr
  have he := restrictionMap_embed h hp w hwV
  rw [hw] at he
  exact hb (restrictionEmbed x v y) (restrictionEmbed x v z)
    (restriction_node_ambient h hp hs) (restrictionEmbed x v w) hwV he.symm

theorem IsNode.load_at_end {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) : load U p (v.val + 1) x = (U x).grade := by
  classical
  rw [← h.saturated]
  unfold load
  apply Finset.sum_subset
  · intro w _
    exact mem_prefix.mpr w.isLt
  · intro w _ hwout
    by_cases hw : ¬ IsHorizontal U w ∧ p w = x
    · have hv := h.last_assigned w hw.1 hw.2
      have hnot := mt mem_prefix.mpr hwout
      omega
    · simp [hw]

/-- The restricted grading has a node spanning its entire word. -/
theorem restriction_fullRoot {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) :
    ∃ y z : Fin (restrictionLength x v),
      IsNode (restrictionWord U x v) (restrictionMap h hp) y z ∧
        y.val = 0 ∧ z.val + 1 = restrictionLength x v := by
  have hxv := h.start_lt_end hp
  have hlen : 0 < restrictionLength x v := by unfold restrictionLength; omega
  let y : Fin (restrictionLength x v) := ⟨0, hlen⟩
  let z : Fin (restrictionLength x v) := ⟨restrictionLength x v - 1, by omega⟩
  have hey : restrictionEmbed x v y = x := by apply Fin.ext; simp [y]
  have hez : restrictionEmbed x v z = v := by
    apply Fin.ext
    simp only [restrictionEmbed_val]
    change x.val + (restrictionLength x v - 1) = v.val
    unfold restrictionLength
    omega
  have hyH : IsHorizontal (restrictionWord U x v) y := by
    simpa only [restriction_isHorizontal, hey] using h.start_horizontal
  have hzV : ¬ IsHorizontal (restrictionWord U x v) z := by
    simpa only [restriction_isHorizontal, hez] using h.end_vertical
  have hzy : restrictionMap h hp z = y := by
    apply restrictionEmbed_injective x v
    rw [restrictionMap_embed h hp z hzV, hez, hey, h.end_assigned]
  have hs : load (restrictionWord U x v) (restrictionMap h hp) (restrictionLength x v) y =
      (restrictionWord U x v y).grade := by
    rw [restriction_load h hp le_rfl, hey]
    have hlength : x.val + restrictionLength x v = v.val + 1 := by
      unfold restrictionLength
      omega
    rw [hlength, h.load_at_end, restrictionWord_apply, hey]
  refine ⟨y, z, ⟨hyH, hzV, hzy, hs, ?_⟩, rfl, ?_⟩
  · intro w _ _
    have hw := w.isLt
    change w.val ≤ restrictionLength x v - 1
    omega
  · change restrictionLength x v - 1 + 1 = restrictionLength x v
    omega

/-- All three literal connectedness requirements hold on the inherited node
word, with the pulled-back h-precursor. -/
theorem IsNode.restriction_connected_data {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) (hb : OwnedBalance U p) :
    ∃ q : Fin (restrictionLength x v) → Fin (restrictionLength x v),
      ValidThrough (restrictionWord U x v) q (restrictionLength x v) ∧
      OwnedBalance (restrictionWord U x v) q ∧
      ∃ y z : Fin (restrictionLength x v), IsNode (restrictionWord U x v) q y z ∧
        y.val = 0 ∧ z.val + 1 = restrictionLength x v :=
  ⟨restrictionMap h hp, restriction_valid h hp, restriction_ownedBalance h hp hb,
    restriction_fullRoot h hp⟩

/-- The grading inherited by any node is connected in the literal manuscript
sense. No connectedness property is inserted as a construction hypothesis. -/
theorem IsNode.restriction_connected {n : ℕ} {U : Word n}
    {p : Fin n → Fin n} {x v : Fin n}
    (h : IsNode U p x v) (hp : ValidThrough U p n) (hb : OwnedBalance U p) :
    KroneckerPaperConnected.FiniteConnected (restrictionWord U x v) :=
  h.restriction_connected_data hp hb

#print axioms KroneckerPredecessor.IsNode.restriction_connected_data
#print axioms KroneckerPredecessor.IsNode.restriction_connected

end
end KroneckerPredecessor
