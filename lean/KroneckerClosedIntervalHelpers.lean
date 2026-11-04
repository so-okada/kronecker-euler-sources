import KroneckerPaperNodeRestriction

/-! Restriction to every nonempty interval closed under the h-precursor.
The endpoints x,v need not form a node. Manuscript U[a,b] corresponds to
x.val=a, v.val=b-1. Existing occurrence embeddings and balance formulas
are independent of any node hypothesis. -/
set_option autoImplicit false
namespace KroneckerPredecessor
noncomputable section
open KroneckerStack

/-- Vertical occurrences of the interval have owners in that interval;
the upper bound follows from the predecessor-before-edge condition. -/
def ClosedInterval {n : ℕ} (U : Word n) (p : Fin n → Fin n) (x v : Fin n) : Prop :=
  ∀ w ∈ nodeOccurrences x v, ¬ IsHorizontal U w → x.val ≤ (p w).val

/-- The restricted predecessor keeps the ambient predecessor of every vertical
occurrence. Its values at horizontal occurrences are immaterial. -/
def closedMap {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n) :
    Fin (restrictionLength x v) → Fin (restrictionLength x v) := fun i =>
  if hi : IsHorizontal (restrictionWord U x v) i then i else
    ⟨(p (restrictionEmbed x v i)).val - x.val, by
      have hV : ¬ IsHorizontal U (restrictionEmbed x v i) := hi
      have hleft := h _ (restrictionEmbed_mem x v i) hV
      have hright := (hp _ (restrictionEmbed x v i).isLt hV).2.1
      have hmem := mem_nodeOccurrences.mp (restrictionEmbed_mem x v i)
      unfold restrictionLength
      omega⟩

theorem closedMap_embed {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n)
    (i : Fin (restrictionLength x v)) (hi : ¬ IsHorizontal (restrictionWord U x v) i) :
    restrictionEmbed x v (closedMap h hp i) = p (restrictionEmbed x v i) := by
  apply Fin.ext
  have hleft := h _ (restrictionEmbed_mem x v i) hi
  simp only [closedMap, dite_eq_right hi, restrictionEmbed_val]
  omega

/-- Loads are transported by the occurrence embedding. Assignments to an
occurrence of the subword cannot come from an earlier ambient prefix. -/
theorem closed_load {n k : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n)
    (hk : k ≤ restrictionLength x v) (j : Fin (restrictionLength x v)) :
    load (restrictionWord U x v) (closedMap h hp) k j =
      load U p (x.val + k) (restrictionEmbed x v j) := by
  classical
  let A := (prefixEdges k).filter fun i : Fin (restrictionLength x v) =>
    ¬ IsHorizontal (restrictionWord U x v) i ∧ closedMap h hp i = j
  let B := (prefixEdges (x.val + k)).filter fun w : Fin n =>
    ¬ IsHorizontal U w ∧ p w = restrictionEmbed x v j
  have hA : load (restrictionWord U x v) (closedMap h hp) k j = A.card := by
    simp [A, load]
  have hB : load U p (x.val + k) (restrictionEmbed x v j) = B.card := by
    simp [B, load]
  rw [hA, hB]
  apply Finset.card_bij (fun i _ => restrictionEmbed x v i)
  · intro i hi
    obtain ⟨hipre, hiV, hiq⟩ := Finset.mem_filter.mp hi
    have hip := mem_prefix.mp hipre
    have he := closedMap_embed h hp i hiV
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
    have hiq : closedMap h hp i = j := by
      apply restrictionEmbed_injective x v
      rw [closedMap_embed h hp i hiV, hei, hwp]
    refine ⟨i, Finset.mem_filter.mpr ⟨mem_prefix.mpr ?_, hiV, hiq⟩, hei⟩
    change w.val - x.val < k
    omega

/-- The pulled-back map satisfies all three predecessor conditions. -/
theorem closed_valid {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n) :
    ValidThrough (restrictionWord U x v) (closedMap h hp) (restrictionLength x v) := by
  intro i _ hiV
  let w := restrictionEmbed x v i
  have hwV : ¬ IsHorizontal U w := hiV
  obtain ⟨hwH, hwprior, hwrem, hwlast⟩ := hp w w.isLt hwV
  have he := closedMap_embed h hp i hiV
  have hpH : IsHorizontal (restrictionWord U x v) (closedMap h hp i) := by
    simpa only [restriction_isHorizontal, he] using hwH
  have hprior : (closedMap h hp i).val < i.val := by
    have hev := congrArg Fin.val he
    simp only [restrictionEmbed_val] at hev
    change (p (restrictionEmbed x v i)).val < x.val + i.val at hwprior
    omega
  refine ⟨hpH, hprior, ?_, ?_⟩
  · rw [closed_load h hp (Nat.le_of_lt i.isLt), restrictionWord_apply, he]
    exact hwrem
  · intro j hjH hjprior hjrem
    rw [closed_load h hp (Nat.le_of_lt i.isLt)] at hjrem
    have hjw : (restrictionEmbed x v j).val < w.val := by
      simp only [w, restrictionEmbed_val]
      omega
    have hb := hwlast (restrictionEmbed x v j) hjH hjw hjrem
    have hev := congrArg Fin.val he
    simp only [restrictionEmbed_val] at hev hb
    change x.val + j.val ≤ (p (restrictionEmbed x v i)).val at hb
    omega

/-- A node of the restricted grading is exactly the same interval of ambient
edge occurrences, with the same saturated predecessor fiber. -/
theorem closed_node_ambient {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n)
    {y z : Fin (restrictionLength x v)}
    (hs : IsNode (restrictionWord U x v) (closedMap h hp) y z) :
    IsNode U p (restrictionEmbed x v y) (restrictionEmbed x v z) := by
  have he := closedMap_embed h hp z hs.end_vertical
  rw [hs.end_assigned] at he
  have hsaturate : load U p (x.val + restrictionLength x v) (restrictionEmbed x v y) =
      (U (restrictionEmbed x v y)).grade := by
    rw [← closed_load h hp le_rfl]
    exact hs.saturated
  have hlen : x.val + restrictionLength x v ≤ n := by
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
  have hiq : closedMap h hp i = y := by
    apply restrictionEmbed_injective x v
    rw [closedMap_embed h hp i hiV, hei, hw]
  have hz := hs.last_assigned i hiV hiq
  change w.val - x.val ≤ z.val at hz
  simp only [restrictionEmbed_val]
  omega

/-- Each owned-edge inequality pulls back along the occurrence embedding. -/
theorem closed_ownedBalance {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n) (hb : OwnedBalance U p) :
    OwnedBalance (restrictionWord U x v) (closedMap h hp) := by
  intro y z hs w hwV hw
  apply (restriction_balance_inequality_iff U x v y w).mpr
  have he := closedMap_embed h hp w hwV
  rw [hw] at he
  exact hb (restrictionEmbed x v y) (restrictionEmbed x v z)
    (closed_node_ambient h hp hs) (restrictionEmbed x v w) hwV he.symm


/-- The reverse direction uses the complete ambient fiber, whose last index
is inside the restricted interval. -/
theorem ambient_node_closed {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n)
    {y z : Fin (restrictionLength x v)}
    (hs : IsNode U p (restrictionEmbed x v y) (restrictionEmbed x v z)) :
    IsNode (restrictionWord U x v) (closedMap h hp) y z := by
  have he : closedMap h hp z = y := by
    apply restrictionEmbed_injective x v
    rw [closedMap_embed h hp z hs.end_vertical, hs.end_assigned]
  refine ⟨hs.start_horizontal, hs.end_vertical, he, ?_, ?_⟩
  · rw [closed_load h hp le_rfl]
    have hm := load_mono U p
      (show (restrictionEmbed x v z).val + 1 ≤ x.val + restrictionLength x v by
        simp only [restrictionEmbed_val]; omega) (restrictionEmbed x v y)
    have hl : x.val + restrictionLength x v ≤ n := by unfold restrictionLength; omega
    have hb := load_le_grade U p hp hl (restrictionEmbed x v y)
    rw [hs.load_at_end] at hm
    exact Nat.le_antisymm hb hm
  · intro w hwV hw
    have hew := closedMap_embed h hp w hwV
    rw [hw] at hew
    have ht := hs.last_assigned (restrictionEmbed x v w) hwV hew.symm
    simp only [restrictionEmbed_val] at ht
    omega

theorem closed_node_iff {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n)
    (y z : Fin (restrictionLength x v)) :
    IsNode (restrictionWord U x v) (closedMap h hp) y z ↔
      IsNode U p (restrictionEmbed x v y) (restrictionEmbed x v z) :=
  ⟨closed_node_ambient h hp, ambient_node_closed h hp⟩

/-- Combined contract: the explicit pullback is valid, every node corresponds
in both directions, and all node balance inequalities restrict. -/
theorem closed_restriction {n : ℕ} {U : Word n} {p : Fin n → Fin n} {x v : Fin n}
    (h : ClosedInterval U p x v) (hp : ValidThrough U p n) :
    ValidThrough (restrictionWord U x v) (closedMap h hp) (restrictionLength x v) ∧
    (∀ y z, IsNode (restrictionWord U x v) (closedMap h hp) y z ↔
      IsNode U p (restrictionEmbed x v y) (restrictionEmbed x v z)) ∧
    (OwnedBalance U p → OwnedBalance (restrictionWord U x v) (closedMap h hp)) :=
  ⟨closed_valid h hp, closed_node_iff h hp, closed_ownedBalance h hp⟩

#print axioms closedMap_embed
#print axioms closed_load
#print axioms closed_valid
#print axioms closed_node_iff
#print axioms closed_ownedBalance
#print axioms closed_restriction
end
end KroneckerPredecessor
