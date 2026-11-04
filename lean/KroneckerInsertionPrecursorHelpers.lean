import KroneckerPrecursorDeletion
import KroneckerPaperNodes

/-! Exact reassignments on an indexed chain of ending edges. The added
vertical edge is `none`, and copied vertical edges are `some v`. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerInsertionPrecursorHelpers

variable {H V : Type*} [DecidableEq V]

def cycle : List V → Equiv.Perm (Option V)
  | [] => Equiv.refl _
  | t :: ts => (Equiv.swap none (some t)).trans (cycle ts)

theorem cycle_fixed (ts : List V) (v : V) (hv : v ∉ ts) :
    cycle ts (some v) = some v := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hv' : v ≠ t ∧ v ∉ ts := by simpa using hv
    have hne : some v ≠ (some t : Option V) := by simpa using hv'.1
    simp only [cycle, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) hne]
    exact ih hv'.2

theorem cycle_none_cons (t : V) (ts : List V) (ht : t ∉ ts) :
    cycle (t :: ts) none = some t := by
  simp only [cycle, Equiv.trans_apply, Equiv.swap_apply_left]
  exact cycle_fixed ts t ht

theorem cycle_at (ts : List V) (hn : ts.Nodup) (j : ℕ) (hj : j < ts.length) :
    cycle ts (some ts[j]) =
      if h : j+1 < ts.length then some ts[j+1] else none := by
  induction ts generalizing j with
  | nil => simp at hj
  | cons t ts ih =>
    obtain ⟨ht, hn⟩ := List.nodup_cons.mp hn
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, cycle, Equiv.trans_apply, Equiv.swap_apply_right]
      cases ts with
      | nil => rfl
      | cons u us =>
        simpa using cycle_none_cons u us (List.nodup_cons.mp hn).1
    | succ j =>
      have hj' : j < ts.length := by simpa using hj
      have hv : ts[j] ≠ t := by
        intro he
        exact ht (he ▸ List.getElem_mem hj')
      simp only [List.getElem_cons_succ, cycle, Equiv.trans_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hv)]
      simpa only [List.length_cons, Nat.succ_eq_add_one, Nat.add_lt_add_iff_right,
        List.getElem_cons_succ] using ih hn j hj'

def extend (p : V → H) (root : H) : Option V → H
  | none => root
  | some v => p v

def inserted (p : V → H) (root : H) (ts : List V) : Option V → H :=
  fun v => extend p root (cycle ts v)

theorem inserted_new (p : V → H) (root : H) (t : V) (ts : List V)
    (ht : t ∉ ts) : inserted p root (t :: ts) none = p t := by
  rw [inserted, cycle_none_cons t ts ht]
  rfl

theorem inserted_new_empty (p : V → H) (root : H) :
    inserted p root [] none = root := rfl

theorem inserted_unchanged (p : V → H) (root : H) (ts : List V)
    (v : V) (hv : v ∉ ts) : inserted p root ts (some v) = p v := by
  rw [inserted, cycle_fixed ts v hv]
  rfl

theorem inserted_ending (p : V → H) (root : H) (ts : List V) (hn : ts.Nodup)
    (j : ℕ) (hj : j < ts.length) :
    inserted p root ts (some ts[j]) =
      if h : j+1 < ts.length then p ts[j+1] else root := by
  rw [inserted, cycle_at ts hn j hj]
  split_ifs <;> rfl

/-- A bijection of actual assignment fibers, including the new root unit. -/
def fiberEquiv (p : V → H) (root x : H) (ts : List V) :
    {v : Option V // inserted p root ts v = x} ≃
      {v : Option V // extend p root v = x} :=
  (cycle ts).subtypeEquiv (fun _ => Iff.rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fiber_count [Fintype V] [DecidableEq H] (p : V → H) (root x : H) (ts : List V) :
    Nat.card {v : Option V // inserted p root ts v = x} =
      Nat.card {v : V // p v = x} + if root = x then 1 else 0 := by
  classical
  rw [Nat.card_congr (fiberEquiv p root x ts)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_option]
  simp only [extend, add_comm]

/-- Exact fiber transport; `cycle` is the explicit product of swaps defined
above, rather than an unspecified permutation. -/
theorem fiber_set (p : V → H) (root x : H) (ts : List V) :
    {v : Option V | inserted p root ts v = x} =
      (cycle ts).symm '' {v : Option V | extend p root v = x} := by
  ext v
  constructor
  · intro hv
    exact ⟨cycle ts v, hv, (cycle ts).symm_apply_apply v⟩
  · rintro ⟨w, hw, rfl⟩
    change extend p root (cycle ts ((cycle ts).symm w)) = x
    rw [Equiv.apply_symm_apply]
    exact hw

def prefixTest (index : V → ℕ) (k : ℕ) : Option V → Prop
  | none => True
  | some v => index v < k

def prefixCount [Fintype V] (index : V → ℕ) (k : ℕ)
    (f : Option V → H) (x : H) : ℕ := by
  classical
  exact ∑ v : Option V, if prefixTest index k v ∧ f v = x then 1 else 0

theorem prefixCount_extend [Fintype V] [DecidableEq H] (index : V → ℕ) (k : ℕ)
    (p : V → H) (root x : H) :
    prefixCount index k (extend p root) x =
      KroneckerPrecursorDeletion.beforeCount index p k x + if root = x then 1 else 0 := by
  classical
  simp [prefixCount, Fintype.sum_option, prefixTest, extend,
    KroneckerPrecursorDeletion.beforeCount, KroneckerPrecursorDeletion.beforeSet,
    Finset.card_filter, add_comm, -Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : index v < k ∧ p v = x <;> simp [h]

theorem prefixCount_swap [Fintype V] (index : V → ℕ) (k : ℕ)
    (f : Option V → H) (x : H) (t : V) (ht : index t < k) :
    prefixCount index k (fun v => f (Equiv.swap none (some t) v)) x =
      prefixCount index k f x := by
  classical
  have hm (v : Option V) : prefixTest index k (Equiv.swap none (some t) v) ↔
      prefixTest index k v := by
    by_cases hn : v = none
    · subst v; simp [prefixTest, ht]
    by_cases he : v = some t
    · subst v; simp [prefixTest, ht]
    rw [Equiv.swap_apply_of_ne_of_ne hn he]
  unfold prefixCount
  calc
    _ = ∑ v : Option V, if prefixTest index k (Equiv.swap none (some t) v) ∧
        f (Equiv.swap none (some t) v) = x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hm]
    _ = _ := Equiv.sum_comp (Equiv.swap none (some t))
      (fun v : Option V => if prefixTest index k v ∧ f v = x then (1 : ℕ) else 0)

def nextOwner (index : V → ℕ) (p : V → H) (root : H) (k : ℕ) : List V → H
  | [] => root
  | t :: ts => if index t < k then nextOwner index p root k ts else p t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem prefix_count_formula [Fintype V] [DecidableEq H] (index : V → ℕ) (k : ℕ)
    (p : V → H) (root x : H) (ts : List V)
    (ho : ts.Pairwise (fun v w => index v < index w)) :
    prefixCount index k (inserted p root ts) x =
      KroneckerPrecursorDeletion.beforeCount index p k x +
        if nextOwner index p root k ts = x then 1 else 0 := by
  classical
  induction ts with
  | nil => exact prefixCount_extend index k p root x
  | cons t ts ih =>
    obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp ho
    have ht : t ∉ ts := by intro hm; exact (lt_irrefl _ (hfirst t hm))
    by_cases hk : index t < k
    · change prefixCount index k
        (fun v => inserted p root ts (Equiv.swap none (some t) v)) x = _
      rw [prefixCount_swap index k _ x t hk, ih htail]
      simp only [nextOwner, ite_eq_left hk]
    · have hfix (v : V) (hv : index v < k) : v ∉ t :: ts := by
        intro hm
        rcases List.mem_cons.mp hm with he | hm
        · subst v; exact hk hv
        · have hh := hfirst v hm
          omega
      have heq : prefixCount index k (inserted p root (t :: ts)) x =
          prefixCount index k (extend p (p t)) x := by
        unfold prefixCount
        apply Finset.sum_congr rfl
        intro v hv
        cases v with
        | none => simp [inserted_new p root t ts ht, extend] <;> rfl
        | some v =>
          by_cases hv : index v < k
          · simp [prefixTest, hv, inserted_unchanged p root (t :: ts) v (hfix v hv), extend]
          · simp [prefixTest, hv]
      rw [heq, prefixCount_extend]
      simp only [nextOwner, ite_eq_right hk]

theorem debt_transfer [Fintype V] [DecidableEq H] (index : V → ℕ) (k : ℕ)
    (p : V → H) (g : H → ℕ) (root x : H) (ts : List V)
    (ho : ts.Pairwise (fun v w => index v < index w)) :
    ((g x + if x = root then 1 else 0 : ℕ) : ℤ) -
      prefixCount index k (inserted p root ts) x =
    ((g x : ℤ) - KroneckerPrecursorDeletion.beforeCount index p k x) +
      (if x = root then 1 else 0) -
      (if x = nextOwner index p root k ts then 1 else 0) := by
  rw [prefix_count_formula index k p root x ts ho]
  push_cast
  by_cases hr : x = root <;>
    by_cases hn : x = nextOwner index p root k ts <;>
    simp [hr, hn, Ne.symm, eq_comm] <;> ring

/-- The last-positive-debt rule at a copied edge before the current node ends.
The hypotheses are the old rule and the two-unit bound at an unchanged owner. -/
theorem last_positive_retained [DecidableEq H] (index : H → ℕ) (D : H → ℤ)
    (root current owner : H) (hr : index root ≤ index owner)
    (hp : 0 < D owner) (hl : ∀ x, index owner < index x → D x ≤ 0)
    (hs : owner ≠ current ∨ current = root ∨ 1 < D owner) :
    0 < D owner + (if owner = root then 1 else 0) - (if owner = current then 1 else 0) ∧
    ∀ x, index owner < index x →
      D x + (if x = root then 1 else 0) - (if x = current then 1 else 0) ≤ 0 := by
  constructor
  · rcases hs with hn | he | hb
    · simp only [ite_eq_right hn]
      split_ifs <;> omega
    · subst current
      omega
    · split_ifs <;> omega
  · intro x hx
    have hn : x ≠ root := by intro he; subst x; omega
    have hb := hl x hx
    simp only [ite_eq_right hn]
    split_ifs <;> omega

/-- The last-positive-debt rule at an ending edge transferred to its parent. -/
theorem last_positive_parent [DecidableEq H] (index : H → ℕ) (D : H → ℤ)
    (root current parent : H) (hr : index root ≤ index parent)
    (hc : index parent < index current) (hd : D current = 1)
    (hp : 0 < D parent)
    (hl : ∀ x, index parent < index x → x ≠ current → D x ≤ 0) :
    0 < D parent + (if parent = root then 1 else 0) - (if parent = current then 1 else 0) ∧
    ∀ x, index parent < index x →
      D x + (if x = root then 1 else 0) - (if x = current then 1 else 0) ≤ 0 := by
  have hpne : parent ≠ current := by intro h; subst parent; omega
  constructor
  · simp only [ite_eq_right hpne]
    split_ifs <;> omega
  · intro x hx
    have hnr : x ≠ root := by intro he; subst x; omega
    simp only [ite_eq_right hnr]
    by_cases he : x = current
    · subst x; simp [hd]
    · have h := hl x hx he
      simp only [ite_eq_right he]
      omega

/-- The decreasing enumeration is fixed by the ordered finite set itself. -/
def descending {n : ℕ} (s : Finset (Fin n)) : Fin s.card → Fin n :=
  fun j => s.orderEmbOfFin rfl j.rev

theorem descending_mem {n : ℕ} (s : Finset (Fin n)) (j : Fin s.card) :
    descending s j ∈ s := Finset.orderEmbOfFin_mem s rfl j.rev

theorem descending_antitone {n : ℕ} (s : Finset (Fin n)) : StrictAnti (descending s) := by
  intro i j hij
  apply (s.orderEmbOfFin rfl).strictMono
  exact Fin.rev_lt_rev.mpr hij

theorem descending_covers {n : ℕ} (s : Finset (Fin n)) (x : Fin n) (hx : x ∈ s) :
    ∃ j : Fin s.card, descending s j = x := by
  let i := (s.orderIsoOfFin rfl).symm ⟨x, hx⟩
  refine ⟨i.rev, ?_⟩
  simp only [descending, Fin.rev_rev]
  exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩)

open KroneckerPredecessor

theorem active_node_end_order {n q : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x y v w : Fin n} (hp : ValidThrough U p n)
    (hx : IsNode U p x v) (hy : IsNode U p y w)
    (hxy : x.val < y.val) (hyq : y.val < q) (hqv : q ≤ v.val) :
    w.val < v.val := by
  obtain ⟨z, hz, hzv⟩ := hx.interior_node hp hy.start_horizontal hxy
    (by omega) (hy.grade_pos hp)
  simpa only [hz.end_unique hy] using hzv

theorem active_iff_ending {n q : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v : Fin n} (hp : ValidThrough U p n) (hx : IsNode U p x v)
    (_hq : q ≤ n) : load U p q x < (U x).grade ↔ q ≤ v.val := by
  constructor
  · intro h
    by_contra hn
    have hs : load U p q x = load U p n x := by
      classical
      unfold load
      apply Finset.sum_subset
      · intro i hi
        simp only [mem_prefix] at hi ⊢
        omega
      · intro i hi hin
        have hqi : q ≤ i.val := by simpa only [mem_prefix, not_lt] using hin
        split_ifs with h
        · have hv := hx.last_assigned i h.1 h.2
          omega
        · rfl
    rw [hs, hx.saturated] at h
    exact (lt_irrefl _ h)
  · exact hx.load_lt_before_end hp

end KroneckerInsertionPrecursorHelpers
