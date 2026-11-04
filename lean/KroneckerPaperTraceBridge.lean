import KroneckerPaperPredecessor
import KroneckerShadow

/-!
# Indexed predecessors and the unguarded debt trace

The declarations here connect assignment counts on distinct indexed occurrences
to the existing unguarded `RawTrace`.  No balance inequalities are imposed.
-/
set_option autoImplicit false
namespace KroneckerPaperTraceBridge
noncomputable section

open KroneckerStack KroneckerShadow KroneckerPredecessor

def sample (E : ℕ → Edge) (n : ℕ) : Word n := fun i => E i.val

def Descending (xs : List Entry) : Prop :=
  xs.Pairwise fun x y => y.origin < x.origin

def Before (k : ℕ) (xs : List Entry) : Prop :=
  ∀ x ∈ xs, x.origin < k

/-- Remaining debt at a specified occurrence. The sum is useful before
distinctness of the origins has been established. -/
def remaining : List Entry → ℕ → ℕ
  | [], _ => 0
  | x :: xs, u => (if x.origin = u then x.debt else 0) + remaining xs u

theorem rawStep_order {E : ℕ → Edge} {k : ℕ} {xs ys : List Entry}
    (hs : RawStep E k xs ys) (hb : Before k xs) (ho : Descending xs) :
    Before (k+1) ys ∧ Descending ys := by
  cases hs with
  | hz he => exact ⟨fun x hx => (hb x hx).trans (by omega), ho⟩
  | hp he =>
      constructor
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp
        · exact (hb x hx).trans (by omega)
      · exact List.pairwise_cons.mpr ⟨fun x hx => hb x hx, ho⟩
  | one he hd =>
      exact ⟨fun x hx => (hb x (by simp [hx])).trans (by omega),
        (List.pairwise_cons.mp ho).2⟩
  | @many x xs g he hd =>
      constructor
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact (hb x (by simp)).trans (by omega)
        · exact (hb y (by simp [hy])).trans (by omega)
      · exact List.pairwise_cons.mpr
          ⟨(List.pairwise_cons.mp ho).1, (List.pairwise_cons.mp ho).2⟩

theorem trace_order {E : ℕ → Edge} {n k : ℕ} {f : ℕ → List Entry}
    (ht : RawTrace E n f) (hk : k ≤ n) :
    Before k (f k) ∧ Descending (f k) := by
  induction k with
  | zero => simp [ht.1, Before, Descending]
  | succ k ih =>
      obtain ⟨hb, ho⟩ := ih (by omega)
      exact rawStep_order (ht.2 k (by omega)) hb ho

theorem remaining_eq_zero {xs : List Entry} {u : ℕ}
    (h : ∀ x ∈ xs, x.origin ≠ u) : remaining xs u = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [remaining, ite_eq_right (h x (by simp)), zero_add]
      exact ih (fun y hy => h y (by simp [hy]))

theorem remaining_member {xs : List Entry} (ho : Descending xs)
    {x : Entry} (hx : x ∈ xs) : remaining xs x.origin = x.debt := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp ho
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hz : remaining ys x.origin = 0 :=
          remaining_eq_zero (fun z hz => Nat.ne_of_lt (hhead z hz))
        simp [remaining, hz]
      · have hne : y.origin ≠ x.origin := Nat.ne_of_gt (hhead x hx)
        simp only [remaining, ite_eq_right hne, zero_add]
        exact ih htail hx

theorem remaining_pos_origin {xs : List Entry} {u : ℕ}
    (h : 0 < remaining xs u) : ∃ x ∈ xs, x.origin = u := by
  induction xs with
  | nil => simp [remaining] at h
  | cons x xs ih =>
      by_cases he : x.origin = u
      · exact ⟨x, by simp, he⟩
      · have ht : 0 < remaining xs u := by simpa [remaining, he] using h
        obtain ⟨y, hy, heq⟩ := ih ht
        exact ⟨y, by simp [hy], heq⟩

/-- At every vertical occurrence, the proposed predecessor is precisely the
origin of the entry whose debt the trace decrements. -/
def FollowsTrace {n : ℕ} (E : ℕ → Edge) (p : Fin n → Fin n)
    (f : ℕ → List Entry) : Prop :=
  ∀ v : Fin n, ¬ IsHorizontal (sample E n) v →
    ∃ x xs, f v.val = x :: xs ∧ x.origin = (p v).val

theorem capacity_step {n k : ℕ} (U : Word n) (hk : k < n) (u : Fin n) :
    capacity U (k+1) u = capacity U k u +
      if u = ⟨k,hk⟩ ∧ IsHorizontal U ⟨k,hk⟩ then (U ⟨k,hk⟩).grade else 0 := by
  classical
  by_cases he : u = ⟨k,hk⟩
  · subst u
    simp [capacity]
  · have hne : u.val ≠ k := fun h => he (Fin.ext h)
    have hlt : u.val < k+1 ↔ u.val < k := by omega
    simp [capacity, he, hlt]

theorem follows_head {n k : ℕ} {E : ℕ → Edge} {p : Fin n → Fin n}
    {f : ℕ → List Entry} (hf : FollowsTrace E p f) (hk : k < n)
    (hv : ¬ IsHorizontal (sample E n) ⟨k,hk⟩)
    {x : Entry} {xs : List Entry} (he : f k = x::xs) :
    x.origin = (p ⟨k,hk⟩).val := by
  obtain ⟨y, ys, hy, hp⟩ := hf ⟨k,hk⟩ hv
  have hh : y = x := (List.cons.inj (hy.symm.trans he)).1
  simpa [hh] using hp

/-- The debt consumed by a vertical character is exactly the count added
to its predecessor's fiber. This identity holds at every character boundary. -/
theorem trace_counts {E : ℕ → Edge} {n k : ℕ} {f : ℕ → List Entry}
    {p : Fin n → Fin n} (ht : RawTrace E n f) (hf : FollowsTrace E p f)
    (hk : k ≤ n) (u : Fin n) :
    load (sample E n) p k u + remaining (f k) u.val =
      capacity (sample E n) k u := by
  classical
  induction k with
  | zero => simp [ht.1, remaining]
  | succ k ih =>
      have hkn : k < n := by omega
      have hi := ih (by omega)
      have hs := ht.2 k hkn
      have hl := load_succ (sample E n) p hkn u
      have hc := capacity_step (sample E n) hkn u
      generalize htarget : f (k+1) = ys at hs ⊢
      cases hsource : f k with
      | nil =>
          rw [hsource] at hs hi
          cases hs with
          | hz he =>
              have hh : IsHorizontal (sample E n) ⟨k,hkn⟩ := by
                simp [IsHorizontal, sample, he]
              simp only [hh, not_true_eq_false, false_and, ↓reduceIte, add_zero] at hl
              simp [sample, he, Edge.grade] at hc
              simpa [hl, hc, remaining] using hi
          | hp he =>
              have hh : IsHorizontal (sample E n) ⟨k,hkn⟩ := by
                simp [IsHorizontal, sample, he]
              simp only [hh, not_true_eq_false, false_and, ↓reduceIte, add_zero] at hl
              by_cases hu : u = ⟨k,hkn⟩
              · subst u
                simp [remaining, hl, hc, sample, he, Edge.grade, hh] at *
                exact hi
              · have hne : k ≠ u.val := fun h => hu (Fin.ext h.symm)
                simpa [remaining, hl, hc, hu, hne] using hi
      | cons x xs =>
          have hphead (hv : ¬ IsHorizontal (sample E n) ⟨k,hkn⟩) :
              x.origin = (p ⟨k,hkn⟩).val := follows_head hf hkn hv hsource
          rw [hsource] at hs hi
          cases hs with
          | hz he =>
              have hh : IsHorizontal (sample E n) ⟨k,hkn⟩ := by
                simp [IsHorizontal, sample, he]
              simp only [hh, not_true_eq_false, false_and, ↓reduceIte, add_zero] at hl
              simp [sample, he, Edge.grade] at hc
              simpa [hl, hc] using hi
          | hp he =>
              have hh : IsHorizontal (sample E n) ⟨k,hkn⟩ := by
                simp [IsHorizontal, sample, he]
              simp only [hh, not_true_eq_false, false_and, ↓reduceIte, add_zero] at hl
              by_cases hu : u = ⟨k,hkn⟩
              · subst u
                simp [hl, hc, hh, sample, he, Edge.grade, remaining]
                simp only [remaining] at hi
                omega
              · have hne : k ≠ u.val := fun h => hu (Fin.ext h.symm)
                simpa [remaining, hl, hc, hu, hne] using hi
          | one he hd =>
              have hv : ¬ IsHorizontal (sample E n) ⟨k,hkn⟩ := by
                simp [IsHorizontal, sample, he]
              have hp := hphead hv
              have hpeq : p ⟨k,hkn⟩ = u ↔ x.origin = u.val := by
                constructor
                · intro h; simpa [h] using hp
                · intro h; exact Fin.ext (hp.symm.trans h)
              simp only [hv, not_false_eq_true, true_and] at hl
              simp only [hv, and_false, ↓reduceIte, add_zero] at hc
              by_cases hu : x.origin = u.val
              · have hpu := hpeq.mpr hu
                simp [remaining, hu, hd] at hi
                simp only [hl, hpu, ↓reduceIte, hc]
                omega
              · have hpu : p ⟨k,hkn⟩ ≠ u := fun h => hu (hpeq.mp h)
                simpa [hl, hpu, hc, remaining, hu] using hi
          | many he hd =>
              have hv : ¬ IsHorizontal (sample E n) ⟨k,hkn⟩ := by
                simp [IsHorizontal, sample, he]
              have hp := hphead hv
              have hpeq : p ⟨k,hkn⟩ = u ↔ x.origin = u.val := by
                constructor
                · intro h; simpa [h] using hp
                · intro h; exact Fin.ext (hp.symm.trans h)
              simp only [hv, not_false_eq_true, true_and] at hl
              simp only [hv, and_false, ↓reduceIte, add_zero] at hc
              by_cases hu : x.origin = u.val
              · have hpu := hpeq.mpr hu
                simp [remaining, hu] at hi
                simp only [hl, hpu, ↓reduceIte, hc, remaining, hu]
                omega
              · have hpu : p ⟨k,hkn⟩ ≠ u := fun h => hu (hpeq.mp h)
                simpa [hl, hpu, hc, remaining, hu] using hi

theorem floors_member {E : ℕ → Edge} {xs : List Entry}
    (hf : Floors E xs) {x : Entry} (hx : x ∈ xs) :
    0 < x.debt ∧ KroneckerCompatibility.PositiveH E x.origin := by
  induction hf with
  | nil => simp at hx
  | @cons y ys hf hd hh he ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨hd, hh⟩
      · exact ih hx

theorem trace_entry_account {E : ℕ → Edge} {n k : ℕ}
    {f : ℕ → List Entry} {p : Fin n → Fin n}
    (ht : RawTrace E n f) (hf : FollowsTrace E p f) (hk : k ≤ n)
    {x : Entry} (hx : x ∈ f k) (hxn : x.origin < n) :
    load (sample E n) p k ⟨x.origin,hxn⟩ + x.debt = (E x.origin).grade := by
  obtain ⟨hb, ho⟩ := trace_order ht hk
  obtain ⟨_, hg, _, he⟩ := floors_member (trace_invariants ht hk).1 hx
  have hh : IsHorizontal (sample E n) ⟨x.origin,hxn⟩ := by
    simp [IsHorizontal, sample, he]
  have hi := trace_counts ht hf hk ⟨x.origin,hxn⟩
  rw [remaining_member ho hx] at hi
  simpa [capacity, hb x hx, hh, sample] using hi

/-- Individual operational debt equals the grade minus the literal number
of assigned vertical occurrences in the prefix. -/
theorem trace_entry_debt {E : ℕ → Edge} {n k : ℕ}
    {f : ℕ → List Entry} {p : Fin n → Fin n}
    (ht : RawTrace E n f) (hf : FollowsTrace E p f) (hk : k ≤ n)
    {x : Entry} (hx : x ∈ f k) (hxn : x.origin < n) :
    x.debt = (E x.origin).grade - load (sample E n) p k ⟨x.origin,hxn⟩ := by
  have hi := trace_entry_account ht hf hk hx hxn
  omega

/-- Top-entry assignments satisfy all three literal predecessor conditions,
including maximality among all horizontal occurrences with unused grade. -/
theorem followsTrace_valid {E : ℕ → Edge} {n : ℕ}
    {f : ℕ → List Entry} {p : Fin n → Fin n}
    (ht : RawTrace E n f) (hf : FollowsTrace E p f) :
    ValidThrough (sample E n) p n := by
  classical
  intro v hv hvV
  obtain ⟨x, xs, hs, hp⟩ := hf v hvV
  have hx : x ∈ f v.val := by simp [hs]
  have hk : v.val ≤ n := Nat.le_of_lt v.isLt
  obtain ⟨hb, ho⟩ := trace_order ht hk
  have hprior : (p v).val < v.val := by simpa [hp] using hb x hx
  obtain ⟨hd, g, hg, he⟩ := floors_member (trace_invariants ht hk).1 hx
  have hh : IsHorizontal (sample E n) (p v) := by
    simp [IsHorizontal, sample, ← hp, he]
  have hxn : x.origin < n := (hb x hx).trans_le hk
  have hidx : (⟨x.origin,hxn⟩ : Fin n) = p v := Fin.ext hp
  have haccount := trace_entry_account ht hf hk hx hxn
  have havailable : load (sample E n) p v.val (p v) <
      ((sample E n) (p v)).grade := by
    rw [hidx] at haccount
    change load (sample E n) p v.val (p v) < (E (p v).val).grade
    rw [← hp]
    omega
  refine ⟨hh, hprior, havailable, ?_⟩
  intro u huH huprior huavail
  have huaccount := trace_counts ht hf hk u
  have hucap : capacity (sample E n) v.val u = ((sample E n) u).grade := by
    simp [capacity, huH, huprior]
  rw [hucap] at huaccount
  have hrem : 0 < remaining (f v.val) u.val := by omega
  obtain ⟨y, hy, hyu⟩ := remaining_pos_origin hrem
  rw [hs] at ho hy
  rcases List.mem_cons.mp hy with rfl | hy
  · omega
  · have hlt := (List.pairwise_cons.mp ho).1 y hy
    omega

theorem rawStep_vertical_source {E : ℕ → Edge} {k : ℕ}
    {xs ys : List Entry} (hs : RawStep E k xs ys)
    (hv : KroneckerCompatibility.Vertical E k) :
    ∃ x zs, xs = x::zs := by
  obtain ⟨g, hg⟩ := hv
  cases hs with
  | hz he => rw [he] at hg; cases hg
  | hp he => rw [he] at hg; cases hg
  | one he hd => exact ⟨_, _, rfl⟩
  | many he hd => exact ⟨_, _, rfl⟩

theorem followsTrace_exists {E : ℕ → Edge} {n : ℕ} {f : ℕ → List Entry}
    (ht : RawTrace E n f) : ∃ p : Fin n → Fin n, FollowsTrace E p f := by
  classical
  have hall : ∀ v : Fin n, ∃ u : Fin n,
      ¬ IsHorizontal (sample E n) v →
        ∃ x xs, f v.val = x::xs ∧ x.origin = u.val := by
    intro v
    by_cases hh : IsHorizontal (sample E n) v
    · exact ⟨v, fun hv => False.elim (hv hh)⟩
    · have hv : KroneckerCompatibility.Vertical E v.val := by
        cases he : E v.val with
        | H g => exact False.elim (hh (by simp [IsHorizontal, sample, he]))
        | V g => exact ⟨g, he⟩
      obtain ⟨x, xs, hx⟩ := rawStep_vertical_source (ht.2 v.val v.isLt) hv
      have hb := (trace_order ht (Nat.le_of_lt v.isLt)).1
      have hxn : x.origin < n :=
        (hb x (by simp [hx])).trans v.isLt
      exact ⟨⟨x.origin,hxn⟩, fun _ => ⟨x, xs, hx, rfl⟩⟩
  choose p hp using hall
  exact ⟨p, hp⟩

/-- The literal predecessor map agrees with the origin decremented by every
vertical trace step. The conclusion has no extra assignment hypothesis. -/
theorem valid_followsTrace {E : ℕ → Edge} {n : ℕ}
    {f : ℕ → List Entry} {p : Fin n → Fin n}
    (ht : RawTrace E n f) (hp : ValidThrough (sample E n) p n) :
    FollowsTrace E p f := by
  obtain ⟨q, hq⟩ := followsTrace_exists ht
  have hqvalid := followsTrace_valid ht hq
  intro v hv
  obtain ⟨x, xs, hx, hxo⟩ := hq v hv
  have hpq := valid_unique (sample E n) p q hp hqvalid v v.isLt hv
  exact ⟨x, xs, hx, by simpa [hpq] using hxo⟩

/-- The cumulative debt used by the trace is total horizontal capacity minus
the number of vertical occurrences. It is distinct from an individual node's debt. -/
theorem prefix_total_debt (E : ℕ → Edge) {n k : ℕ} (hk : k ≤ n) :
    (horizontalGrade (sample E n) k : ℤ) - (verticalCount (sample E n) k : ℤ) =
      KroneckerCompatibility.debt E k := by
  induction k with
  | zero => simp [horizontalGrade, KroneckerCompatibility.debt, KroneckerCompatibility.walk]
  | succ k ih =>
      have hkn : k < n := by omega
      have hi := ih (by omega)
      have hg := horizontalGrade_succ (sample E n) hkn
      have hv := verticalCount_succ (sample E n) hkn
      rw [KroneckerCompatibility.debt_step]
      cases he : E k with
      | H g =>
          simp [IsHorizontal, sample, he, Edge.grade] at hg hv
          simp only [Edge.debtChange]
          rw [hg, hv]
          push_cast
          omega
      | V g =>
          simp [IsHorizontal, sample, he] at hg hv
          simp only [Edge.debtChange]
          rw [hg, hv]
          push_cast
          omega

/-- A literal predecessor map supplies the complete unguarded trace, with
exact agreement of the assigned horizontal occurrences. -/
theorem valid_has_trace {E : ℕ → Edge} {n : ℕ} {p : Fin n → Fin n}
    (hp : ValidThrough (sample E n) p n) :
    ∃ f, RawTrace E n f ∧ FollowsTrace E p f := by
  have hprefix := valid_implies_prefix_inequalities (sample E n) p hp
  have hpos : ∀ k, k < n → KroneckerCompatibility.Vertical E k →
      0 < KroneckerCompatibility.debt E k := by
    intro k hk hv
    obtain ⟨g, he⟩ := hv
    have hg := horizontalGrade_succ (sample E n) hk
    have hv := verticalCount_succ (sample E n) hk
    simp [IsHorizontal, sample, he] at hg hv
    have hi := hprefix (k+1) (by omega)
    rw [hg, hv] at hi
    have hd := prefix_total_debt E (n := n) (Nat.le_of_lt hk)
    omega
  obtain ⟨f, ht⟩ := trace_exists E n hpos
  exact ⟨f, ht, valid_followsTrace ht hp⟩

theorem valid_iff_trace {E : ℕ → Edge} {n : ℕ} {p : Fin n → Fin n} :
    ValidThrough (sample E n) p n ↔
      ∃ f, RawTrace E n f ∧ FollowsTrace E p f :=
  ⟨valid_has_trace, fun ⟨_, ht, hf⟩ => followsTrace_valid ht hf⟩

theorem predecessor_followsTrace {E : ℕ → Edge} {n : ℕ}
    {f : ℕ → List Entry}
    {P : KroneckerPredecessor.Vertical (sample E n) →
      KroneckerPredecessor.Horizontal (sample E n)}
    (ht : RawTrace E n f) (hp : IsHorizontalPredecessor (sample E n) P) :
    FollowsTrace E (KroneckerPredecessor.extend (sample E n) P) f :=
  valid_followsTrace ht hp

/-- The manuscript's named `Debt` agrees with the debt of its indexed trace entry. -/
theorem predecessor_entry_debt {E : ℕ → Edge} {n k : ℕ}
    {f : ℕ → List Entry}
    {P : KroneckerPredecessor.Vertical (sample E n) →
      KroneckerPredecessor.Horizontal (sample E n)}
    (ht : RawTrace E n f) (hp : IsHorizontalPredecessor (sample E n) P)
    (hk : k ≤ n) {x : Entry} (hx : x ∈ f k)
    (u : KroneckerPredecessor.Horizontal (sample E n)) (hu : u.val.val = x.origin) :
    x.debt = Debt (sample E n) P u k := by
  have hxn : x.origin < n := by rw [← hu]; exact u.val.isLt
  have heq : (⟨x.origin,hxn⟩ : Fin n) = u.val := Fin.ext hu.symm
  have hd := trace_entry_debt ht (predecessor_followsTrace ht hp) hk hx hxn
  simpa [Debt, assignedBefore, sample, heq, ← hu] using hd

end
end KroneckerPaperTraceBridge
