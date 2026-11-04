import KroneckerStack

/-!
# H-precursors of ordered edge occurrences

This module gives the literal predecessor map in the manuscript. The internal
word of length `n` has edge occurrences indexed by `Fin n`; equal values at
distinct indices are distinct edges. Index `i.val` represents the manuscript's
edge `U_{i.val+1}`. The vertical grades play no role in the map.

`ValidThrough` is an internal partial-prefix formulation.  The public
`IsHorizontalPredecessor` predicate below is on maps from vertical occurrences
to horizontal occurrences and states the prior, remaining-grade, and
latest-eligible conditions.  No stack-execution theorem is assumed.
-/
set_option autoImplicit false
namespace KroneckerPredecessor
noncomputable section

open KroneckerStack

abbrev Word (n : ℕ) := Fin n → Edge

def IsHorizontal {n : ℕ} (U : Word n) (i : Fin n) : Prop :=
  match U i with
  | .H _ => True
  | .V _ => False

instance {n : ℕ} (U : Word n) (i : Fin n) : Decidable (IsHorizontal U i) := by
  unfold IsHorizontal
  cases U i <;> infer_instance

abbrev Horizontal {n : ℕ} (U : Word n) := {i : Fin n // IsHorizontal U i}
abbrev Vertical {n : ℕ} (U : Word n) := {i : Fin n // ¬ IsHorizontal U i}

/-- The first `k` edge occurrences. -/
def prefixEdges {n : ℕ} (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < k

@[simp] theorem mem_prefix {n k : ℕ} {i : Fin n} :
    i ∈ prefixEdges k ↔ i.val < k := by simp [prefixEdges]

@[simp] theorem prefix_zero (n : ℕ) : @prefixEdges n 0 = ∅ := by
  ext i
  simp

theorem prefix_succ {n k : ℕ} (hk : k < n) :
    @prefixEdges n (k + 1) = insert ⟨k, hk⟩ (prefixEdges k) := by
  ext i
  simp only [mem_prefix, Finset.mem_insert]
  constructor
  · intro hi
    by_cases h : i.val = k
    · left; exact Fin.ext h
    · right; omega
  · rintro (rfl | h)
    · simp
    · omega

def load {n : ℕ} (U : Word n) (p : Fin n → Fin n) (k : ℕ) (x : Fin n) : ℕ := by
  classical
  exact ∑ v ∈ prefixEdges k, if ¬ IsHorizontal U v ∧ p v = x then 1 else 0

def verticalCount {n : ℕ} (U : Word n) (k : ℕ) : ℕ := by
  classical
  exact ∑ v ∈ prefixEdges k, if ¬ IsHorizontal U v then 1 else 0

/-- The prefix vertical count counts occurrences rather than character values. -/
theorem verticalCount_eq_card {n : ℕ} (U : Word n) (k : ℕ) :
    verticalCount U k =
      ((prefixEdges k).filter fun v => ¬ IsHorizontal U v).card := by
  classical
  exact (Finset.card_filter (fun v => ¬ IsHorizontal U v) (prefixEdges k)).symm

def capacity {n : ℕ} (U : Word n) (k : ℕ) (x : Fin n) : ℕ := by
  classical
  exact if x.val < k ∧ IsHorizontal U x then (U x).grade else 0

def horizontalGrade {n : ℕ} (U : Word n) (k : ℕ) : ℕ :=
  ∑ x, capacity U k x

/-- Conditions (a), (b), and (c), on all vertical occurrences before `k`.
The auxiliary total map has no prescribed values at horizontal occurrences. -/
def ValidThrough {n : ℕ} (U : Word n) (p : Fin n → Fin n) (k : ℕ) : Prop :=
  ∀ v : Fin n, v.val < k → ¬ IsHorizontal U v →
    IsHorizontal U (p v) ∧ (p v).val < v.val ∧
    load U p v.val (p v) < (U (p v)).grade ∧
    ∀ x : Fin n, IsHorizontal U x → x.val < v.val →
      load U p v.val x < (U x).grade → x.val ≤ (p v).val

@[simp] theorem load_zero {n : ℕ} (U : Word n) (p : Fin n → Fin n) (x : Fin n) :
    load U p 0 x = 0 := by simp [load]

@[simp] theorem verticalCount_zero {n : ℕ} (U : Word n) :
    verticalCount U 0 = 0 := by simp [verticalCount]

@[simp] theorem capacity_zero {n : ℕ} (U : Word n) (x : Fin n) :
    capacity U 0 x = 0 := by simp [capacity]

theorem load_succ {n k : ℕ} (U : Word n) (p : Fin n → Fin n)
    (hk : k < n) (x : Fin n) :
    load U p (k + 1) x = load U p k x +
      if ¬ IsHorizontal U ⟨k, hk⟩ ∧ p ⟨k, hk⟩ = x then 1 else 0 := by
  classical
  unfold load
  rw [prefix_succ hk, Finset.sum_insert (by simp)]
  exact Nat.add_comm _ _

theorem verticalCount_succ {n k : ℕ} (U : Word n) (hk : k < n) :
    verticalCount U (k + 1) = verticalCount U k +
      if ¬ IsHorizontal U ⟨k, hk⟩ then 1 else 0 := by
  classical
  simp [verticalCount, prefix_succ hk, add_comm]

theorem horizontalGrade_eq_sum {n : ℕ} (U : Word n) (k : ℕ) :
    horizontalGrade U k =
      ∑ x ∈ prefixEdges k, if IsHorizontal U x then (U x).grade else 0 := by
  classical
  unfold horizontalGrade capacity prefixEdges
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x.val < k <;> by_cases hh : IsHorizontal U x <;> simp [hx, hh]

theorem horizontalGrade_succ {n k : ℕ} (U : Word n) (hk : k < n) :
    horizontalGrade U (k + 1) = horizontalGrade U k +
      if IsHorizontal U ⟨k, hk⟩ then (U ⟨k, hk⟩).grade else 0 := by
  classical
  simp [horizontalGrade_eq_sum, prefix_succ hk, add_comm]

theorem sum_load {n : ℕ} (U : Word n) (p : Fin n → Fin n) (k : ℕ) :
    (∑ x, load U p k x) = verticalCount U k := by
  classical
  unfold load verticalCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : IsHorizontal U v <;> simp [hv, eq_comm]

theorem load_congr {n k : ℕ} (U : Word n) (p q : Fin n → Fin n)
    (hpq : ∀ v, v.val < k → ¬ IsHorizontal U v → p v = q v) (x : Fin n) :
    load U p k x = load U q k x := by
  classical
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : IsHorizontal U v
  · simp [h]
  · simp [h, hpq v (mem_prefix.mp hv) h]

theorem valid_mono {n k l : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p k) (hlk : l ≤ k) : ValidThrough U p l := by
  intro v hv hh
  exact hp v (by omega) hh

theorem valid_congr {n k : ℕ} {U : Word n} {p q : Fin n → Fin n}
    (hp : ValidThrough U p k)
    (hpq : ∀ v, v.val < k → ¬ IsHorizontal U v → p v = q v) :
    ValidThrough U q k := by
  intro v hv hh
  have he := hpq v hv hh
  have hl : ∀ x, load U p v.val x = load U q v.val x := fun x =>
    load_congr U p q (fun w hw hwv => hpq w (by omega) hwv) x
  obtain ⟨h1, h2, h3, h4⟩ := hp v hv hh
  refine ⟨by simpa [← he] using h1, by simpa [← he] using h2,
    by simpa [← he, ← hl] using h3, ?_⟩
  intro x hx hxv hxg
  rw [← he]
  apply h4 x hx hxv
  simpa [hl] using hxg

theorem capacity_mono {n k l : ℕ} (U : Word n) (hkl : k ≤ l) (x : Fin n) :
    capacity U k x ≤ capacity U l x := by
  classical
  unfold capacity
  split_ifs with h1 h2
  · exact le_rfl
  · exact False.elim (h2 ⟨by omega, h1.2⟩)
  · exact Nat.zero_le _
  · exact le_rfl

theorem load_le_capacity {n k : ℕ} (U : Word n) (p : Fin n → Fin n)
    (hk : k ≤ n) (hp : ValidThrough U p k) (x : Fin n) :
    load U p k x ≤ capacity U k x := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k < n := by omega
    have hprev := ih (by omega) (valid_mono hp (by omega))
    rw [load_succ U p hkn x]
    by_cases hv : IsHorizontal U ⟨k, hkn⟩
    · simp only [hv, not_true_eq_false, false_and, ↓reduceIte, add_zero]
      exact hprev.trans (capacity_mono U (by omega) x)
    · by_cases hx : p ⟨k, hkn⟩ = x
      · obtain ⟨hh, hlt, hrem, _⟩ := hp ⟨k, hkn⟩ (by simp) hv
        rw [hx] at hh hlt hrem
        change x.val < k at hlt
        change load U p k x < (U x).grade at hrem
        simp only [hv, not_false_eq_true, hx, and_self, ↓reduceIte]
        have hc : capacity U (k + 1) x = (U x).grade := by
          simp [capacity, hh, show x.val < k + 1 by omega]
        rw [hc]
        omega
      · simp only [hx, and_false, ↓reduceIte, add_zero]
        exact hprev.trans (capacity_mono U (by omega) x)

theorem valid_implies_prefix_inequalities {n : ℕ} (U : Word n)
    (p : Fin n → Fin n) (hp : ValidThrough U p n) :
    ∀ k ≤ n, verticalCount U k ≤ horizontalGrade U k := by
  intro k hk
  rw [← sum_load U p k]
  exact Finset.sum_le_sum fun x _ =>
    load_le_capacity U p hk (valid_mono hp hk) x


/-- Updating an assignment at boundary `k` does not change any earlier load. -/
theorem load_update {n k : ℕ} (U : Word n) (p : Fin n → Fin n)
    (hk : k < n) (a x : Fin n) {i : ℕ} (hi : i ≤ k) :
    load U (Function.update p ⟨k, hk⟩ a) i x = load U p i x := by
  apply load_congr
  intro v hv _
  have hne : v ≠ ⟨k, hk⟩ := by
    intro he
    have he' := congrArg Fin.val he
    simp only at he'
    omega
  simp [Function.update_of_ne hne]

/-- The next vertical occurrence has an eligible preceding horizontal occurrence
whenever the prefix inequality holds immediately after that occurrence. -/
theorem eligible_exists {n k : ℕ} (U : Word n) (p : Fin n → Fin n)
    (hk : k < n) (hv : ¬ IsHorizontal U ⟨k, hk⟩)
    (hineq : verticalCount U (k + 1) ≤ horizontalGrade U (k + 1)) :
    ∃ x : Fin n, x.val < k ∧ IsHorizontal U x ∧ load U p k x < (U x).grade := by
  classical
  have hs : (∑ x, load U p k x) < ∑ x, capacity U k x := by
    rw [sum_load]
    change verticalCount U k < horizontalGrade U k
    rw [verticalCount_succ U hk, horizontalGrade_succ U hk] at hineq
    simp only [hv, not_false_eq_true, ↓reduceIte, add_zero] at hineq
    omega
  have hex : ∃ x : Fin n, load U p k x < capacity U k x := by
    by_contra! h
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ => h x)
    omega
  obtain ⟨x, hx⟩ := hex
  by_cases hc : x.val < k ∧ IsHorizontal U x
  · exact ⟨x, hc.1, hc.2, by simpa [capacity, hc] using hx⟩
  · simp [capacity, hc] at hx

/-- Extension at one character boundary, choosing the latest eligible occurrence. -/
theorem valid_extend {n k : ℕ} (U : Word n) (p : Fin n → Fin n)
    (hk : k < n) (hp : ValidThrough U p k)
    (hineq : verticalCount U (k + 1) ≤ horizontalGrade U (k + 1)) :
    ∃ q : Fin n → Fin n, ValidThrough U q (k + 1) := by
  classical
  by_cases hv : IsHorizontal U ⟨k, hk⟩
  · refine ⟨p, ?_⟩
    intro v hkv hV
    have hne : v.val ≠ k := by
      intro he
      have he' : v = ⟨k, hk⟩ := Fin.ext he
      subst v
      exact hV hv
    exact hp v (by omega) hV
  · obtain ⟨x, hxlt, hxH, hxg⟩ := eligible_exists U p hk hv hineq
    let A : Finset (Fin n) := Finset.univ.filter fun x =>
      x.val < k ∧ IsHorizontal U x ∧ load U p k x < (U x).grade
    have hA : A.Nonempty := ⟨x, by simp [A, hxlt, hxH, hxg]⟩
    let a : Fin n := A.max' hA
    have ha : a ∈ A := Finset.max'_mem A hA
    have ham : a.val < k ∧ IsHorizontal U a ∧ load U p k a < (U a).grade := by
      simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using ha
    let q := Function.update p ⟨k, hk⟩ a
    have hprior : ValidThrough U q k := by
      apply valid_congr hp
      intro v hkv _
      have hne : v ≠ ⟨k, hk⟩ := by
        intro he
        have he' := congrArg Fin.val he
        simp only at he'
        omega
      simp [q, Function.update_of_ne hne]
    refine ⟨q, ?_⟩
    intro v hkv hV
    by_cases hlt : v.val < k
    · exact hprior v hlt hV
    · have he : v = ⟨k, hk⟩ := Fin.ext (by change v.val = k; omega)
      subst v
      have hqa : q ⟨k, hk⟩ = a := by simp [q]
      refine ⟨by simpa [hqa] using ham.2.1,
        by simpa [hqa] using ham.1, ?_, ?_⟩
      · change load U q k (q ⟨k, hk⟩) < (U (q ⟨k, hk⟩)).grade
        rw [hqa, show load U q k a = load U p k a from load_update U p hk a a le_rfl]
        exact ham.2.2
      · intro y hyH hylt hyg
        rw [hqa]
        have hyload : load U p k y < (U y).grade := by
          change load U q k y < (U y).grade at hyg
          rwa [show load U q k y = load U p k y from load_update U p hk a y le_rfl] at hyg
        have hymem : y ∈ A := by simp [A, hyH, hylt, hyload]
        exact Finset.le_max' A y hymem

theorem prefix_inequalities_imply_valid {n : ℕ} (U : Word n)
    (hineq : ∀ k ≤ n, verticalCount U k ≤ horizontalGrade U k) :
    ∃ p : Fin n → Fin n, ValidThrough U p n := by
  have hind : ∀ k ≤ n, ∃ p : Fin n → Fin n, ValidThrough U p k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨id, ?_⟩
      intro v hv _
      omega
    | succ k ih =>
      intro hk
      obtain ⟨p, hp⟩ := ih (by omega)
      exact valid_extend U p (by omega) hp (hineq (k + 1) hk)
  exact hind n le_rfl

/-- Uniqueness uses only earlier assignments and the latest-eligible condition. -/
theorem valid_unique {n k : ℕ} (U : Word n) (p q : Fin n → Fin n)
    (hp : ValidThrough U p k) (hq : ValidThrough U q k) :
    ∀ v, v.val < k → ¬ IsHorizontal U v → p v = q v := by
  have hind : ∀ i, ∀ v : Fin n, v.val = i → v.val < k →
      ¬ IsHorizontal U v → p v = q v := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro v hvi hv hV
      have hearlier : ∀ w : Fin n, w.val < v.val → ¬ IsHorizontal U w → p w = q w := by
        intro w hw hW
        exact ih w.val (by omega) w rfl (by omega) hW
      have hloads := load_congr U p q hearlier
      obtain ⟨hpH, hpv, hpg, hplast⟩ := hp v hv hV
      obtain ⟨hqH, hqv, hqg, hqlast⟩ := hq v hv hV
      have hqp : (q v).val ≤ (p v).val :=
        hplast (q v) hqH hqv (by simpa [hloads] using hqg)
      have hpq : (p v).val ≤ (q v).val :=
        hqlast (p v) hpH hpv (by simpa [← hloads] using hpg)
      exact Fin.ext (by omega)
  intro v hv hV
  exact hind v.val v rfl hv hV


/-- Canonical extension of a map on vertical occurrences.  The identity values
on horizontal occurrences are auxiliary and never contribute to `load`. -/
def extend {n : ℕ} (U : Word n) (P : Vertical U → Horizontal U) (i : Fin n) : Fin n :=
  if h : IsHorizontal U i then i else (P ⟨i, h⟩).val

@[simp] theorem extend_vertical {n : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) (v : Vertical U) :
    extend U P v.val = (P v).val := by
  simp [extend, v.property]

@[simp] theorem extend_horizontal {n : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) (x : Horizontal U) :
    extend U P x.val = x.val := by
  simp [extend, x.property]

/-- Number of vertical occurrences assigned to `x` before character boundary `i`. -/
def assignedBefore {n : ℕ} (U : Word n) (P : Vertical U → Horizontal U)
    (i : ℕ) (x : Horizontal U) : ℕ := load U (extend U P) i x.val

/-- This is the manuscript's `Debt_{U,g}(x,i)`.  The grading is contained in `U`,
and uniqueness makes the predecessor argument canonical when it exists. -/
def Debt {n : ℕ} (U : Word n) (P : Vertical U → Horizontal U)
    (x : Horizontal U) (i : ℕ) : ℕ := (U x.val).grade - assignedBefore U P i x

/-- Exact finite-set interpretation of the assignment count. -/
theorem assignedBefore_eq_card {n : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) (i : ℕ) (x : Horizontal U) :
    assignedBefore U P i x =
      (Finset.univ.filter fun v : Vertical U => v.val.val < i ∧ P v = x).card := by
  classical
  let A := (prefixEdges i).filter fun v : Fin n =>
    ¬ IsHorizontal U v ∧ extend U P v = x.val
  let B := Finset.univ.filter fun v : Vertical U => v.val.val < i ∧ P v = x
  have hA : ∀ v ∈ A, ¬ IsHorizontal U v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2.1
  change assignedBefore U P i x = B.card
  have heq : assignedBefore U P i x = A.card := by
    simp [assignedBefore, load, A]
  rw [heq]
  apply Finset.card_bij (fun v hv => (⟨v, hA v hv⟩ : Vertical U))
  · intro v hv
    obtain ⟨hvpre, hvH, hvP⟩ := Finset.mem_filter.mp hv
    have hext : extend U P v = (P ⟨v, hvH⟩).val := by simp [extend, hvH]
    have hPx : P ⟨v, hvH⟩ = x := Subtype.ext (hext.symm.trans hvP)
    simp [B, mem_prefix.mp hvpre, hPx]
  · intro v hv w hw he
    exact congrArg Subtype.val he
  · intro v hv
    have hvm : v.val.val < i ∧ P v = x := by simpa [B] using hv
    have hvA : v.val ∈ A := by
      simp [A, hvm.1, v.property, hvm.2]
    exact ⟨v.val, hvA, rfl⟩

/-- A h-precursor map of the manuscript. -/
def IsHorizontalPredecessor {n : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) : Prop := ValidThrough U (extend U P) n

/-- The literal occurrence conditions: a preceding horizontal edge, positive
remaining grade there, and maximal starting boundary among eligible edges. -/
theorem isHorizontalPredecessor_iff {n : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) : IsHorizontalPredecessor U P ↔
    ∀ v : Vertical U,
      (P v).val.val < v.val.val ∧
      assignedBefore U P v.val.val (P v) < (U (P v).val).grade ∧
      ∀ x : Horizontal U, x.val.val < v.val.val →
        assignedBefore U P v.val.val x < (U x.val).grade →
        x.val.val ≤ (P v).val.val := by
  constructor
  · intro hp v
    obtain ⟨_, hprior, hrem, hlast⟩ := hp v.val v.val.isLt v.property
    refine ⟨by simpa using hprior, by simpa [assignedBefore] using hrem, ?_⟩
    intro x hx hxg
    simpa using hlast x.val x.property hx hxg
  · intro hp v _ hv
    let w : Vertical U := ⟨v, hv⟩
    obtain ⟨hprior, hrem, hlast⟩ := hp w
    have he : extend U P v = (P w).val := extend_vertical U P w
    refine ⟨by rw [he]; exact (P w).property,
      by simpa [he] using hprior,
      by simpa [assignedBefore, he] using hrem, ?_⟩
    intro x hx hxv hxg
    have hb := hlast ⟨x, hx⟩ hxv hxg
    simpa [he] using hb

/-- Lemma: there is at most one h-precursor map. -/
theorem horizontalPredecessor_unique {n : ℕ} (U : Word n)
    (P Q : Vertical U → Horizontal U)
    (hP : IsHorizontalPredecessor U P) (hQ : IsHorizontalPredecessor U Q) : P = Q := by
  funext v
  apply Subtype.ext
  have he := valid_unique U (extend U P) (extend U Q) hP hQ v.val v.val.isLt v.property
  simpa using he

/-- Lemma: a h-precursor map exists exactly when every prefix has
at least as much horizontal grade as it has vertical edge occurrences. -/
theorem exists_horizontalPredecessor_iff {n : ℕ} (U : Word n) :
    (∃ P : Vertical U → Horizontal U, IsHorizontalPredecessor U P) ↔
      ∀ k ≤ n, verticalCount U k ≤ horizontalGrade U k := by
  constructor
  · rintro ⟨P, hP⟩
    exact valid_implies_prefix_inequalities U (extend U P) hP
  · intro hineq
    obtain ⟨p, hp⟩ := prefix_inequalities_imply_valid U hineq
    let P : Vertical U → Horizontal U := fun v =>
      ⟨p v.val, (hp v.val v.val.isLt v.property).1⟩
    refine ⟨P, valid_congr hp ?_⟩
    intro v _ hv
    simp [extend, hv, P]

theorem existsUnique_horizontalPredecessor_iff {n : ℕ} (U : Word n) :
    (∃! P : Vertical U → Horizontal U, IsHorizontalPredecessor U P) ↔
      ∀ k ≤ n, verticalCount U k ≤ horizontalGrade U k := by
  constructor
  · rintro ⟨P, hP, _⟩
    exact (exists_horizontalPredecessor_iff U).mp ⟨P, hP⟩
  · intro hineq
    obtain ⟨P, hP⟩ := (exists_horizontalPredecessor_iff U).mpr hineq
    exact ⟨P, hP, fun Q hQ => horizontalPredecessor_unique U Q P hQ hP⟩

theorem assignedBefore_le_grade {n i : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) (hP : IsHorizontalPredecessor U P)
    (hi : i ≤ n) (x : Horizontal U) : assignedBefore U P i x ≤ (U x.val).grade := by
  have hb := load_le_capacity U (extend U P) hi (valid_mono hP hi) x.val
  change load U (extend U P) i x.val ≤ (U x.val).grade
  apply hb.trans
  unfold capacity
  split_ifs <;> omega

/-- Natural subtraction in `Debt` is exact for a h-precursor map. -/
theorem Debt_add_assignedBefore {n i : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) (hP : IsHorizontalPredecessor U P)
    (hi : i ≤ n) (x : Horizontal U) :
    Debt U P x i + assignedBefore U P i x = (U x.val).grade := by
  exact Nat.sub_add_cancel (assignedBefore_le_grade U P hP hi x)

@[simp] theorem Debt_zero {n : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) (x : Horizontal U) :
    Debt U P x 0 = (U x.val).grade := by simp [Debt, assignedBefore]

theorem Debt_positive_before_assignment {n : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) (hP : IsHorizontalPredecessor U P)
    (v : Vertical U) : 0 < Debt U P (P v) v.val.val := by
  have hrem := ((isHorizontalPredecessor_iff U P).mp hP v).2.1
  exact Nat.sub_pos_iff_lt.mpr hrem

theorem Debt_zero_iff {n i : ℕ} (U : Word n)
    (P : Vertical U → Horizontal U) (hP : IsHorizontalPredecessor U P)
    (hi : i ≤ n) (x : Horizontal U) :
    Debt U P x i = 0 ↔ assignedBefore U P i x = (U x.val).grade := by
  have he := Debt_add_assignedBefore U P hP hi x
  omega

#print axioms KroneckerPredecessor.exists_horizontalPredecessor_iff
#print axioms KroneckerPredecessor.horizontalPredecessor_unique
#print axioms KroneckerPredecessor.Debt_add_assignedBefore

end
end KroneckerPredecessor
