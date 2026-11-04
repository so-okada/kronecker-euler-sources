import KroneckerInsertionPrecursorAssembly
import KroneckerPaperConnected
import Mathlib.Logic.Equiv.Fin.Basic

/-! The insertion assignment on literal finite edge occurrences. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerInsertionOccurrenceAssembly
open KroneckerStack KroneckerPredecessor KroneckerPaperConnected
open KroneckerPrecursorDeletion KroneckerInsertionPrecursorAssembly
variable {n : ℕ}

theorem occurrence_count (U : Word n) (p : Vertical U → Horizontal U)
    (k : ℕ) (x : Horizontal U) :
    beforeCount (fun v : Vertical U => v.val.val) p k x = assignedBefore U p k x := by
  classical
  rw [assignedBefore_eq_card]
  apply congrArg Finset.card
  ext v
  simp only [beforeSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem occurrence_precursor (U : Word n) (p : Vertical U → Horizontal U) :
    IsHorizontalPredecessor U p ↔
      Precursor (fun x : Horizontal U => x.val.val)
        (fun v : Vertical U => v.val.val) (fun x => (U x.val).grade) p := by
  rw [isHorizontalPredecessor_iff]
  simp only [Precursor, occurrence_count]

theorem fullRoot_of_connected (U : Word n) (p : Vertical U → Horizontal U)
    (hp : IsHorizontalPredecessor U p) (hc : FiniteConnected U) :
    FullRoot U (KroneckerPredecessor.extend U p) := by
  obtain ⟨q, hq, _, x, v, hn, hx, hv⟩ := hc
  have he (w : Fin n) (hw : ¬ IsHorizontal U w) :
      q w = KroneckerPredecessor.extend U p w :=
    valid_unique U q _ hq hp w w.isLt hw
  refine ⟨x, v, ?_, hx, hv⟩
  exact ⟨hn.start_horizontal, hn.end_vertical,
    (he v hn.end_vertical).symm.trans hn.end_assigned,
    (load_congr U q _ (fun w _ hw => he w hw) x).symm.trans hn.saturated,
    fun w hw hwx => hn.last_assigned w hw ((he w hw).trans hwx)⟩

theorem connected_saturated (U : Word n) (p : Vertical U → Horizontal U)
    (hp : IsHorizontalPredecessor U p) (hc : FiniteConnected U)
    (x : Horizontal U) :
    (fiber p x).card = (U x.val).grade := by
  obtain ⟨r, v, hn, hr, hv⟩ := fullRoot_of_connected U p hp hc
  have hf : beforeSet (fun w : Vertical U => w.val.val) p n x = fiber p x := by
    ext w
    simp [beforeSet, fiber]
  rw [← hf, ← beforeCount, occurrence_count]
  by_cases he : x.val = r
  · simpa [assignedBefore, he] using hn.saturated
  · have hne : x.val.val ≠ r.val := fun h => he (Fin.ext h)
    have hs := hn.interior_saturated hp x.property (by omega) (by have := x.val.isLt; omega)
    have hm := load_mono U (KroneckerPredecessor.extend U p) (Nat.le_of_lt v.isLt) x.val
    have hb := load_le_grade U (KroneckerPredecessor.extend U p) hp le_rfl x.val
    change load U (KroneckerPredecessor.extend U p) n x.val = _
    omega

/-- Insert a zero-graded vertical edge and increase the specified root grade by one. -/
def insertedWord (U : Word n) (root : Horizontal U) (q : Fin (n+1)) : Word (n+1) :=
  fun i => match finSuccEquiv' q i with
    | none => .V 0
    | some j => if j = root.val then .H ((U j).grade+1) else U j

@[simp] theorem word_new (U : Word n) (root : Horizontal U) (q : Fin (n+1)) :
    insertedWord U root q q = .V 0 := by simp [insertedWord]

@[simp] theorem word_copy (U : Word n) (root : Horizontal U) (q : Fin (n+1)) (i : Fin n) :
    insertedWord U root q (q.succAbove i) =
      if i = root.val then .H ((U i).grade+1) else U i := by simp [insertedWord]

@[simp] theorem horizontal_copy (U : Word n) (root : Horizontal U)
    (q : Fin (n+1)) (i : Fin n) :
    IsHorizontal (insertedWord U root q) (q.succAbove i) ↔ IsHorizontal U i := by
  change (match insertedWord U root q (q.succAbove i) with
    | .H _ => True | .V _ => False) ↔ IsHorizontal U i
  rw [word_copy]
  by_cases he : i = root.val
  · subst i
    simpa only [↓reduceIte, true_iff] using root.property
  · simp only [ite_eq_right he]
    rfl

@[simp] theorem horizontal_new (U : Word n) (root : Horizontal U) (q : Fin (n+1)) :
    ¬ IsHorizontal (insertedWord U root q) q := by simp [IsHorizontal, word_new]

def copyHorizontal (U : Word n) (root : Horizontal U) (q : Fin (n+1))
    (x : Horizontal U) : Horizontal (insertedWord U root q) :=
  ⟨q.succAbove x.val, (horizontal_copy U root q x.val).mpr x.property⟩

def copyVertical (U : Word n) (root : Horizontal U) (q : Fin (n+1)) :
    Option (Vertical U) → Vertical (insertedWord U root q)
  | none => ⟨q, horizontal_new U root q⟩
  | some v => ⟨q.succAbove v.val, fun h => v.property ((horizontal_copy U root q v.val).mp h)⟩

theorem copyHorizontal_bijective (U : Word n) (root : Horizontal U) (q : Fin (n+1)) :
    Function.Bijective (copyHorizontal U root q) := by
  constructor
  · intro x y he
    exact Subtype.ext (Fin.succAbove_right_injective (congrArg Subtype.val he))
  · rintro ⟨i, hi⟩
    induction i using Fin.succAboveCases q with
    | x => exact (horizontal_new U root q hi).elim
    | p i => exact ⟨⟨i, (horizontal_copy U root q i).mp hi⟩, rfl⟩

theorem copyVertical_bijective (U : Word n) (root : Horizontal U) (q : Fin (n+1)) :
    Function.Bijective (copyVertical U root q) := by
  constructor
  · intro x y he
    have he' := congrArg (fun v => finSuccEquiv' q v.val) he
    cases x <;> cases y <;> simp [copyVertical] at he' ⊢
    exact Subtype.ext he'
  · rintro ⟨i, hi⟩
    induction i using Fin.succAboveCases q with
    | x => exact ⟨none, rfl⟩
    | p i => exact ⟨some ⟨i, fun h => hi ((horizontal_copy U root q i).mpr h)⟩, rfl⟩

def horizontalEquiv (U : Word n) (root : Horizontal U) (q : Fin (n+1)) :
    Horizontal U ≃ Horizontal (insertedWord U root q) :=
  Equiv.ofBijective (copyHorizontal U root q) (copyHorizontal_bijective U root q)

def verticalEquiv (U : Word n) (root : Horizontal U) (q : Fin (n+1)) :
    Option (Vertical U) ≃ Vertical (insertedWord U root q) :=
  Equiv.ofBijective (copyVertical U root q) (copyVertical_bijective U root q)

theorem succAbove_index (q : Fin (n+1)) (i : Fin n) :
    (q.succAbove i).val = shift q.val i.val := by
  unfold Fin.succAbove shift
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

@[simp] theorem horizontal_index (U : Word n) (root : Horizontal U)
    (q : Fin (n+1)) (x : Horizontal U) :
    (horizontalEquiv U root q x).val.val = shift q.val x.val.val :=
  succAbove_index q x.val

@[simp] theorem vertical_index (U : Word n) (root : Horizontal U)
    (q : Fin (n+1)) (v : Option (Vertical U)) :
    (verticalEquiv U root q v).val.val = verticalIndex q.val (fun w => w.val.val) v := by
  cases v with
  | none => rfl
  | some v => exact succAbove_index q v.val

@[simp] theorem horizontal_grade (U : Word n) (root : Horizontal U)
    (q : Fin (n+1)) (x : Horizontal U) :
    (insertedWord U root q (horizontalEquiv U root q x).val).grade =
      raised (fun y : Horizontal U => (U y.val).grade) root x := by
  change (insertedWord U root q (q.succAbove x.val)).grade = _
  rw [word_copy]
  by_cases he : x = root
  · subst x
    simp [raised, Edge.grade]
  · have hne : x.val ≠ root.val := fun h => he (Subtype.ext h)
    simp [hne, raised, he]

def assignment (U : Word n) (root : Horizontal U) (q : Fin (n+1))
    (p : Vertical U → Horizontal U) :
    Vertical (insertedWord U root q) → Horizontal (insertedWord U root q) :=
  fun v => horizontalEquiv U root q
    (KroneckerInsertionPrecursorHelpers.inserted p root
      (chain (fun x : Horizontal U => x.val.val) (fun v : Vertical U => v.val.val)
        p root q.val) ((verticalEquiv U root q).symm v))

/-- Changing the names of finite edges transports the literal precursor conditions. -/
theorem reindex_precursor {H V H' V' : Type*}
    [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (eh : H ≃ H') (ev : V ≃ V') (hi : H → ℕ) (vi : V → ℕ) (g : H → ℕ)
    (hi' : H' → ℕ) (vi' : V' → ℕ) (g' : H' → ℕ)
    (hh : ∀ x, hi' (eh x) = hi x) (hv : ∀ v, vi' (ev v) = vi v)
    (hg : ∀ x, g' (eh x) = g x) (p : V → H) (hp : Precursor hi vi g p) :
    Precursor hi' vi' g' (fun v => eh (p (ev.symm v))) := by
  classical
  let P := fun v => eh (p (ev.symm v))
  have hc (k : ℕ) (x : H) : beforeCount vi' P k (eh x) = beforeCount vi p k x := by
    unfold beforeCount
    apply Finset.card_bij (fun v _ => ev.symm v)
    · intro v hv'
      simp only [beforeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv' ⊢
      refine ⟨?_, ?_⟩
      · rw [← hv, Equiv.apply_symm_apply]
        exact hv'.1
      · exact eh.injective hv'.2
    · intro v _ w _ he
      exact ev.symm.injective he
    · intro v hv'
      refine ⟨ev v, ?_, ev.symm_apply_apply v⟩
      simpa [beforeSet, P, hv] using hv'
  intro v
  obtain ⟨w, rfl⟩ := ev.surjective v
  change hi' (eh (p (ev.symm (ev w)))) < vi' (ev w) ∧ _
  simp only [Equiv.symm_apply_apply, hh, hv]
  refine ⟨(hp w).1, ?_, ?_⟩
  · rw [hc, hg]
    exact (hp w).2.1
  · intro x hx hxg
    obtain ⟨y, rfl⟩ := eh.surjective x
    rw [hh] at hx ⊢
    rw [hc, hg] at hxg
    exact (hp w).2.2 y hx hxg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical chain formula is a precursor on the inserted word.
Connectedness supplies saturation and the final root edge. -/
theorem assignment_isPrecursor (U : Word n) (p : Vertical U → Horizontal U)
    (hp : IsHorizontalPredecessor U p) (hc : FiniteConnected U)
    (root : Horizontal U) (hr : root.val.val = 0)
    (q : Fin (n+1)) (hq0 : 0 < q.val) (hqn : q.val < n) :
    IsHorizontalPredecessor (insertedWord U root q) (assignment U root q p) := by
  obtain ⟨x, v, hn, hx, hv⟩ := fullRoot_of_connected U p hp hc
  have hex : x = root.val := Fin.ext (by omega)
  let r : Vertical U := ⟨v, hn.end_vertical⟩
  have hpr : p r = root := Subtype.ext (by
    have h := hn.end_assigned
    rw [hex] at h
    simpa [KroneckerPredecessor.extend, hn.end_vertical, r] using h)
  have ht := inserted_precursor (fun x : Horizontal U => x.val.val)
    (fun v : Vertical U => v.val.val)
    (fun _ _ h => Subtype.ext (Fin.ext h)) (fun _ _ h => h)
    (fun x => (U x.val).grade) p ((occurrence_precursor U p).mp hp)
    (connected_saturated U p hp hc) root r hpr
    (fun x => by omega) (fun w => by dsimp [r]; have := w.val.isLt; omega)
    q.val (by omega) (by dsimp [r]; omega)
  apply (occurrence_precursor _ _).mpr
  refine reindex_precursor (horizontalEquiv U root q) (verticalEquiv U root q)
    _ _ _ _ _ _ (horizontal_index U root q) (vertical_index U root q)
    (horizontal_grade U root q) _ ?_
  convert ht using 1 <;> congr 1 <;> exact Subsingleton.elim _ _

/-- The geometric transport preserves the explicit cycle's assignment fibers. -/
theorem assignment_fiber_card (U : Word n) (root : Horizontal U) (q : Fin (n+1))
    (p : Vertical U → Horizontal U) (x : Horizontal U) :
    Nat.card {v : Vertical (insertedWord U root q) // assignment U root q p v = horizontalEquiv U root q x} =
      Nat.card {v : Vertical U // p v = x} + if root = x then 1 else 0 := by
  classical
  let ts := chain (fun x : Horizontal U => x.val.val) (fun v : Vertical U => v.val.val) p root q.val
  let e := (verticalEquiv U root q).symm.subtypeEquiv
    (p := fun v => assignment U root q p v = horizontalEquiv U root q x)
    (q := fun v => KroneckerInsertionPrecursorHelpers.inserted p root ts v = x)
    (fun v => by simp [assignment, ts])
  rw [Nat.card_congr e]
  exact KroneckerInsertionPrecursorHelpers.fiber_count p root x ts

theorem assignment_saturated (U : Word n) (p : Vertical U → Horizontal U)
    (hp : IsHorizontalPredecessor U p) (hc : FiniteConnected U)
    (root : Horizontal U) (q : Fin (n+1)) (x : Horizontal U) :
    assignedBefore (insertedWord U root q) (assignment U root q p) (n+1)
      (horizontalEquiv U root q x) =
      (insertedWord U root q (horizontalEquiv U root q x).val).grade := by
  classical
  rw [assignedBefore_eq_card]
  have hcard := assignment_fiber_card U root q p x
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hcard
  have he : (Finset.univ.filter fun v : Vertical (insertedWord U root q) =>
      v.val.val < n+1 ∧ assignment U root q p v = horizontalEquiv U root q x) =
      Finset.univ.filter (fun v => assignment U root q p v = horizontalEquiv U root q x) := by
    ext v
    have hv : v.val.val < n+1 := v.val.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_right hv
  rw [he, hcard, horizontal_grade]
  have hs := connected_saturated U p hp hc x
  change (fiber p x).card + (if root = x then 1 else 0) = raised (fun y : Horizontal U => (U y.val).grade) root x
  rw [hs]
  simp [raised, eq_comm]

theorem assignment_fullRoot (U : Word n) (p : Vertical U → Horizontal U)
    (hp : IsHorizontalPredecessor U p) (hc : FiniteConnected U)
    (root : Horizontal U) (hr : root.val.val = 0)
    (q : Fin (n+1)) (hq0 : 0 < q.val) (hqn : q.val < n) :
    FullRoot (insertedWord U root q)
      (KroneckerPredecessor.extend _ (assignment U root q p)) := by
  classical
  obtain ⟨x, v, hn, hx, hv⟩ := fullRoot_of_connected U p hp hc
  have hex : x = root.val := Fin.ext (by omega)
  let r : Vertical U := ⟨v, hn.end_vertical⟩
  have hpr : p r = root := Subtype.ext (by
    have h := hn.end_assigned
    rw [hex] at h
    simpa [KroneckerPredecessor.extend, hn.end_vertical, r] using h)
  let eh := horizontalEquiv U root q
  let ev := verticalEquiv U root q
  have hend : (ev (some r)).val.val = n := by
    rw [vertical_index]
    dsimp [verticalIndex, shift, r]
    split_ifs <;> omega
  have hstart : (eh root).val.val = 0 := by
    rw [horizontal_index]
    simp [shift, hr, hq0]
  have hnot : r ∉ chain (fun x : Horizontal U => x.val.val) (fun w : Vertical U => w.val.val) p root q.val := by
    simp [hpr]
  have hass : assignment U root q p (ev (some r)) = eh root := by
    dsimp only [ev, eh]
    simp only [assignment, Equiv.symm_apply_apply]
    rw [KroneckerInsertionPrecursorHelpers.inserted_unchanged p root _ r hnot, hpr]
  refine ⟨(eh root).val, (ev (some r)).val, ?_, hstart, by omega⟩
  exact ⟨(eh root).property, (ev (some r)).property,
    (KroneckerPredecessor.extend_vertical _ _ _).trans (congrArg Subtype.val hass),
    assignment_saturated U p hp hc root q root,
    fun w _ _ => by have := w.isLt; omega⟩

#print axioms assignment_isPrecursor
#print axioms assignment_saturated
#print axioms assignment_fullRoot
end KroneckerInsertionOccurrenceAssembly
