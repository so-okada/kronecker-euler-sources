import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Translated north-east paths

The geometric interface of Definitions 2.2--2.3. `true` is an east step and
`false` a north step. Empty paths have one normalized representative; the
paper's starting point is exposed only for nonempty paths. Internal lists
and their existing word proofs are unchanged.
-/
set_option autoImplicit false

namespace KroneckerPaperPaths

abbrev LatticePoint := ℤ × ℤ

structure TNEPath where
  steps : List Bool
  origin : LatticePoint
  empty_origin : steps = [] → origin = 0

@[ext] theorem TNEPath.ext {P Q : TNEPath}
    (hs : P.steps = Q.steps) (ho : P.origin = Q.origin) : P = Q := by
  cases P
  cases Q
  cases hs
  cases ho
  rfl

/-- Normalize the otherwise immaterial location of an empty path. -/
def ofSteps (s : List Bool) (o : LatticePoint) : TNEPath where
  steps := s
  origin := if s = [] then 0 else o
  empty_origin := by intro h; simp [h]

@[simp] theorem ofSteps_steps (s : List Bool) (o : LatticePoint) :
    (ofSteps s o).steps = s := rfl

@[simp] theorem ofSteps_origin_of_ne_nil (s : List Bool) (o : LatticePoint)
    (h : s ≠ []) : (ofSteps s o).origin = o := by simp [ofSteps, h]

def empty : TNEPath := ofSteps [] 0

@[simp] theorem empty_steps : empty.steps = [] := rfl
@[simp] theorem empty_origin : empty.origin = 0 := rfl

theorem eq_empty_iff (P : TNEPath) : P = empty ↔ P.steps = [] := by
  constructor
  · intro h; simp [h]
  · intro h
    apply TNEPath.ext h
    exact P.empty_origin h

@[simp] theorem ofSteps_nil (o : LatticePoint) : ofSteps [] o = empty := by
  apply TNEPath.ext <;> simp [ofSteps, empty]

/-- Unlike the internal normalized origin, `Start_pt` requires a nonempty path. -/
def Start_pt (P : TNEPath) (_h : P ≠ empty) : LatticePoint := P.origin

def stepVector (b : Bool) : LatticePoint := if b then (1, 0) else (0, 1)

def displacement : List Bool → LatticePoint
  | [] => 0
  | b :: bs => stepVector b + displacement bs

@[simp] theorem displacement_nil : displacement [] = 0 := rfl

theorem displacement_append (s t : List Bool) :
    displacement (s ++ t) = displacement s + displacement t := by
  induction s with
  | nil => simp [displacement]
  | cons b s ih => simp [displacement, ih, add_assoc]

theorem displacement_sum (s : List Bool) :
    (displacement s).1 + (displacement s).2 = (s.length : ℤ) := by
  induction s with
  | nil => simp [displacement]
  | cons b s ih =>
    cases b <;> simp [displacement, stepVector] at * <;> omega

/-- The internal vertex evaluator; paper boundaries satisfy `i ≤ P.steps.length`. -/
def vertex (P : TNEPath) (i : ℕ) : LatticePoint :=
  P.origin + displacement (P.steps.take i)

abbrev Edge (P : TNEPath) := Fin P.steps.length

/-- The ordered endpoints of a geometric unit edge. -/
def edge (P : TNEPath) (k : Edge P) : LatticePoint × LatticePoint :=
  (vertex P k.val, vertex P (k.val + 1))

theorem steps_ne_nil_of_edge (P : TNEPath) (k : Edge P) : P.steps ≠ [] := by
  intro h
  have hk := k.isLt
  simp [h] at hk

theorem vertex_sum (P : TNEPath) (i : ℕ) (hi : i ≤ P.steps.length) :
    (vertex P i).1 + (vertex P i).2 = P.origin.1 + P.origin.2 + (i : ℤ) := by
  have h := displacement_sum (P.steps.take i)
  simp only [List.length_take, Nat.min_eq_left hi] at h
  change P.origin.1 + (displacement (P.steps.take i)).1 +
      (P.origin.2 + (displacement (P.steps.take i)).2) = _
  omega

theorem edge_injective (P : TNEPath) : Function.Injective (edge P) := by
  intro k l h
  have hv : vertex P k.val = vertex P l.val := congrArg Prod.fst h
  have hs := congrArg (fun v : LatticePoint => v.1 + v.2) hv
  rw [vertex_sum P k.val (Nat.le_of_lt k.isLt),
    vertex_sum P l.val (Nat.le_of_lt l.isLt)] at hs
  apply Fin.ext
  omega

theorem edge_direction (P : TNEPath) (k : Edge P) :
    (edge P k).2 - (edge P k).1 = stepVector (P.steps.get k) := by
  change (P.origin + displacement (P.steps.take (k.val + 1))) -
    (P.origin + displacement (P.steps.take k.val)) = stepVector (P.steps.get k)
  rw [List.take_succ_eq_append_getElem k.isLt, displacement_append]
  simp only [displacement, add_zero, List.get_eq_getElem]
  abel

/-- Actual geometric edges, with occurrence indices recovered uniquely. -/
abbrev GeomEdge (P : TNEPath) := Set.range (edge P)

noncomputable def edgeEquiv (P : TNEPath) : Edge P ≃ GeomEdge P where
  toFun k := ⟨edge P k, ⟨k, rfl⟩⟩
  invFun e := Classical.choose e.property
  left_inv k := edge_injective P (Classical.choose_spec
    (show ∃ i : Edge P, edge P i = edge P k from ⟨k, rfl⟩))
  right_inv e := by
    apply Subtype.ext
    exact Classical.choose_spec e.property

@[simp] theorem edgeEquiv_apply (P : TNEPath) (k : Edge P) :
    ((edgeEquiv P) k).val = edge P k := rfl

@[simp] theorem edgeEquiv_symm_apply_apply (P : TNEPath) (k : Edge P) :
    (edgeEquiv P).symm ((edgeEquiv P) k) = k :=
  (edgeEquiv P).symm_apply_apply k

/-- Definition 2.2: Trans(P,ζ)=P+ζ; the argument t denotes ζ. -/
def translate (P : TNEPath) (t : LatticePoint) : TNEPath :=
  ofSteps P.steps (P.origin + t)

@[simp] theorem translate_steps (P : TNEPath) (t : LatticePoint) :
    (translate P t).steps = P.steps := rfl

@[simp] theorem translate_empty (t : LatticePoint) : translate empty t = empty := by
  simp [translate]

theorem translate_origin (P : TNEPath) (t : LatticePoint) (h : P.steps ≠ []) :
    (translate P t).origin = P.origin + t := by simp [translate, h]

@[simp] theorem translate_zero (P : TNEPath) : translate P 0 = P := by
  apply TNEPath.ext
  · rfl
  by_cases h : P.steps = []
  · simp [translate, ofSteps, h, P.empty_origin h]
  · simp [translate, ofSteps, h]

theorem translate_add (P : TNEPath) (s t : LatticePoint) :
    translate (translate P s) t = translate P (s + t) := by
  apply TNEPath.ext
  · rfl
  by_cases h : P.steps = [] <;> simp [translate, ofSteps, h, add_assoc]

@[simp] theorem translate_neg (P : TNEPath) (t : LatticePoint) :
    translate (translate P t) (-t) = P := by rw [translate_add]; simp

theorem vertex_translate (P : TNEPath) (t : LatticePoint) (i : ℕ)
    (h : P.steps ≠ []) : vertex (translate P t) i = vertex P i + t := by
  simp [vertex, translate, ofSteps, h, add_assoc, add_comm]

theorem edge_translate (P : TNEPath) (t : LatticePoint) (k : Edge P) :
    edge (translate P t) k = ((edge P k).1 + t, (edge P k).2 + t) := by
  simp [edge, vertex_translate, steps_ne_nil_of_edge P k]

/-- The initial vertex comes from the first nonempty factor. -/
def concat (U V : TNEPath) : TNEPath :=
  ofSteps (U.steps ++ V.steps) (if U.steps = [] then V.origin else U.origin)

@[simp] theorem concat_steps (U V : TNEPath) :
    (concat U V).steps = U.steps ++ V.steps := rfl

@[simp] theorem empty_concat (P : TNEPath) : concat empty P = P := by
  apply TNEPath.ext
  · simp [concat]
  · by_cases h : P.steps = []
    · simp [concat, ofSteps, h, P.empty_origin h]
    · simp [concat, ofSteps, h]

@[simp] theorem concat_empty (P : TNEPath) : concat P empty = P := by
  apply TNEPath.ext
  · simp [concat]
  · by_cases h : P.steps = []
    · simp [concat, ofSteps, h, P.empty_origin h]
    · simp [concat, ofSteps, h]

/-- Used for the paper's `0 ≤ i ≤ j ≤ |P|`; outside that range lists truncate. -/
def subpath (P : TNEPath) (i j : ℕ) : TNEPath :=
  ofSteps ((P.steps.drop i).take (j - i)) (vertex P i)

@[simp] theorem subpath_steps (P : TNEPath) (i j : ℕ) :
    (subpath P i j).steps = (P.steps.drop i).take (j - i) := rfl

@[simp] theorem subpath_self (P : TNEPath) (i : ℕ) : subpath P i i = empty := by
  simp [subpath]

theorem subpath_origin (P : TNEPath) (i j : ℕ) (hij : i < j)
    (hj : j ≤ P.steps.length) : (subpath P i j).origin = vertex P i := by
  have hs : (P.steps.drop i).take (j - i) ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_take, List.length_drop, List.length_nil] at hl
    omega
  simp [subpath, hs]

theorem subpath_vertex (P : TNEPath) (i j k : ℕ) (hij : i < j)
    (hj : j ≤ P.steps.length) (hk : k ≤ j - i) :
    vertex (subpath P i j) k = vertex P (i + k) := by
  change (subpath P i j).origin +
    displacement (((P.steps.drop i).take (j - i)).take k) = _
  rw [subpath_origin P i j hij hj, List.take_take, Nat.min_eq_left hk]
  simp only [vertex, List.take_add, displacement_append, add_assoc]

/-- The ambient occurrence of an edge of a literal subpath. -/
def subpathEdge (P : TNEPath) (i j : ℕ) (hj : j ≤ P.steps.length)
    (k : Edge (subpath P i j)) : Edge P :=
  ⟨i + k.val, by
    have hk := k.isLt
    simp only [subpath_steps, List.length_take, List.length_drop] at hk
    omega⟩

theorem subpath_edge (P : TNEPath) (i j : ℕ) (hj : j ≤ P.steps.length)
    (k : Edge (subpath P i j)) :
    edge (subpath P i j) k = edge P (subpathEdge P i j hj k) := by
  have hk := k.isLt
  simp only [subpath_steps, List.length_take, List.length_drop] at hk
  have hij : i < j := by omega
  have hk0 : k.val ≤ j - i := by omega
  have hk1 : k.val + 1 ≤ j - i := by omega
  change (vertex (subpath P i j) k.val, vertex (subpath P i j) (k.val + 1)) =
    (vertex P (i + k.val), vertex P (i + k.val + 1))
  rw [subpath_vertex P i j k.val hij hj hk0,
    subpath_vertex P i j (k.val + 1) hij hj hk1]
  simp [Nat.add_assoc]

def simpleRun (j : ℕ) (_hj : 0 < j) : TNEPath :=
  ofSteps (true :: List.replicate j false) 0

@[simp] theorem simpleRun_steps (j : ℕ) (hj : 0 < j) :
    (simpleRun j hj).steps = true :: List.replicate j false := rfl

/-- Insert by literal prefix--path--suffix concatenation. -/
def insert (U : TNEPath) (i : ℕ) (V : TNEPath) : TNEPath :=
  ofSteps (U.steps.take i ++ V.steps ++ U.steps.drop i)
    (if i = 0 ∧ V.steps ≠ [] then V.origin else
      if U.steps = [] then V.origin else U.origin)

@[simp] theorem insert_steps (U V : TNEPath) (i : ℕ) :
    (insert U i V).steps = U.steps.take i ++ V.steps ++ U.steps.drop i := rfl

@[simp] theorem insert_empty (V : TNEPath) : insert empty 0 V = V := by
  apply TNEPath.ext
  · simp [insert]
  · by_cases h : V.steps = []
    · simp [insert, ofSteps, h, V.empty_origin h]
    · simp [insert, ofSteps, h]

/-- The paper's prefix concatenated with the suffix translated by `(0,-1)`. -/
def deleteVertical (U : TNEPath) (k : Edge U) (_hk : U.steps.get k = false) : TNEPath :=
  concat (subpath U 0 k.val)
    (translate (subpath U (k.val + 1) U.steps.length) (0, -1))

theorem ofSteps_translate (s : List Bool) (o t : LatticePoint) :
    translate (ofSteps s o) t = ofSteps s (o + t) := by
  apply TNEPath.ext
  · rfl
  · by_cases h : s = [] <;> simp [translate, ofSteps, h]

theorem translate_to_origin (P : TNEPath) (o : LatticePoint) :
    translate P (o - P.origin) = ofSteps P.steps o := by
  apply TNEPath.ext
  · rfl
  · by_cases h : P.steps = []
    · simp [translate, ofSteps, h]
    · simp [translate, ofSteps, h]

theorem subpath_translate (P : TNEPath) (t : LatticePoint) (i j : ℕ) :
    subpath (translate P t) i j = translate (subpath P i j) t := by
  by_cases h : P.steps = []
  · simp [subpath, translate, ofSteps, h]
  · change ofSteps ((P.steps.drop i).take (j - i)) (vertex (translate P t) i) = _
    rw [vertex_translate P t i h]
    exact (ofSteps_translate _ _ _).symm

theorem concat_origin (U V : TNEPath) (hU : U.steps ≠ []) :
    (concat U V).origin = U.origin := by
  simp [concat, ofSteps, hU]

@[simp] theorem subpath_prefix_steps (P : TNEPath) (i : ℕ) :
    (subpath P 0 i).steps = P.steps.take i := by simp [subpath]

@[simp] theorem subpath_suffix_steps (P : TNEPath) (i : ℕ) :
    (subpath P i P.steps.length).steps = P.steps.drop i := by
  change (P.steps.drop i).take (P.steps.length - i) = _
  rw [← List.length_drop]
  exact List.take_length

@[simp] theorem deleteVertical_steps (U : TNEPath) (k : Edge U)
    (hk : U.steps.get k = false) :
    (deleteVertical U k hk).steps = U.steps.take k.val ++ U.steps.drop (k.val + 1) := by
  simp only [deleteVertical, concat_steps, translate_steps,
    subpath_prefix_steps, subpath_suffix_steps]

theorem deleteVertical_paper_formula (U : TNEPath) (k : Edge U)
    (hk : U.steps.get k = false) :
    deleteVertical U k hk = concat (subpath U 0 k.val)
      (translate (subpath U (k.val + 1) U.steps.length) (0, -1)) := rfl

/-- The suffix of a concatenation is precisely the translated second factor. -/
theorem concat_suffix (U V : TNEPath) (hU : U.steps ≠ []) :
    subpath (concat U V) U.steps.length (U.steps.length + V.steps.length) =
      translate V (U.origin + displacement U.steps - V.origin) := by
  have hs : ((U.steps ++ V.steps).drop U.steps.length).take
      (U.steps.length + V.steps.length - U.steps.length) = V.steps := by
    simp
  unfold subpath
  change ofSteps (((U.steps ++ V.steps).drop U.steps.length).take
    (U.steps.length + V.steps.length - U.steps.length))
    (vertex (concat U V) U.steps.length) = _
  rw [hs, translate_to_origin]
  congr 1
  simp [vertex, concat_origin U V hU]

theorem insert_nonempty (U V : TNEPath) (i : ℕ) (hU : U.steps ≠ []) :
    (insert U i V).steps ≠ [] := by
  intro h
  have hparts : U.steps.take i = [] ∧ V.steps = [] ∧ U.steps.drop i = [] := by
    simpa [insert, List.append_eq_nil_iff, and_assoc] using h
  apply hU
  rw [← List.take_append_drop i U.steps, hparts.1, hparts.2.2]
  rfl

/-- The manuscript's direct concatenation formula for insertion. -/
theorem insert_paper_formula (U V : TNEPath) (i : ℕ) :
    insert U i V = concat (concat (subpath U 0 i) V)
      (subpath U i U.steps.length) := by
  apply TNEPath.ext
  · simp only [insert_steps, concat_steps, subpath_prefix_steps, subpath_suffix_steps]
  · by_cases hU : U.steps = []
    · by_cases hV : V.steps = [] <;>
        simp [insert, concat, subpath, ofSteps, hU, hV]
    · by_cases hi : i = 0
      · subst i
        by_cases hV : V.steps = []
        · simp [insert, concat, subpath, vertex, ofSteps, hU, hV]
        · simp [insert, concat, subpath, vertex, ofSteps, hU, hV]
      · have hp : U.steps.take i ≠ [] := by
          intro h
          have hl := congrArg List.length h
          simp only [List.length_take, List.length_nil] at hl
          have hu : 0 < U.steps.length := List.length_pos_iff.mpr hU
          omega
        have hq : U.steps.take i ++ V.steps ≠ [] := by
          intro h
          exact hp (List.append_eq_nil_iff.mp h).1
        have hall : U.steps.take i ++ V.steps ++ U.steps.drop i ≠ [] := by
          intro h
          exact hq (List.append_eq_nil_iff.mp h).1
        simp [insert, concat, subpath, vertex, ofSteps, hU, hi, hp, hq]


/-- Definition 2.2: the ending point is defined only for a nonempty path. -/
def End_pt (P : TNEPath) (_h : P ≠ empty) : LatticePoint := vertex P P.steps.length

private theorem nonempty_length_pos (P : TNEPath) (h : P ≠ empty) :
    0 < P.steps.length := by
  exact List.length_pos_iff.mpr (fun hs => h ((eq_empty_iff P).mpr hs))

/-- Definition 2.2: the actual geometric starting edge. -/
noncomputable def Start_NE (P : TNEPath) (h : P ≠ empty) : GeomEdge P :=
  edgeEquiv P ⟨0, nonempty_length_pos P h⟩

/-- Definition 2.2: the actual geometric ending edge. -/
noncomputable def End_NE (P : TNEPath) (h : P ≠ empty) : GeomEdge P :=
  edgeEquiv P ⟨P.steps.length - 1, by have := nonempty_length_pos P h; omega⟩

@[simp] theorem Start_NE_index (P : TNEPath) (h : P ≠ empty) :
    ((edgeEquiv P).symm (Start_NE P h)).val = 0 := by simp [Start_NE]

@[simp] theorem End_NE_index (P : TNEPath) (h : P ≠ empty) :
    ((edgeEquiv P).symm (End_NE P h)).val = P.steps.length - 1 := by simp [End_NE]

theorem Start_NE_point (P : TNEPath) (h : P ≠ empty) :
    (Start_NE P h).val.1 = Start_pt P h := by
  simp [Start_NE, edge, vertex, Start_pt]

theorem End_NE_point (P : TNEPath) (h : P ≠ empty) :
    (End_NE P h).val.2 = End_pt P h := by
  have hn : P.steps.length - 1 + 1 = P.steps.length := by
    have := nonempty_length_pos P h
    omega
  simp [End_NE, edge, End_pt, hn]

end KroneckerPaperPaths
