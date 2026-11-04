import KroneckerInsertionOccurrenceAssembly
import KroneckerBalanceTraceCorrespondence

/-! Literal geometric insertion, with the explicit precursor assembled from
connectedness. Finite occurrence indices are zero-based. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerGeometricInsertionPrecursor
open KroneckerPaperPaths
open KroneckerPaperPathGradings (Horizontal Vertical edgeIndex)
open KroneckerNaturalPathGradings (Grading bounded)
open KroneckerInsertionOccurrenceAssembly
open KroneckerPrecursorDeletion

/-- The literal inserted step sequence, indexed without a chosen enumeration. -/
def insertedPath (Y : TNEPath) (q : Fin (Y.steps.length+1)) : TNEPath :=
  ofSteps (List.ofFn (Fin.insertNth (α := fun _ => Bool) q false Y.steps.get)) Y.origin

@[simp] theorem inserted_length (Y : TNEPath) (q : Fin (Y.steps.length+1)) :
    (insertedPath Y q).steps.length = Y.steps.length+1 := by simp [insertedPath]

theorem ofFn_insertNth {α : Type*} (s : List α) (b : α) (q : Fin (s.length+1)) :
    List.ofFn (q.insertNth b s.get) = s.take q.val ++ b :: s.drop q.val := by
  have hq : q.val ≤ s.length := by omega
  apply List.ext_getElem (by simp [hq]; omega)
  intro i hi hj
  rw [List.getElem_ofFn hi]
  by_cases hb : i < q.val
  · rw [Fin.insertNth_apply_below (show (⟨i, by simpa using hi⟩ : Fin (s.length+1)) < q from hb)]
    simp [min_eq_left hq, hb, List.get_eq_getElem]
  · by_cases he : i = q.val
    · subst i
      simp [min_eq_left hq]
    · have ha : q.val < i := by omega
      rw [Fin.insertNth_apply_above (show q < (⟨i, by simpa using hi⟩ : Fin (s.length+1)) from ha)]
      have hz : i-q.val ≠ 0 := by omega
      simp [List.getElem_append, min_eq_left hq, hb, List.get_eq_getElem]
      simp [List.getElem_cons, hz, show q.val + (i-q.val-1) = i-1 by omega]

/-- The indexed path is exactly prefix, one vertical edge, and translated suffix. -/
theorem insertedPath_eq (Y : TNEPath) (q : Fin (Y.steps.length+1)) (hq : 0 < q.val) :
    insertedPath Y q = KroneckerPaperPaths.insert Y q.val (ofSteps [false] 0) := by
  apply TNEPath.ext
  · simpa [insertedPath, KroneckerPaperPaths.insert, List.append_assoc] using
      ofFn_insertNth Y.steps false q
  · have hy : Y.steps ≠ [] := by
      have hl : 0 < Y.steps.length := by have := q.isLt; omega
      intro h
      simpa [h] using hl
    have hn : List.ofFn (Fin.insertNth (α := fun _ => Bool) q false Y.steps.get) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
    simp [insertedPath, KroneckerPaperPaths.insert, ofSteps, hy, Nat.ne_of_gt hq]

def edgeIndexEquiv (Y : TNEPath) (q : Fin (Y.steps.length+1)) :
    GeomEdge (insertedPath Y q) ≃ Fin (Y.steps.length+1) :=
  (edgeEquiv (insertedPath Y q)).symm.trans (finCongr (inserted_length Y q))

@[simp] theorem edge_index (Y : TNEPath) (q : Fin (Y.steps.length+1))
    (e : GeomEdge (insertedPath Y q)) : (edgeIndexEquiv Y q e).val = edgeIndex e := rfl

theorem inserted_step (Y : TNEPath) (q : Fin (Y.steps.length+1))
    (e : GeomEdge (insertedPath Y q)) :
    (insertedPath Y q).steps.get ((edgeEquiv _).symm e) =
      Fin.insertNth (α := fun _ => Bool) q false Y.steps.get (edgeIndexEquiv Y q e) := by
  exact List.get_ofFn _ _

abbrev oldWord {Y : TNEPath} (g : Grading Y) :=
  KroneckerPaperPathGradings.occurrenceWord (bounded g)

abbrev newWord {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1)) :=
  insertedWord (oldWord g) root q

theorem newWord_direction {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1))
    (i : Fin (Y.steps.length+1)) :
    KroneckerPredecessor.IsHorizontal (newWord g root q) i ↔
      Fin.insertNth (α := fun _ => Bool) q false Y.steps.get i = true := by
  induction i using Fin.succAboveCases q with
  | x => simp [newWord]
  | p i => simp [newWord, KroneckerPaperPathGradings.occurrenceWord_horizontal]

def newHorizontalEquiv {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1)) :
    Horizontal (insertedPath Y q) ≃ KroneckerPredecessor.Horizontal (newWord g root q) :=
  (edgeIndexEquiv Y q).subtypeEquiv (fun e => by
    rw [newWord_direction, inserted_step])

def newVerticalEquiv {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1)) :
    Vertical (insertedPath Y q) ≃ KroneckerPredecessor.Vertical (newWord g root q) :=
  (edgeIndexEquiv Y q).subtypeEquiv (fun e => by
    rw [newWord_direction, inserted_step]
    cases Fin.insertNth (α := fun _ => Bool) q false Y.steps.get (edgeIndexEquiv Y q e) <;> simp)

def insertedGrading {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1)) :
    Grading (insertedPath Y q) := fun e => (newWord g root q (edgeIndexEquiv Y q e)).grade

def geometricAssignment {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1))
    (p : KroneckerPredecessor.Vertical (oldWord g) → KroneckerPredecessor.Horizontal (oldWord g)) :
    Vertical (insertedPath Y q) → Horizontal (insertedPath Y q) :=
  fun v => (newHorizontalEquiv g root q).symm
    (assignment (oldWord g) root q p (newVerticalEquiv g root q v))

/-- The added edge and copied edges in the literal path. -/
def addedEdge (Y : TNEPath) (q : Fin (Y.steps.length+1)) : GeomEdge (insertedPath Y q) :=
  (edgeIndexEquiv Y q).symm q

def copiedEdge (Y : TNEPath) (q : Fin (Y.steps.length+1))
    (e : GeomEdge Y) : GeomEdge (insertedPath Y q) :=
  (edgeIndexEquiv Y q).symm (q.succAbove ((edgeEquiv Y).symm e))

@[simp] theorem grade_added {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1)) :
    insertedGrading g root q (addedEdge Y q) = 0 := by
  simp [insertedGrading, addedEdge, newWord, KroneckerStack.Edge.grade]

theorem grade_copied {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1))
    (e : GeomEdge Y) :
    insertedGrading g root q (copiedEdge Y q e) =
      g e + if (edgeEquiv Y).symm e = root.val then 1 else 0 := by
  simp only [insertedGrading, copiedEdge, Equiv.apply_symm_apply, newWord, word_copy]
  have hg : (oldWord g ((edgeEquiv Y).symm e)).grade = g e := by
    simpa [oldWord, bounded] using
      KroneckerPaperPathGradings.occurrenceWord_grade (bounded g) ((edgeEquiv Y).symm e)
  split_ifs
  · change (oldWord g ((edgeEquiv Y).symm e)).grade+1 = g e+1
    rw [hg]
  · simpa using hg

def copiedHorizontal {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1))
    (x : KroneckerPredecessor.Horizontal (oldWord g)) : Horizontal (insertedPath Y q) :=
  (newHorizontalEquiv g root q).symm (horizontalEquiv (oldWord g) root q x)

def insertedVertical {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1))
    (v : Option (KroneckerPredecessor.Vertical (oldWord g))) : Vertical (insertedPath Y q) :=
  (newVerticalEquiv g root q).symm (verticalEquiv (oldWord g) root q v)

/-- The geometric map is the explicit endpoint cycle, on the actual copied edges. -/
theorem geometricAssignment_formula {Y : TNEPath} (g : Grading Y)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (q : Fin (Y.steps.length+1))
    (p : KroneckerPredecessor.Vertical (oldWord g) → KroneckerPredecessor.Horizontal (oldWord g))
    (v : Option (KroneckerPredecessor.Vertical (oldWord g))) :
    geometricAssignment g root q p (insertedVertical g root q v) =
      copiedHorizontal g root q (KroneckerInsertionPrecursorHelpers.inserted p root
        (KroneckerInsertionPrecursorAssembly.chain (fun x => x.val.val) (fun w => w.val.val)
          p root q.val) v) := by
  simp [geometricAssignment, insertedVertical, assignment, copiedHorizontal]

/-- No chain, fiber, parent, debt, or local-rule contracts are assumed here. -/
theorem geometricAssignment_isHPrecursor {Y : TNEPath} (g : Grading Y)
    (p : KroneckerPredecessor.Vertical (oldWord g) → KroneckerPredecessor.Horizontal (oldWord g))
    (hp : KroneckerPredecessor.IsHorizontalPredecessor (oldWord g) p)
    (hc : KroneckerNaturalPathGradings.ConnectedGrading g)
    (root : KroneckerPredecessor.Horizontal (oldWord g)) (hr : root.val.val = 0)
    (q : Fin (Y.steps.length+1)) (hq0 : 0 < q.val) (hqn : q.val < Y.steps.length) :
    KroneckerNaturalPathGradings.IsHPrecursor (insertedGrading g root q)
      (geometricAssignment g root q p) := by
  classical
  let : Fintype (Vertical (insertedPath Y q)) :=
    Fintype.ofEquiv _ (newVerticalEquiv g root q).symm
  have hc' : KroneckerPaperConnected.FiniteConnected (oldWord g) := by
    unfold oldWord
    rw [KroneckerBalanceTraceCorrespondence.geometricWord_eq]
    exact hc
  have hp' := (occurrence_precursor _ _).mp (assignment_isPrecursor (oldWord g) p hp hc' root hr q hq0 hqn)
  apply (natural_precursor_iff _ _ _).mpr
  apply reindex_precursor (newHorizontalEquiv g root q).symm (newVerticalEquiv g root q).symm
    _ _ _ _ _ _ ?_ ?_ ?_ _ hp'
  · intro x
    have h := congrArg (fun a => a.val.val) ((newHorizontalEquiv g root q).apply_symm_apply x)
    exact h
  · intro v
    have h := congrArg (fun a => a.val.val) ((newVerticalEquiv g root q).apply_symm_apply v)
    exact h
  · intro x
    have h := congrArg (fun a => (newWord g root q a.val).grade)
      ((newHorizontalEquiv g root q).apply_symm_apply x)
    exact h

/-- Connectedness alone supplies the original map and first horizontal edge.
The conclusion is the explicitly defined insertion assignment on the literal path. -/
theorem connected_assembly {Y : TNEPath} (g : Grading Y)
    (hc : KroneckerNaturalPathGradings.ConnectedGrading g)
    (q : Fin (Y.steps.length+1)) (hq0 : 0 < q.val) (hqn : q.val < Y.steps.length) :
    ∃ (root : KroneckerPredecessor.Horizontal (oldWord g))
      (p : KroneckerPredecessor.Vertical (oldWord g) → KroneckerPredecessor.Horizontal (oldWord g)),
      root.val.val = 0 ∧ KroneckerPredecessor.IsHorizontalPredecessor (oldWord g) p ∧
      insertedPath Y q = KroneckerPaperPaths.insert Y q.val (ofSteps [false] 0) ∧
      KroneckerNaturalPathGradings.IsHPrecursor (insertedGrading g root q)
        (geometricAssignment g root q p) := by
  have hc' : KroneckerPaperConnected.FiniteConnected (oldWord g) := by
    unfold oldWord
    rw [KroneckerBalanceTraceCorrespondence.geometricWord_eq]
    exact hc
  obtain ⟨P, hP, _, x, v, hn, hx, _⟩ := hc'
  let p : KroneckerPredecessor.Vertical (oldWord g) → KroneckerPredecessor.Horizontal (oldWord g) :=
    fun w => ⟨P w.val, (hP w.val w.val.isLt w.property).1⟩
  have hp : KroneckerPredecessor.IsHorizontalPredecessor (oldWord g) p := by
    apply KroneckerPredecessor.valid_congr hP
    intro w _ hw
    simp [KroneckerPredecessor.extend, hw, p]
  let root : KroneckerPredecessor.Horizontal (oldWord g) := ⟨x, hn.start_horizontal⟩
  exact ⟨root, p, hx, hp, insertedPath_eq Y q hq0,
    geometricAssignment_isHPrecursor g p hp hc root hx q hq0 hqn⟩

#print axioms connected_assembly
end KroneckerGeometricInsertionPrecursor
