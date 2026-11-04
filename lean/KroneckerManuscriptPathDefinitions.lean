import KroneckerGeometricPredecessor
import KroneckerOrientationPositions
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace KroneckerPaperPaths

def orientationIndices (P : TNEPath) (b : Bool) : Finset (Edge P) :=
  Finset.univ.filter (fun k => P.steps.get k = b)

theorem orientationIndices_card (P : TNEPath) (b : Bool) :
    (orientationIndices P b).card = P.steps.count b := by
  simpa [orientationIndices, KroneckerOrientationPositions.Positions,
    Fintype.card_subtype, List.get_eq_getElem] using
    KroneckerOrientationPositions.positions_card P.steps b

def labeledEdge (P : TNEPath) (b : Bool) (k : Fin (P.steps.count b)) : GeomEdge P :=
  edgeEquiv P ((orientationIndices P b).orderEmbOfFin (orientationIndices_card P b) k)

theorem labeledEdge_direction (P : TNEPath) (b : Bool) (k : Fin (P.steps.count b)) :
    P.steps.get ((edgeEquiv P).symm (labeledEdge P b k)) = b := by
  have h := Finset.orderEmbOfFin_mem (orientationIndices P b) (orientationIndices_card P b) k
  have h' := (Finset.mem_filter.mp h).2
  simpa only [labeledEdge, Equiv.symm_apply_apply] using h'

theorem labeledEdge_order (P : TNEPath) (b : Bool) :
    StrictMono (fun k => ((edgeEquiv P).symm (labeledEdge P b k)).val) := by
  intro i j hij
  simp only [labeledEdge, Equiv.symm_apply_apply]
  exact ((orientationIndices P b).orderEmbOfFin (orientationIndices_card P b)).strictMono hij

theorem labeledEdge_exhausts (P : TNEPath) (b : Bool) (v : GeomEdge P)
    (hv : P.steps.get ((edgeEquiv P).symm v) = b) : ∃ k, labeledEdge P b k = v := by
  let x : orientationIndices P b := ⟨(edgeEquiv P).symm v, by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩
  obtain ⟨k, hk⟩ := ((orientationIndices P b).orderIsoOfFin
    (orientationIndices_card P b)).surjective x
  refine ⟨k, ?_⟩
  have he := congrArg Subtype.val hk
  change (orientationIndices P b).orderEmbOfFin (orientationIndices_card P b) k =
    (edgeEquiv P).symm v at he
  simp only [labeledEdge, he, Equiv.apply_symm_apply]

def subpathEdgeSet (P : TNEPath) (i j : ℕ) : Set (GeomEdge P) :=
  {v | i ≤ ((edgeEquiv P).symm v).val ∧ ((edgeEquiv P).symm v).val < j}

theorem subpathEdgeSet_geometry (P : TNEPath) (i j : ℕ) (hj : j ≤ P.steps.length)
    (v : GeomEdge P) : v ∈ subpathEdgeSet P i j ↔
      ∃ k : Edge (subpath P i j), edge (subpath P i j) k = v.val := by
  constructor
  · intro h
    let a := (edgeEquiv P).symm v
    let k : Edge (subpath P i j) := ⟨a.val-i, by
      simp only [subpath_steps, List.length_take, List.length_drop]
      change i ≤ a.val ∧ a.val < j at h
      omega⟩
    refine ⟨k, ?_⟩
    rw [subpath_edge P i j hj k]
    have he : subpathEdge P i j hj k = a := by
      apply Fin.ext
      change i + (a.val-i) = a.val
      exact Nat.add_sub_of_le h.1
    rw [he]
    exact congrArg Subtype.val ((edgeEquiv P).apply_symm_apply v)
  · rintro ⟨k, hk⟩
    rw [subpath_edge P i j hj k] at hk
    have he : edgeEquiv P (subpathEdge P i j hj k) = v := Subtype.ext hk
    have hi := congrArg (fun z => ((edgeEquiv P).symm z).val) he
    simp only [Equiv.symm_apply_apply, subpathEdge] at hi
    have hb := k.isLt
    simp only [subpath_steps, List.length_take, List.length_drop] at hb
    change i ≤ ((edgeEquiv P).symm v).val ∧ ((edgeEquiv P).symm v).val < j
    omega

structure CyclicSubpath (P : TNEPath) where
  first : Edge P
  last : Edge P

def CyclicSubpath.edges {P : TNEPath} (C : CyclicSubpath P) : List (GeomEdge P) :=
  List.ofFn (fun k => edgeEquiv P (cyclicIndex C.first C.last k))

def CyclicSubpath.Included {P : TNEPath} (A B : CyclicSubpath P) : Prop :=
  ∃ i j : ℕ, i < j ∧ j ≤ B.edges.length ∧ A.edges = (B.edges.drop i).take (j-i)

def CyclicSubpath.Disjoint {P : TNEPath} (A B : CyclicSubpath P) : Prop :=
  _root_.Disjoint (A.edges.toFinset) (B.edges.toFinset)

end KroneckerPaperPaths

namespace KroneckerPaperPathGradings
open KroneckerPaperPaths

def horizontalShadow {m : ℕ} {P : TNEPath} (g : Grading m P) (u : Edge P) :
    Set (GeomEdge P) :=
  if ∃ v, FirstShadow g u v then
    {w | P.steps.get ((edgeEquiv P).symm w) = false ∧
      ∃ v, FirstShadow g u v ∧ w ∈ (CyclicSubpath.mk u v).edges}
  else {w | P.steps.get ((edgeEquiv P).symm w) = false}

def ShadowComponent {m : ℕ} {P : TNEPath} (g : Grading m P) (C : CyclicSubpath P) : Prop :=
  FirstShadow g C.first C.last ∧ ∀ D : CyclicSubpath P,
    FirstShadow g D.first D.last → C.Included D → D.Included C

def Tight {m : ℕ} {P : TNEPath} (g : Grading m P) : Prop :=
  Compatible g ∧ ∀ v : Vertical P, 0 < (g v.val).val →
    ∃ u : Horizontal P, 0 < (g u.val).val ∧
      v.val ∈ horizontalShadow g ((edgeEquiv P).symm u.val)

theorem horizontalShadow_nonclosing {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u : Edge P) (h : ¬∃ v, FirstShadow g u v) :
    horizontalShadow g u = {w | P.steps.get ((edgeEquiv P).symm w) = false} := by
  simp only [horizontalShadow, h, ↓reduceIte]

def intervalNorthCount {P : TNEPath} (i j : ℕ) : ℕ :=
  ∑ k ∈ KroneckerPredecessor.intervalEdges (n := P.steps.length) i j,
    if P.steps.get k = false then 1 else 0

def intervalEastGrade {m : ℕ} {P : TNEPath} (g : Grading m P) (i j : ℕ) : ℕ :=
  ∑ k ∈ KroneckerPredecessor.intervalEdges i j,
    if P.steps.get k = true then (g (edgeEquiv P k)).val else 0

theorem intervalNorthCount_core {m : ℕ} {P : TNEPath} (g : Grading m P) (i j : ℕ) :
    KroneckerPredecessor.intervalVerticalCount (occurrenceWord g) i j =
      intervalNorthCount (P := P) i j := by
  unfold KroneckerPredecessor.intervalVerticalCount intervalNorthCount
  apply Finset.sum_congr rfl
  intro k _
  simp only [occurrenceWord_horizontal]
  cases P.steps.get k <;> simp

theorem intervalEastGrade_core {m : ℕ} {P : TNEPath} (g : Grading m P) (i j : ℕ) :
    KroneckerPredecessor.intervalHorizontalGrade (occurrenceWord g) i j =
      intervalEastGrade g i j := by
  simp only [KroneckerPredecessor.intervalHorizontalGrade, intervalEastGrade,
    occurrenceWord_horizontal, occurrenceWord_grade]

theorem isNode_iff_first_shadow_counts {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (hp : IsPredecessor g p)
    (x : Horizontal P) (v : Vertical P) :
    IsNode g p x v ↔ edgeIndex x.val < edgeIndex v.val ∧
      intervalNorthCount (P := P) (edgeIndex x.val) (edgeIndex v.val+1) =
        intervalEastGrade g (edgeIndex x.val) (edgeIndex v.val+1) ∧
      ∀ k, edgeIndex x.val < k → k ≤ edgeIndex v.val →
        intervalNorthCount (P := P) (edgeIndex x.val) k <
          intervalEastGrade g (edgeIndex x.val) k := by
  rw [isNode_iff]
  rw [KroneckerPredecessor.isNode_iff_first_horizontal_shadow
    ((isPredecessor_iff g p).mp hp)]
  simp only [(horizontalEquiv g x).property, (verticalEquiv g v).property,
    not_false_eq_true, true_and, intervalNorthCount_core, intervalEastGrade_core]
  rfl

end KroneckerPaperPathGradings

#print axioms KroneckerPaperPathGradings.isNode_iff_first_shadow_counts
#print axioms KroneckerPaperPaths.subpathEdgeSet_geometry
