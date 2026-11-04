import KroneckerManuscriptPriorityDefinitions
noncomputable section
open Classical
open scoped BigOperators
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions

namespace Quiver
/-- A directed path records every vertex and arrow, including paths of length zero. -/
structure DirectedPath (Q : Quiver) (n : ℕ) where
  vertex : Fin (n + 1) → Q.Vert
  arrow : Fin n → Q.Arrow
  source_eq : ∀ i, Q.source (arrow i) = vertex i.castSucc
  target_eq : ∀ i, Q.target (arrow i) = vertex i.succ

structure DirectedCycle (Q : Quiver) where
  length : ℕ
  positive : 0 < length
  vertex : Fin (length + 1) → Q.Vert
  arrow : Fin length → Q.Arrow
  source_eq : ∀ i, Q.source (arrow i) = vertex i.castSucc
  target_eq : ∀ i, Q.target (arrow i) = vertex i.succ
  closed : vertex (Fin.last length) = vertex 0
  distinct : Function.Injective (fun i : Fin length => vertex i.castSucc)

def DirectedCycle.path {Q : Quiver} (c : DirectedCycle Q) : DirectedPath Q c.length :=
  ⟨c.vertex, c.arrow, c.source_eq, c.target_eq⟩

def Acyclic (Q : Quiver) : Prop := ¬ Nonempty (DirectedCycle Q)

inductive Traversal (Q : Quiver) : Q.Vert → Q.Vert → Type
  | nil (v) : Traversal Q v v
  | forward {u v} (p : Traversal Q u v) (a : Q.Arrow) (h : Q.source a = v) :
      Traversal Q u (Q.target a)
  | backward {u v} (p : Traversal Q u v) (a : Q.Arrow) (h : Q.target a = v) :
      Traversal Q u (Q.source a)

theorem Covering.unique_outgoing {Q T : Quiver} (p : Covering Q T)
    (v : Q.Vert) (a : T.Arrow) (h : T.source a = p.vertex v) :
    ∃! b : {b : Q.Arrow // Q.source b = v}, p.edge b.val = a := by
  obtain ⟨b, hb⟩ := (p.source_bijective v).2 ⟨a,h⟩
  refine ⟨b, congrArg Subtype.val hb, ?_⟩
  intro c hc
  apply (p.source_bijective v).1
  apply Subtype.ext
  exact hc.trans (congrArg Subtype.val hb).symm
theorem Covering.unique_incoming {Q T : Quiver} (p : Covering Q T)
    (v : Q.Vert) (a : T.Arrow) (h : T.target a = p.vertex v) :
    ∃! b : {b : Q.Arrow // Q.target b = v}, p.edge b.val = a := by
  obtain ⟨b, hb⟩ := (p.target_bijective v).2 ⟨a,h⟩
  refine ⟨b, congrArg Subtype.val hb, ?_⟩
  intro c hc
  apply (p.target_bijective v).1
  apply Subtype.ext
  exact hc.trans (congrArg Subtype.val hb).symm
end Quiver

namespace ColoredBranch
/-- Encode the enlarged tree: the distinguished parent is excluded from all weights. -/
structure Data where
  graph : Graph
  finiteVert : Finite graph.Vert
  finiteEdge : Finite graph.Edge
  tree : graph.IsTree
  bipartition : graph.Bipartition
  color : graph.Edge → Fin 3
  proper : ∀ v e f, v ∈ graph.boundary e → v ∈ graph.boundary f → color e = color f → e = f
  parent : graph.Vert
  root : graph.Vert
  parentEdge : graph.Edge
  endpoints : graph.boundary parentEdge = s(parent, root)
  parent_leaf : ∀ e, parent ∈ graph.boundary e → e = parentEdge
  source_degree : ∀ v ∈ bipartition.sources, v ≠ parent →
    Nat.card {e : graph.Edge // v ∈ graph.boundary e} = 3
attribute [instance] Data.finiteVert Data.finiteEdge
def parentColor (B : Data) : Fin 3 := B.color B.parentEdge
def IsSource (B : Data) : Prop := B.root ∈ B.bipartition.sources
def IsSink (B : Data) : Prop := B.root ∈ B.bipartition.sinks
def sourceCount (B : Data) : ℕ := Nat.card {v : B.graph.Vert // v ∈ B.bipartition.sources ∧ v ≠ B.parent}
def leafCount (B : Data) (d : Fin 3) : ℕ :=
  Nat.card {v : B.graph.Vert // v ∈ B.bipartition.sinks ∧ v ≠ B.parent ∧
    ∃ e, v ∈ B.graph.boundary e ∧ B.color e = d ∧
      ∀ f, v ∈ B.graph.boundary f → f = e}
structure Iso (B D : Data) where
  graphIso : B.graph.Iso D.graph
  parent_eq : graphIso.vertexEquiv B.parent = D.parent
  root_eq : graphIso.vertexEquiv B.root = D.root
  color_eq : ∀ e, D.color (graphIso.edgeEquiv e) = B.color e
  source_iff : ∀ v, graphIso.vertexEquiv v ∈ D.bipartition.sources ↔ v ∈ B.bipartition.sources
  sink_iff : ∀ v, graphIso.vertexEquiv v ∈ D.bipartition.sinks ↔ v ∈ B.bipartition.sinks
end ColoredBranch

namespace Representation
def Res {Q : Quiver} (U : Set Q.Vert) (R : Representation Q) :
    Representation (Q.fullSubquiver U) where
  Space v := R.Space v.val
  arrow a := R.arrow a.val
@[simp] theorem res_dimension {Q : Quiver} (U : Set Q.Vert) (R : Representation Q)
    (v : U) : (Res U R).dimension v = R.dimension v.val := rfl
def ResHom {Q : Quiver} (U : Set Q.Vert) {R S : Representation Q} (f : Hom R S) :
    Hom (Res U R) (Res U S) where
  vertexMap v := f.vertexMap v.val
  commutes a := f.commutes a.val

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The dependent function model equals the original space on U and a zero space off U. -/
def ExtZero {Q : Quiver} (U : Set Q.Vert) (R : Representation (Q.fullSubquiver U)) :
    Representation Q where
  Space v := (h : PLift (v ∈ U)) → R.Space ⟨v,h.down⟩
  spaceFiniteDimensional v := by
    let : Fintype (PLift (v ∈ U)) := Fintype.ofFinite _
    infer_instance
  arrow a := if hs : Q.source a ∈ U then
    { toFun := fun x ht => R.arrow ⟨a,hs,ht.down⟩ (x ⟨hs⟩)
      map_add' := by intros; funext ht; simp
      map_smul' := by intros; funext ht; simp }
    else 0
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def ExtZeroHom {Q : Quiver} (U : Set Q.Vert)
    {R S : Representation (Q.fullSubquiver U)} (f : Hom R S) :
    Hom (ExtZero U R) (ExtZero U S) where
  vertexMap v :=
    { toFun := fun x h => f.vertexMap ⟨v,h.down⟩ (x h)
      map_add' := by intro x y; funext h; exact (f.vertexMap ⟨v,h.down⟩).map_add (x h) (y h)
      map_smul' := by intro c x; funext h; exact (f.vertexMap ⟨v,h.down⟩).map_smul c (x h) }
  commutes a := by
    apply LinearMap.ext
    intro x
    change (fun ht => f.vertexMap ⟨Q.target a,ht.down⟩ ((ExtZero U R).arrow a x ht)) =
      (ExtZero U S).arrow a (fun hs => f.vertexMap ⟨Q.source a,hs.down⟩ (x hs))
    funext ht
    by_cases hs : Q.source a ∈ U
    · have h := LinearMap.congr_fun (f.commutes ⟨a,hs,ht.down⟩) (x ⟨hs⟩)
      simp only [ExtZero, dite_eq_left hs]
      exact h
    · simp only [ExtZero, dite_eq_right hs, LinearMap.zero_apply, Pi.zero_apply]
      exact (f.vertexMap ⟨Q.target a,ht.down⟩).map_zero
theorem extZero_off_support {Q : Quiver} (U : Set Q.Vert)
    (R : Representation (Q.fullSubquiver U)) (v : Q.Vert) (h : v ∉ U) :
    Subsingleton ((ExtZero U R).Space v) := by
  refine ⟨fun f g => ?_⟩
  funext hv
  exact False.elim (h hv.down)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def extZeroAt {Q : Quiver} (U : Set Q.Vert)
    (R : Representation (Q.fullSubquiver U)) (v : U) :
    (ExtZero U R).Space v.val ≃ₗ[ℂ] R.Space v where
  toFun x := x ⟨v.property⟩
  invFun x := fun _ => x
  left_inv x := by funext h; rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem extZero_dimension {Q : Quiver} (U : Set Q.Vert)
    (R : Representation (Q.fullSubquiver U)) (v : U) :
    (ExtZero U R).dimension v.val = R.dimension v := (extZeroAt U R v).finrank_eq
end Representation

def PrefDiff (z y : ℕ → ℕ) (j : ℕ) : ℤ :=
  ((Finset.range j).filter (fun i => z i = 2)).card -
  (((Finset.range j).filter (fun i => y i = 2)).card : ℤ)
def PrefSum (z y : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ j ∈ Finset.range h, (PrefDiff z y (j+1)).natAbs
@[simp] theorem prefDiff_self (z : ℕ → ℕ) (j : ℕ) : PrefDiff z z j = 0 := by simp [PrefDiff]
@[simp] theorem prefSum_self (z : ℕ → ℕ) (h : ℕ) : PrefSum z z h = 0 := by simp [PrefSum]
theorem prefDiff_swap (z y : ℕ → ℕ) (j : ℕ) : PrefDiff z y j = - PrefDiff y z j := by
  simp [PrefDiff]
end KroneckerManuscriptQuiverDefinitions
