import KroneckerIteratedBallFinite
import KroneckerLabeledWalkTransport
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/- Original module: KroneckerPathBallGraph -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

/-- One genuine oriented or reverse-oriented arrow as a typed walk. -/
def oneStep (s t : A → V) (x : A × Bool) : LabeledWalk s t (stepStart s t x) (stepEnd s t x) := by
  rcases x with ⟨a,b⟩
  cases b
  · exact .backward a (.nil _)
  · exact .forward a (.nil _)

@[simp] theorem oneStep_labels (x : A × Bool) : labels (oneStep s t x) = [x] := by
  rcases x with ⟨a,b⟩
  cases b <;> rfl

/-- An unfolding edge is defined by appending ONE signed original arrow and
free-reducing the word; it is not defined by equality of endpoint adjacency. -/
def WordNeighbor {u : V} {r : ℕ}
    (p q : ReducedPathBall (s:=s) (t:=t) u r) : Prop :=
  ∃ x : A × Bool, p.val.1 = stepStart s t x ∧
    labels q.val.2 = FreeGroup.reduce (labels p.val.2 ++ [x])

/-- Typed normal forms force the endpoint of every word-defined unfolding edge. -/
theorem wordNeighbor_end {u : V} {r : ℕ}
    (p q : ReducedPathBall (s:=s) (t:=t) u r) (x : A × Bool)
    (hs : p.val.1 = stepStart s t x)
    (hword : labels q.val.2 = FreeGroup.reduce (labels p.val.2 ++ [x])) :
    q.val.1 = stepEnd s t x := by
  let e := castEndpoints hs.symm rfl (oneStep s t x)
  obtain ⟨z,hz,_,_,_⟩ := exists_reduced_normal_form (append p.val.2 e)
  have he : labels z = labels q.val.2 := by
    rw [hz,labels_append]
    simpa only [e,labels_castEndpoints,oneStep_labels] using hword.symm
  exact (labels_heq z q.val.2 rfl he).1.symm

/-- Below the girth threshold every actual edge inside the vertex ball is the
word-defined edge of its unique reduced path representatives. -/
theorem wordNeighbor_of_endpoints {g r : ℕ} (hg : ReducedGirthBound s t g)
    (hr : 2*r+1 < g) {u : V}
    (p q : ReducedPathBall (s:=s) (t:=t) u r) (x : A × Bool)
    (hs : p.val.1 = stepStart s t x) (ht : q.val.1 = stepEnd s t x) : WordNeighbor p q := by
  let e := castEndpoints hs.symm ht.symm (oneStep s t x)
  obtain ⟨z,hz,hzr,hzl,_⟩ := exists_reduced_normal_form (append p.val.2 e)
  have he : (labels z).length + (labels q.val.2).length < g := by
    simp only [labels_append,List.length_append,e,labels_castEndpoints,oneStep_labels,
      List.length_singleton] at hzl
    have hp := p.property.2
    have hq := q.property.2
    omega
  have hq : z = q.val.2 := reduced_paths_unique_below_girth hg z q.val.2 hzr q.property.1 he
  refine ⟨x,hs,?_⟩
  rw [←hq,hz,labels_append]
  simp only [e,labels_castEndpoints,oneStep_labels]

/-- The actual induced undirected radius-ball graph, retaining an existential
signed arrow witness and excluding loops as required for SimpleGraph. -/
def vertexBallGraph (u : V) (r : ℕ) : SimpleGraph (VertexBall (s:=s) (t:=t) u r) where
  Adj p q := p ≠ q ∧ ∃x : A × Bool, p.val = stepStart s t x ∧ q.val = stepEnd s t x
  symm := by
    constructor
    intro p q h
    rcases h with ⟨hpq,⟨⟨a,b⟩,hs,ht⟩⟩
    refine ⟨Ne.symm hpq,⟨(a,!b),?_,?_⟩⟩ <;>
      cases b <;> simpa [stepStart,stepEnd] using (by assumption)
  loopless := ⟨by intro p h; exact h.1 rfl⟩

/-- Canonical word-normal-form adjacency on the truncated unfolding. -/
def pathBallGraph (u : V) (r : ℕ) : SimpleGraph (ReducedPathBall (s:=s) (t:=t) u r) where
  Adj p q := p ≠ q ∧ (WordNeighbor p q ∨ WordNeighbor q p)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,h.2.symm⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩

theorem pathBallGraph_adj_iff {g r : ℕ} (hg : ReducedGirthBound s t g)
    (hr : 2*r+1 < g) (u : V)
    (p q : ReducedPathBall (s:=s) (t:=t) u r) :
    (pathBallGraph u r).Adj p q ↔ (vertexBallGraph u r).Adj (ballEndpoint p) (ballEndpoint q) := by
  have hinj := ballEndpoint_injective hg (by omega : 2*r < g) u
  constructor
  · rintro ⟨hpq,h | h⟩
    · obtain ⟨x,hs,hw⟩ := h
      exact ⟨fun he => hpq (hinj he),x,hs,wordNeighbor_end p q x hs hw⟩
    · obtain ⟨x,hs,hw⟩ := h
      apply (vertexBallGraph u r).symm.symm
      exact ⟨fun he => hpq (hinj he.symm),x,hs,wordNeighbor_end q p x hs hw⟩
  · rintro ⟨hpq,x,hs,ht⟩
    exact ⟨fun he => hpq (congrArg ballEndpoint he),Or.inl (wordNeighbor_of_endpoints hg hr p q x hs ht)⟩

/-- Explicit graph isomorphism between the actual induced radius ball and the
truncated word-normal-form unfolding. This does not identify the entire cover
with a universal tree. -/
noncomputable def pathBallGraphIso {g r : ℕ} (hg : ReducedGirthBound s t g)
    (hr : 2*r+1 < g) (u : V) : pathBallGraph (s:=s) (t:=t) u r ≃g vertexBallGraph (s:=s) (t:=t) u r where
  toEquiv := pathBallEquiv hg (by omega) u
  map_rel_iff' := by intro p q; exact (pathBallGraph_adj_iff hg hr u p q).symm

end LabeledWalk
namespace TypedQuiver
open LabeledWalk

/-- Concrete iteration depth supporting the graph-level radius-ball bridge. -/
noncomputable def iterate_pathBallGraphIso (Q : TypedQuiver) (r : ℕ)
    [DecidableEq (Q.iterate (2*r+2)).A]
    (u : (Q.iterate (2*r+2)).V) :
    pathBallGraph (s:=(Q.iterate (2*r+2)).source) (t:=(Q.iterate (2*r+2)).target) u r ≃g
      vertexBallGraph (s:=(Q.iterate (2*r+2)).source) (t:=(Q.iterate (2*r+2)).target) u r := by
  classical
  apply pathBallGraphIso (iterate_girth Q (2*r+1)) _ u
  have h : 2*r+1 < 2^(2*r+1) := Nat.lt_two_pow_self
  omega

end TypedQuiver
end KroneckerAbelianCover
end

/- Original module: KroneckerLabeledGraphForest -/
section
set_option autoImplicit false
namespace KroneckerAbelianCover
namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

private theorem prefix_reduced (x : A × Bool) {u v : V} (p : LabeledWalk s t u v)
    (hp : Reduced p) (hx : stepStart s t x ∉ vertices p) :
    List.IsChain (fun a b : A × Bool => a.1 ≠ b.1 ∨ a.2 = b.2) (x :: labels p) := by
  cases p with
  | nil => simp [labels]
  | forward a p =>
    simp only [labels,List.isChain_cons_cons]
    refine ⟨?_,hp⟩
    rcases x with ⟨b,ε⟩
    cases ε with
    | true => exact Or.inr rfl
    | false =>
      left
      intro h
      change b = a at h
      subst b
      apply hx
      exact List.mem_cons_of_mem _ (start_mem_vertices p)
  | backward a p =>
    simp only [labels,List.isChain_cons_cons]
    refine ⟨?_,hp⟩
    rcases x with ⟨b,ε⟩
    cases ε with
    | false => exact Or.inr rfl
    | true =>
      left
      intro h
      change b = a at h
      subst b
      apply hx
      exact List.mem_cons_of_mem _ (start_mem_vertices p)

/-- Vertex-simple typed walks cannot contain immediate inverse arrows. -/
theorem reduced_of_vertices_nodup {u v : V} (p : LabeledWalk s t u v)
    (hp : (vertices p).Nodup) : Reduced p := by
  induction p with
  | nil => simp [Reduced,labels]
  | forward a p ih =>
    have hh := List.nodup_cons.mp hp
    exact prefix_reduced (a,true) p (ih hh.2) hh.1
  | backward a p ih =>
    have hh := List.nodup_cons.mp hp
    exact prefix_reduced (a,false) p (ih hh.2) hh.1

/-- Prepend a signed actual arrow with explicit endpoint identifications. -/
def consStep (x : A × Bool) {u v w : V}
    (hs : stepStart s t x = u) (ht : stepEnd s t x = v)
    (p : LabeledWalk s t v w) : LabeledWalk s t u w := by
  rcases x with ⟨a,b⟩
  cases b
  · dsimp [stepStart,stepEnd] at hs ht
    subst u; subst v
    exact .backward a p
  · dsimp [stepStart,stepEnd] at hs ht
    subst u; subst v
    exact .forward a p

theorem consStep_vertices (x : A × Bool) {u v w : V}
    (hs : stepStart s t x = u) (ht : stepEnd s t x = v)
    (p : LabeledWalk s t v w) : vertices (consStep x hs ht p) = u :: vertices p := by
  rcases x with ⟨a,b⟩
  cases b <;> dsimp [stepStart,stepEnd] at hs ht <;> subst u <;> subst v <;> rfl

end LabeledWalk
open LabeledWalk

/-- The actual underlying simple graph of a labeled quiver. Loops are omitted;
parallel labels are retained as witnesses rather than silently identified in
walk lifting. -/
def underlyingGraph {V A : Type} (s t : A → V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃x : A × Bool, u = stepStart s t x ∧ v = stepEnd s t x
  symm := by
    constructor
    intro p q h
    rcases h with ⟨hpq,⟨⟨a,b⟩,hs,ht⟩⟩
    refine ⟨Ne.symm hpq,⟨(a,!b),?_,?_⟩⟩ <;>
      cases b <;> simpa [stepStart,stepEnd] using (by assumption)
  loopless := ⟨by intro p h; exact h.1 rfl⟩

namespace LabeledWalk
variable {V A : Type} [DecidableEq A] {s t : A → V}

/-- Lift every graph walk, choosing actual signed arrow witnesses for its edges. -/
noncomputable def ofGraph {u v : V} (p : (underlyingGraph s t).Walk u v) :
    LabeledWalk s t u v := by
  induction p with
  | nil => exact .nil _
  | @cons u v w h p ih =>
    let x := Classical.choose h.2
    have hx := Classical.choose_spec h.2
    exact consStep x hx.1.symm hx.2.symm ih

theorem ofGraph_vertices {u v : V} (p : (underlyingGraph s t).Walk u v) :
    vertices (ofGraph p) = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih => simpa only [ofGraph,consStep_vertices,SimpleGraph.Walk.support_cons] using congrArg (List.cons _) ih

theorem ofGraph_reduced {u v : V} (p : (underlyingGraph s t).Walk u v)
    (hp : p.IsPath) : Reduced (ofGraph p) := by
  apply reduced_of_vertices_nodup
  rw [ofGraph_vertices]
  exact hp.support_nodup

/-- The internal all-reduced-loop criterion yields Mathlib's actual graph
acyclicity predicate, by unique lifting of all simple graph paths. -/
theorem underlyingGraph_acyclic
    (hf : ∀ u (p : LabeledWalk s t u u), Reduced p → labels p = []) :
    (underlyingGraph s t).IsAcyclic := by
  apply SimpleGraph.isAcyclic_iff_subsingleton_path.mpr
  intro u v
  refine ⟨fun p q => ?_⟩
  apply Subtype.ext
  apply SimpleGraph.Walk.support_injective
  have he := reduced_paths_unique_of_forest hf (ofGraph p.val) (ofGraph q.val)
    (ofGraph_reduced p.val p.property) (ofGraph_reduced q.val q.property)
  have hv := congrArg vertices he
  simpa only [ofGraph_vertices] using hv

end LabeledWalk
namespace TypedQuiver
open LabeledWalk

/-- Every finite actual arrow subquiver of size at most m is an acyclic simple
graph at depth m+1. This is Mathlib IsAcyclic, not an assumed tree predicate. -/
theorem iterate_restricted_acyclic (Q : TypedQuiver) (m : ℕ)
    [DecidableEq (Q.iterate (m+1)).A]
    (F : Finset (Q.iterate (m+1)).A) (hF : F.card ≤ m) :
    (underlyingGraph ((Q.iterate (m+1)).restrictArrows F).source
      ((Q.iterate (m+1)).restrictArrows F).target).IsAcyclic := by
  classical
  exact underlyingGraph_acyclic (fun u p hp => iterate_restricted_forest Q m F hF p hp)

/-- Each genuine connected component of that finite-support graph is a tree. -/
theorem iterate_restricted_component_tree (Q : TypedQuiver) (m : ℕ)
    [DecidableEq (Q.iterate (m+1)).A]
    (F : Finset (Q.iterate (m+1)).A) (hF : F.card ≤ m)
    (c : (underlyingGraph ((Q.iterate (m+1)).restrictArrows F).source
      ((Q.iterate (m+1)).restrictArrows F).target).ConnectedComponent) :
    c.toSimpleGraph.IsTree :=
  (iterate_restricted_acyclic Q m F hF).isTree_connectedComponent c

end TypedQuiver
end KroneckerAbelianCover
end
