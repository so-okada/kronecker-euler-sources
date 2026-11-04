import KroneckerManuscriptQuiverDefinitions
import Mathlib.CategoryTheory.Category.Basic

noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions
namespace Quiver
structure Hom (Q R : Quiver) where
  vertex : Q.Vert → R.Vert
  edge : Q.Edge → R.Edge
  map_source : ∀ e, R.source (edge e) = vertex (Q.source e)
  map_target : ∀ e, R.target (edge e) = vertex (Q.target e)
def Hom.id (Q : Quiver) : Hom Q Q := ⟨fun v => v, fun e => e, fun _ => rfl, fun _ => rfl⟩
def Hom.comp {Q R S : Quiver} (g : Hom R S) (f : Hom Q R) : Hom Q S where
  vertex := g.vertex ∘ f.vertex
  edge := g.edge ∘ f.edge
  map_source e := (g.map_source (f.edge e)).trans (congrArg g.vertex (f.map_source e))
  map_target e := (g.map_target (f.edge e)).trans (congrArg g.vertex (f.map_target e))
@[simp] theorem Hom.id_comp {Q R : Quiver} (f : Hom Q R) : (Hom.id R).comp f = f := rfl
@[simp] theorem Hom.comp_id {Q R : Quiver} (f : Hom Q R) : f.comp (Hom.id Q) = f := rfl
theorem Hom.comp_assoc {Q R S T : Quiver} (h : Hom S T) (g : Hom R S) (f : Hom Q R) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl
def Iso.toHom {Q R : Quiver} (f : Q.Iso R) : Hom Q R :=
  ⟨f.vertexEquiv, f.arrowEquiv, f.map_source, f.map_target⟩
structure Subquiver (Q : Quiver) where
  vertices : Set Q.Vert
  edges : Set Q.Edge
  endpoints : ∀ e ∈ edges, Q.source e ∈ vertices ∧ Q.target e ∈ vertices
def Subquiver.toQuiver {Q : Quiver} (U : Subquiver Q) : Quiver where
  Vert := U.vertices
  Edge := U.edges
  delta e := (⟨Q.source e.val, (U.endpoints e.val e.property).1⟩,
    ⟨Q.target e.val, (U.endpoints e.val e.property).2⟩)
def Subquiver.inclusion {Q : Quiver} (U : Subquiver Q) : Hom U.toQuiver Q :=
  ⟨Subtype.val, Subtype.val, fun _ => rfl, fun _ => rfl⟩
end Quiver
namespace ColoredQuiver
structure Hom {C : Type} (Q R : ColoredQuiver C) where
  quiverHom : Quiver.Hom Q.1 R.1
  preserves_color : ∀ e, R.QCol (quiverHom.edge e) = Q.QCol e
def Hom.id {C : Type} (Q : ColoredQuiver C) : Hom Q Q :=
  ⟨Quiver.Hom.id Q.1, fun _ => rfl⟩
def Hom.comp {C : Type} {Q R S : ColoredQuiver C} (g : Hom R S) (f : Hom Q R) : Hom Q S :=
  ⟨g.quiverHom.comp f.quiverHom, fun e =>
    (g.preserves_color (f.quiverHom.edge e)).trans (f.preserves_color e)⟩
def Iso.toHom {C : Type} {Q R : ColoredQuiver C} (f : Iso Q R) : Hom Q R :=
  ⟨f.quiverIso.toHom, f.preserves_color⟩
def subquiver {C : Type} (Q : ColoredQuiver C) (U : Quiver.Subquiver Q.1) : ColoredQuiver C :=
  ⟨U.toQuiver, fun e => Q.QCol e.val⟩
end ColoredQuiver
namespace Representation
abbrev SubRep {Q : Quiver} (R : Representation Q) :=
  KroneckerFiniteQuiverHom.SubrepOn R.toRepresentationOn
def SubRep.toRepresentation {Q : Quiver} {R : Representation Q} (W : R.SubRep) : Representation Q where
  Space v := W.space v
  arrow e := (R.arrow e).restrict (W.invariant e)
def arrowOverHom {Q T : Quiver} (R : Representation T) (f : Quiver.Hom Q T) (e : Q.Edge) :
    R.Space (f.vertex (Q.source e)) →ₗ[ℂ] R.Space (f.vertex (Q.target e)) :=
  (R.spaceCast (f.map_target e)).toLinearMap.comp
    ((R.arrow (f.edge e)).comp (R.spaceCast (f.map_source e)).symm.toLinearMap)
structure HomOver {Q T : Quiver} (R : Representation Q) (S : Representation T)
    (f : Quiver.Hom Q T) where
  vertexMap : ∀ v, R.Space v →ₗ[ℂ] S.Space (f.vertex v)
  commutes : ∀ e, (vertexMap (Q.target e)).comp (R.arrow e) =
    (S.arrowOverHom f e).comp (vertexMap (Q.source e))
abbrev Hom {Q : Quiver} (R S : Representation Q) := HomOver R S (Quiver.Hom.id Q)
def Iso.toHomOver {Q T : Quiver} {R : Representation Q} {S : Representation T}
    {f : Q.Iso T} (g : Iso R S f) : HomOver R S f.toHom :=
  ⟨fun v => (g.vertexIso v).toLinearMap, g.commutes⟩
@[simp] theorem spaceCast_trans {Q : Quiver} (R : Representation Q) {u v w : Q.Vert}
    (h : u = v) (k : v = w) (x : R.Space u) :
    R.spaceCast k (R.spaceCast h x) = R.spaceCast (h.trans k) x := by
  cases h; cases k; rfl
@[simp] theorem spaceCast_symm_apply {Q : Quiver} (R : Representation Q) {u v : Q.Vert}
    (h : u = v) (x : R.Space v) : (R.spaceCast h).symm x = R.spaceCast h.symm x := by
  cases h; rfl
@[simp] theorem HomOver.map_cast {Q T : Quiver} {R : Representation Q} {S : Representation T}
    {f : Quiver.Hom Q T} (g : HomOver R S f) {u v : Q.Vert} (h : u = v) (x : R.Space u) :
    g.vertexMap v (R.spaceCast h x) = S.spaceCast (congrArg f.vertex h) (g.vertexMap u x) := by
  cases h; rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def HomOver.comp {Q T U : Quiver} {R : Representation Q} {S : Representation T}
    {P : Representation U} {f : Quiver.Hom Q T} {g : Quiver.Hom T U}
    (b : HomOver S P g) (a : HomOver R S f) : HomOver R P (g.comp f) where
  vertexMap v := (b.vertexMap (f.vertex v)).comp (a.vertexMap v)
  commutes e := by
    ext x
    have ha := LinearMap.congr_fun (a.commutes e) x
    have hb := LinearMap.congr_fun (b.commutes (f.edge e))
      (S.spaceCast (f.map_source e).symm (a.vertexMap (Q.source e) x))
    simp only [LinearMap.comp_apply, arrowOverHom, LinearEquiv.coe_toLinearMap,
      spaceCast_symm_apply] at ha hb ⊢
    change b.vertexMap (f.vertex (Q.target e)) (a.vertexMap (Q.target e) (R.arrow e x)) = _
    rw [ha, b.map_cast, hb]
    simp only [b.map_cast, spaceCast_trans]
    rfl

@[ext] theorem HomOver.ext {Q T : Quiver} {R : Representation Q} {S : Representation T}
    {f : Quiver.Hom Q T} {a b : HomOver R S f}
    (h : ∀ v, a.vertexMap v = b.vertexMap v) : a = b := by
  cases a
  cases b
  congr
  exact funext h

def Hom.id {Q : Quiver} (R : Representation Q) : Hom R R where
  vertexMap _ := LinearMap.id
  commutes _ := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def Hom.comp {Q : Quiver} {R S T : Representation Q} (g : Hom S T) (f : Hom R S) : Hom R T where
  vertexMap v := (g.vertexMap v).comp (f.vertexMap v)
  commutes e := by
    have hf := f.commutes e
    have hg := g.commutes e
    change (f.vertexMap (Q.target e)).comp (R.arrow e) =
      (S.arrow e).comp (f.vertexMap (Q.source e)) at hf
    change (g.vertexMap (Q.target e)).comp (S.arrow e) =
      (T.arrow e).comp (g.vertexMap (Q.source e)) at hg
    change ((g.vertexMap (Q.target e)).comp (f.vertexMap (Q.target e))).comp (R.arrow e) =
      (T.arrow e).comp ((g.vertexMap (Q.source e)).comp (f.vertexMap (Q.source e)))
    rw [LinearMap.comp_assoc, hf, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]

instance category (Q : Quiver) : CategoryTheory.Category (Representation Q) where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp f := by ext v x; rfl
  comp_id f := by ext v x; rfl
  assoc f g h := by ext v x; rfl

end Representation
abbrev SubColRep {C : Type} {Q : ColoredQuiver C} (R : ColoredRepresentation Q) := R.SubRep
structure ColoredRepresentationHom {C : Type} {Q T : ColoredQuiver C}
    (R : ColoredRepresentation Q) (S : ColoredRepresentation T) where
  coloredHom : ColoredQuiver.Hom Q T
  representationHom : Representation.HomOver R S coloredHom.quiverHom
namespace ColoredRepresentationHom
def id {C : Type} {Q : ColoredQuiver C} (R : ColoredRepresentation Q) : ColoredRepresentationHom R R :=
  ⟨ColoredQuiver.Hom.id Q, Representation.Hom.id R⟩
def comp {C : Type} {Q T U : ColoredQuiver C} {R : ColoredRepresentation Q}
    {S : ColoredRepresentation T} {P : ColoredRepresentation U}
    (g : ColoredRepresentationHom S P) (f : ColoredRepresentationHom R S) :
    ColoredRepresentationHom R P :=
  ⟨g.coloredHom.comp f.coloredHom, g.representationHom.comp f.representationHom⟩
@[simp] theorem id_comp {C : Type} {Q T : ColoredQuiver C} {R : ColoredRepresentation Q}
    {S : ColoredRepresentation T} (f : ColoredRepresentationHom R S) : (id S).comp f = f := rfl
@[simp] theorem comp_id {C : Type} {Q T : ColoredQuiver C} {R : ColoredRepresentation Q}
    {S : ColoredRepresentation T} (f : ColoredRepresentationHom R S) : f.comp (id R) = f := rfl
theorem comp_assoc {C : Type} {Q T U V : ColoredQuiver C} {R : ColoredRepresentation Q}
    {S : ColoredRepresentation T} {P : ColoredRepresentation U} {N : ColoredRepresentation V}
    (h : ColoredRepresentationHom P N) (g : ColoredRepresentationHom S P)
    (f : ColoredRepresentationHom R S) : (h.comp g).comp f = h.comp (g.comp f) := rfl
end ColoredRepresentationHom
/-- Distinct object wrapper prevents identification with the fixed-base Rep category. -/
structure ColRep {C : Type} (Q : ColoredQuiver C) where
  representation : ColoredRepresentation Q
instance colRepCategory {C : Type} (Q : ColoredQuiver C) : CategoryTheory.Category (ColRep Q) where
  Hom R S := ColoredRepresentationHom R.representation S.representation
  id R := ColoredRepresentationHom.id R.representation
  comp f g := g.comp f
  id_comp := ColoredRepresentationHom.comp_id
  comp_id := ColoredRepresentationHom.id_comp
  assoc f g h := (ColoredRepresentationHom.comp_assoc h g f).symm

namespace Graph
inductive Walk (G : Graph) : G.Vert → G.Vert → Type
  | nil (v) : Walk G v v
  | cons {u v w} (e : G.Edge) (h : G.boundary e = s(u,v)) (p : Walk G v w) : Walk G u w
def Walk.vertices {G : Graph} {u v : G.Vert} : Walk G u v → List G.Vert
  | .nil u => [u]
  | .cons (u := u) _ _ p => u :: p.vertices
def Walk.edges {G : Graph} {u v : G.Vert} : Walk G u v → List G.Edge
  | .nil _ => []
  | .cons e _ p => e :: p.edges
def Walk.IsSimplePath {G : Graph} {u v : G.Vert} (p : Walk G u v) : Prop := p.vertices.Nodup
def Walk.IsCycle {G : Graph} {u : G.Vert} (p : Walk G u u) : Prop :=
  p.edges ≠ [] ∧ p.vertices.dropLast.Nodup ∧ p.edges.Nodup
def Walk.append {G : Graph} {u v w : G.Vert} (p : Walk G u v) (q : Walk G v w) : Walk G u w :=
  match p with
  | .nil _ => q
  | .cons e h p => .cons e h (p.append q)
def Walk.reverse {G : Graph} {u v : G.Vert} (p : Walk G u v) : Walk G v u :=
  match p with
  | .nil u => .nil u
  | .cons e h p => p.reverse.append (.cons e (h.trans Sym2.eq_swap) (.nil _))
def reachableSetoid (G : Graph) : Setoid G.Vert where
  r u v := Nonempty (Walk G u v)
  iseqv := ⟨fun v => ⟨.nil v⟩, fun ⟨p⟩ => ⟨p.reverse⟩,
    fun ⟨p⟩ ⟨q⟩ => ⟨p.append q⟩⟩
def componentVertices (G : Graph) (v : G.Vert) : Set G.Vert :=
  {w | (G.reachableSetoid).r v w}
def IsForest (G : Graph) : Prop := ∃ h : G.IsSimple, (G.simpleGraph h).IsAcyclic

def Connected (G : Graph) : Prop := ∀ u v, Nonempty (Walk G u v)
theorem connected_of_isEmpty (G : Graph) [IsEmpty G.Vert] : G.Connected :=
  fun u => isEmptyElim u
def Walk.toSimple {G : Graph} (h : G.IsSimple) {u v : G.Vert} (p : Walk G u v) :
    (G.simpleGraph h).Walk u v :=
  match p with
  | .nil _ => .nil
  | .cons e he p => .cons ⟨e,he⟩ (p.toSimple h)
def Walk.ofSimple {G : Graph} (h : G.IsSimple) {u v : G.Vert}
    (p : (G.simpleGraph h).Walk u v) : Walk G u v :=
  match p with
  | .nil => .nil _
  | .cons huv p => .cons (Classical.choose huv) (Classical.choose_spec huv) (Walk.ofSimple h p)
theorem connected_iff_simple (G : Graph) (h : G.IsSimple) :
    G.Connected ↔ (G.simpleGraph h).Preconnected := by
  constructor
  · intro hw u v
    exact ⟨(Classical.choice (hw u v)).toSimple h⟩
  · intro hc
    exact fun u v => ⟨Walk.ofSimple h (Classical.choice (hc u v))⟩
theorem tree_iff_connected_forest (G : Graph) :
    G.IsTree ↔ Nonempty G.Vert ∧ G.Connected ∧ G.IsForest := by
  constructor
  · rintro ⟨h,ht⟩
    exact ⟨ht.connected.nonempty,(G.connected_iff_simple h).mpr ht.connected.preconnected,
      ⟨h,ht.isAcyclic⟩⟩
  · rintro ⟨hn,hc,h,hf⟩
    let := hn
    exact ⟨h,⟨{preconnected := (G.connected_iff_simple h).mp hc},hf⟩⟩

def leaves (G : Graph) : Set G.Vert := {v | G.Leaf v}
structure Subgraph (G : Graph) where
  vertices : Set G.Vert
  edges : Set G.Edge
  endpoints : ∀ e ∈ edges, ∃ u ∈ vertices, ∃ v ∈ vertices, G.boundary e = s(u,v)
def Subgraph.induced (G : Graph) (U : Set G.Vert) : Subgraph G where
  vertices := U
  edges := {e | ∃ u ∈ U, ∃ v ∈ U, G.boundary e = s(u,v)}
  endpoints _ h := h
private theorem Subgraph.endpoint_pair {G : Graph} (H : Subgraph G) (e : H.edges) :
    ∃ p : H.vertices × H.vertices, G.boundary e.val = s(p.1.val,p.2.val) := by
  obtain ⟨u,hu,v,hv,h⟩ := H.endpoints e.val e.property
  exact ⟨(⟨u,hu⟩,⟨v,hv⟩),h⟩
def Subgraph.toGraph {G : Graph} (H : Subgraph G) : Graph where
  Vert := H.vertices
  Edge := H.edges
  boundary e := Sym2.mk (Classical.choose (H.endpoint_pair e)).1 (Classical.choose (H.endpoint_pair e)).2
theorem Subgraph.map_boundary {G : Graph} (H : Subgraph G) (e : H.edges) :
    Sym2.map Subtype.val (H.toGraph.boundary e) = G.boundary e.val :=
  (Classical.choose_spec (H.endpoint_pair e)).symm
def connectedComponent (G : Graph) (v : G.Vert) : Graph :=
  (Subgraph.induced G (G.componentVertices v)).toGraph
theorem connectedComponent_nonempty (G : Graph) (v : G.Vert) :
    Nonempty (G.connectedComponent v).Vert := ⟨⟨v,⟨.nil v⟩⟩⟩

def ProperEdgeColoring (G : Graph) {C : Type} (c : G.Edge → C) : Prop :=
  G.IsSimple ∧ ∀ e f u v w, G.boundary e = s(u,v) → G.boundary f = s(u,w) → e ≠ f → c e ≠ c f
/-- A finite bipartite tree, encoded by its two vertex parts and incidence relation. -/
structure SourceTrivalentTree where
  Source : Type
  Sink : Type
  [sourceFintype : Fintype Source]
  [sinkFintype : Fintype Sink]
  incidence : Source → Sink → Prop
  tree : (KroneckerBipartiteIncidence.incidenceGraph incidence).IsTree
  source_degree : ∀ i, Nat.card {j // incidence i j} = 3
attribute [instance] SourceTrivalentTree.sourceFintype SourceTrivalentTree.sinkFintype
structure ColoredSourceTrivalentTree extends SourceTrivalentTree where
  color : {p : Source × Sink // incidence p.1 p.2} → Fin 3
  proper_source : ∀ i j k (h : incidence i j) (h' : incidence i k),
    j ≠ k → color ⟨(i,j),h⟩ ≠ color ⟨(i,k),h'⟩
  proper_sink : ∀ i k j (h : incidence i j) (h' : incidence k j),
    i ≠ k → color ⟨(i,j),h⟩ ≠ color ⟨(k,j),h'⟩

end Graph
end KroneckerManuscriptQuiverDefinitions
