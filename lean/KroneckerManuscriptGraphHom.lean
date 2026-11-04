import KroneckerManuscriptRevision

noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions
namespace Graph
structure Hom (G H : Graph) where
  vertex : G.Vert → H.Vert
  edge : G.Edge → H.Edge
  map_boundary : ∀ e, H.boundary (edge e) = Sym2.map vertex (G.boundary e)
def Hom.id (G : Graph) : Hom G G where
  vertex := fun v => v
  edge := fun e => e
  map_boundary e := by simp

def Hom.comp {G H K : Graph} (g : Hom H K) (f : Hom G H) : Hom G K where
  vertex := g.vertex ∘ f.vertex
  edge := g.edge ∘ f.edge
  map_boundary e := by
    change K.boundary (g.edge (f.edge e)) = _
    rw [g.map_boundary, f.map_boundary, Sym2.map_map]
@[simp] theorem Hom.id_comp {G H : Graph} (f : Hom G H) : (Hom.id H).comp f = f := rfl
@[simp] theorem Hom.comp_id {G H : Graph} (f : Hom G H) : f.comp (Hom.id G) = f := rfl
theorem Hom.comp_assoc {G H K L : Graph} (h : Hom K L) (g : Hom H K) (f : Hom G H) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl
theorem Hom.edge_eq_of_vertex_eq {G H : Graph} (h : H.IsSimple) (f g : Hom G H)
    (hv : f.vertex = g.vertex) : f.edge = g.edge := by
  funext e
  apply h.2
  rw [f.map_boundary,g.map_boundary,hv]

def Iso.toHom {G H : Graph} (f : G.Iso H) : Hom G H :=
  ⟨f.vertexEquiv,f.edgeEquiv,f.map_boundary⟩
def CutConnected (G : Graph) : Prop :=
  ∀ U : Set G.Vert, U.Nonempty → U ≠ Set.univ →
    ∃ u ∈ U, ∃ v ∉ U, ∃ e, G.boundary e = s(u,v)
theorem connected_iff_cutConnected (G : Graph) : G.Connected ↔ G.CutConnected := by
  classical
  constructor
  · intro hp U hU hproper
    by_contra h
    push Not at h
    obtain ⟨u,hu⟩ := hU
    have hv : ∃ v, v ∉ U := by
      by_contra hh
      push Not at hh
      exact hproper (Set.eq_univ_of_forall hh)
    obtain ⟨v,hv⟩ := hv
    obtain ⟨p⟩ := hp u v
    have closed : ∀ {a b}, Walk G a b → a ∈ U → b ∈ U := by
      intro a b q
      induction q with
      | nil => exact fun h => h
      | @cons a b c e he q ih =>
        intro ha
        apply ih
        by_contra hb
        exact h a ha b hb e he
    exact hv (closed p hu)
  · intro hcut u v
    by_contra hv
    let U : Set G.Vert := {w | Nonempty (Walk G u w)}
    have hu : u ∈ U := ⟨Walk.nil u⟩
    have hproper : U ≠ Set.univ := by
      intro h
      exact hv (show v ∈ U from h ▸ Set.mem_univ v)
    obtain ⟨a,ha,b,hb,e,he⟩ := hcut U ⟨u,hu⟩ hproper
    obtain ⟨p⟩ := ha
    exact hb ⟨p.append (Walk.cons e he (Walk.nil b))⟩

end Graph

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def Quiver.Hom.graphHom {Q R : Quiver} (f : Quiver.Hom Q R) :
    Graph.Hom Q.underlyingGraph R.underlyingGraph where
  vertex := f.vertex
  edge := f.edge
  map_boundary e := by
    change s(R.source (f.edge e), R.target (f.edge e)) = s(f.vertex (Q.source e), f.vertex (Q.target e))
    rw [f.map_source, f.map_target]

def ColoredGraph (C : Type) := Σ G : Graph, G.Edge → C
structure ColoredGraph.Hom {C : Type} (G H : ColoredGraph C) where
  graphHom : Graph.Hom G.1 H.1
  preserves_color : ∀ e, H.2 (graphHom.edge e) = G.2 e

def ColoredQuiver.underlyingColoredGraph {C : Type} (Q : ColoredQuiver C) : ColoredGraph C :=
  ⟨Q.1.underlyingGraph, Q.QCol⟩
def ColoredQuiver.Hom.graphHom {C : Type} {Q R : ColoredQuiver C} (f : ColoredQuiver.Hom Q R) :
    ColoredGraph.Hom Q.underlyingColoredGraph R.underlyingColoredGraph :=
  ⟨f.quiverHom.graphHom, f.preserves_color⟩

abbrev Quiver.SubQuiv (Q : Quiver) (U : Set Q.Vert) := Q.fullSubquiver U
abbrev ColoredQuiver.SubColQuiv {C : Type} (Q : ColoredQuiver C) (U : Set Q.1.Vert) := Q.fullSubquiver U

@[simp] theorem Representation.supportQuiver_eq_SubQuiv {Q : Quiver} (R : Representation Q) :
    R.supportQuiver = Q.SubQuiv R.support := rfl
abbrev ColoredRepresentation.SuppColQuiv {C : Type} {Q : ColoredQuiver C}
    (R : ColoredRepresentation Q) := ColoredRepresentation.supportQuiver R
@[simp] theorem ColoredRepresentation.SuppColQuiv_eq_SubColQuiv {C : Type} {Q : ColoredQuiver C}
    (R : ColoredRepresentation Q) : R.SuppColQuiv = Q.SubColQuiv R.support := rfl
@[simp] theorem ColoredRepresentation.supportQuiver_eq_SubColQuiv {C : Type} {Q : ColoredQuiver C}
    (R : ColoredRepresentation Q) : ColoredRepresentation.supportQuiver R = Q.SubColQuiv R.support := rfl
end KroneckerManuscriptQuiverDefinitions
