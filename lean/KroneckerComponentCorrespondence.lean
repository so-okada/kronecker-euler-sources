import KroneckerStructuredBipartitions
import KroneckerManuscriptGraphHom

/-! Connected components as maximal nonempty connected induced subgraphs.
The result applies to the manuscript graph model, including loops and
parallel edges. No finiteness or simplicity hypothesis is used. -/

noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions.Graph

def MaximalConnectedVertices (G : Graph) (U : Set G.Vert) : Prop :=
  U.Nonempty ∧ (Subgraph.induced G U).toGraph.Connected ∧
    ∀ V : Set G.Vert, U ⊆ V → (Subgraph.induced G V).toGraph.Connected → V ⊆ U

/-- A walk in an induced subgraph is a walk in the ambient graph. -/
def induced_walk_to_ambient (G : Graph) (U : Set G.Vert)
    {a b : (Subgraph.induced G U).toGraph.Vert}
    (p : Walk (Subgraph.induced G U).toGraph a b) : Walk G a.val b.val := by
  induction p with
  | nil a => exact .nil a.val
  | @cons a b c e he p ih =>
      apply Walk.cons e.val _ ih
      have h := (Subgraph.induced G U).map_boundary e
      rw [he] at h
      exact h.symm

/-- A walk lifts to an induced subgraph when its vertices are closed under
edges leaving that subgraph. -/
theorem walk_lift_closed (G : Graph) (U : Set G.Vert)
    (closed : ∀ a ∈ U, ∀ b e, G.boundary e = s(a,b) → b ∈ U)
    {a b : G.Vert} (p : Walk G a b) (ha : a ∈ U) :
    ∃ hb : b ∈ U, Nonempty (Walk (Subgraph.induced G U).toGraph ⟨a,ha⟩ ⟨b,hb⟩) := by
  induction p with
  | nil a =>
      refine ⟨ha, ⟨?_⟩⟩
      exact Walk.nil (G := (Subgraph.induced G U).toGraph) (⟨a,ha⟩ : {v : G.Vert // v ∈ U})
  | @cons a b c e he p ih =>
      have hb : b ∈ U := closed a ha b e he
      obtain ⟨hc, ⟨q⟩⟩ := ih hb
      let e' : (Subgraph.induced G U).toGraph.Edge := ⟨e, ⟨a,ha,b,hb,he⟩⟩
      have h' : (Subgraph.induced G U).toGraph.boundary e' = s(⟨a,ha⟩,⟨b,hb⟩) := by
        apply Sym2.map.injective (show Function.Injective (@Subtype.val G.Vert U) from Subtype.val_injective)
        calc
          _ = G.boundary e := (Subgraph.induced G U).map_boundary e'
          _ = s(a,b) := he
          _ = Sym2.map Subtype.val s(⟨a,ha⟩,⟨b,hb⟩) := rfl
      exact ⟨hc, ⟨.cons e' h' q⟩⟩

theorem component_closed (G : Graph) (root : G.Vert) :
    ∀ a ∈ G.componentVertices root, ∀ b e, G.boundary e = s(a,b) →
      b ∈ G.componentVertices root := by
  intro a ha b e he
  obtain ⟨p⟩ := ha
  exact ⟨p.append (.cons e he (.nil b))⟩

theorem component_connected (G : Graph) (root : G.Vert) :
    (Subgraph.induced G (G.componentVertices root)).toGraph.Connected := by
  intro a b
  obtain ⟨pa⟩ := a.property
  obtain ⟨pb⟩ := b.property
  obtain ⟨hb, h⟩ := walk_lift_closed G (G.componentVertices root)
    (component_closed G root) (pa.reverse.append pb) a.property
  exact h

theorem connected_vertices_subset_component (G : Graph) (U : Set G.Vert)
    (hU : (Subgraph.induced G U).toGraph.Connected) (root : G.Vert) (hr : root ∈ U) :
    U ⊆ G.componentVertices root := by
  intro v hv
  obtain ⟨p⟩ := hU ⟨root,hr⟩ ⟨v,hv⟩
  exact ⟨induced_walk_to_ambient G U p⟩

theorem component_maximal (G : Graph) (root : G.Vert) :
    MaximalConnectedVertices G (G.componentVertices root) := by
  refine ⟨⟨root, ⟨.nil root⟩⟩, component_connected G root, ?_⟩
  intro V hsub hV
  have hr : root ∈ V := hsub ⟨.nil root⟩
  exact connected_vertices_subset_component G V hV root hr

theorem maximal_iff_component (G : Graph) (U : Set G.Vert) :
    MaximalConnectedVertices G U ↔ ∃ root : G.Vert, U = G.componentVertices root := by
  constructor
  · rintro ⟨⟨root,hr⟩, hU, hmax⟩
    have hsub := connected_vertices_subset_component G U hU root hr
    have hrev := hmax (G.componentVertices root) hsub (component_connected G root)
    exact ⟨root, Set.Subset.antisymm hsub hrev⟩
  · rintro ⟨root,rfl⟩
    exact component_maximal G root

/-- The manuscript's set of maximal induced subgraphs equals the existing
reachable-component set, as actual graph objects. -/
theorem ctdComp_iff_maximal (G : Graph) (H : Graph) :
    H ∈ G.CtdComp ↔ ∃ U : Set G.Vert,
      MaximalConnectedVertices G U ∧ H = (Subgraph.induced G U).toGraph := by
  constructor
  · rintro ⟨root, rfl⟩
    exact ⟨G.componentVertices root, component_maximal G root, rfl⟩
  · rintro ⟨U, hU, hH⟩
    obtain ⟨root, rfl⟩ := (maximal_iff_component G U).mp hU
    exact ⟨root, hH.symm⟩

end KroneckerManuscriptQuiverDefinitions.Graph

#print axioms KroneckerManuscriptQuiverDefinitions.Graph.induced_walk_to_ambient
#print axioms KroneckerManuscriptQuiverDefinitions.Graph.walk_lift_closed
#print axioms KroneckerManuscriptQuiverDefinitions.Graph.maximal_iff_component
#print axioms KroneckerManuscriptQuiverDefinitions.Graph.ctdComp_iff_maximal
