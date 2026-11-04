import KroneckerManuscriptGraphHom

open KroneckerManuscriptQuiverDefinitions

example (G : Graph) [IsEmpty G.Vert] : G.Connected := G.connected_of_isEmpty
example (G : Graph) [IsEmpty G.Vert] : ¬ G.IsTree := by
  intro h
  obtain ⟨v⟩ := (G.tree_iff_connected_forest.mp h).1
  exact isEmptyElim v
example (G : Graph) (v : G.Vert) : Nonempty (G.connectedComponent v).Vert :=
  G.connectedComponent_nonempty v

#print axioms Graph.connected_of_isEmpty
#print axioms Graph.connected_iff_simple
#print axioms Graph.tree_iff_connected_forest
#print axioms Graph.connectedComponent_nonempty
#print axioms Graph.connected_iff_cutConnected
#print axioms Graph.Hom.edge_eq_of_vertex_eq
