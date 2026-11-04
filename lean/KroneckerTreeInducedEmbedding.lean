import KroneckerColoredTreeLift

set_option autoImplicit false
namespace KroneckerTreeInducedEmbedding
open SimpleGraph KroneckerReducedColorWords KroneckerGraphColorWords
open KroneckerColorWordCover KroneckerColoredTreeLift

theorem connected_hom_into_tree_induced {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.Preconnected) (hH : H.IsTree) (f : G →g H) (hf : Function.Injective f)
    {u v : V} : H.Adj (f u) (f v) ↔ G.Adj u v := by
  constructor
  · intro h
    obtain ⟨p,hp⟩ := hG.exists_isPath u v
    have he : p.map f = .cons h .nil :=
      (hH.existsUnique_path (f u) (f v)).unique (hp.map hf)
        (Walk.IsPath.nil.cons (by simpa using h.ne))
    have hl := congrArg Walk.length he
    simp only [Walk.length_map, Walk.length_cons, Walk.length_nil, zero_add] at hl
    exact Walk.adj_of_length_eq_one hl
  · exact f.map_adj

noncomputable def treeEmbedding {V : Type*} {G : SimpleGraph V} (C : EdgeColoring G)
    (hT : G.IsTree) (r : V) : G ↪g cover where
  toFun := rootLift C hT r
  inj' := rootLift_injective C hT r
  map_rel_iff' := connected_hom_into_tree_induced hT.connected.preconnected cover_tree
    (rootLiftHom C hT r) (rootLift_injective C hT r)

end KroneckerTreeInducedEmbedding
