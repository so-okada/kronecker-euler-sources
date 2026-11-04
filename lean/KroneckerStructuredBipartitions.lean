import KroneckerExplicitBipartitions

/-! Structured graph and colored-quiver inputs for the manuscript notation.
The fields reuse the checked bipartition structures. Subgraph vertex sets are
subtypes in Lean; the image statements identify them with ambient intersections. -/

noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions

structure StructuredGraph where
  graph : Graph
  bipartition : graph.Bipartition

namespace StructuredGraph

def ofParts (G : Graph) (I J : Set G.Vert) (h : G.IsBipartiteOn I J) : StructuredGraph :=
  ⟨G, h.toBipartition⟩

def sources (G : StructuredGraph) : Set G.graph.Vert := G.bipartition.sources
def sinks (G : StructuredGraph) : Set G.graph.Vert := G.bipartition.sinks

def srcAdj (G : StructuredGraph) (v : G.graph.Vert) : Set G.graph.Vert :=
  Graph.SrcAdj G.bipartition v
def snkAdj (G : StructuredGraph) (v : G.graph.Vert) : Set G.graph.Vert :=
  Graph.SnkAdj G.bipartition v

def subSrc (G : StructuredGraph) (H : G.graph.Subgraph) : Set G.graph.Vert :=
  G.sources ∩ H.vertices
def subSnk (G : StructuredGraph) (H : G.graph.Subgraph) : Set G.graph.Vert :=
  G.sinks ∩ H.vertices

def restrict (G : StructuredGraph) (H : G.graph.Subgraph) : StructuredGraph :=
  ⟨H.toGraph, G.bipartition.restrictSubgraph H⟩

@[simp] theorem ofParts_sources (G : Graph) (I J : Set G.Vert)
    (h : G.IsBipartiteOn I J) : (ofParts G I J h).sources = I := rfl
@[simp] theorem ofParts_sinks (G : Graph) (I J : Set G.Vert)
    (h : G.IsBipartiteOn I J) : (ofParts G I J h).sinks = J := rfl

theorem restrict_sources_image (G : StructuredGraph) (H : G.graph.Subgraph) :
    Subtype.val '' (G.restrict H).sources = G.subSrc H := by
  ext v
  constructor
  · rintro ⟨⟨v,hv⟩, hI, rfl⟩
    exact ⟨hI, hv⟩
  · rintro ⟨hI,hv⟩
    exact ⟨⟨v,hv⟩, hI, rfl⟩

theorem restrict_sinks_image (G : StructuredGraph) (H : G.graph.Subgraph) :
    Subtype.val '' (G.restrict H).sinks = G.subSnk H := by
  ext v
  constructor
  · rintro ⟨⟨v,hv⟩, hJ, rfl⟩
    exact ⟨hJ, hv⟩
  · rintro ⟨hJ,hv⟩
    exact ⟨⟨v,hv⟩, hJ, rfl⟩

end StructuredGraph

namespace Quiver

/-- Restriction allows arbitrary subquivers, including omitted arrows. -/
def Bipartition.restrictSubquiver {Q : Quiver} (B : Q.Bipartition)
    (H : Q.Subquiver) : H.toQuiver.Bipartition where
  sources := {v | v.val ∈ B.sources}
  sinks := {v | v.val ∈ B.sinks}
  disjoint := Set.disjoint_left.mpr (fun _ hu hv => Set.disjoint_left.mp B.disjoint hu hv)
  exhaustive := by
    ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have h : v.val ∈ B.sources ∪ B.sinks := B.exhaustive.symm ▸ Set.mem_univ v.val
    exact h
  source_mem e := B.source_mem e.val
  target_mem e := B.target_mem e.val

end Quiver

structure StructuredQuiver where
  quiver : Quiver
  bipartition : quiver.Bipartition

namespace StructuredQuiver

def underlyingGraph (Q : StructuredQuiver) : StructuredGraph :=
  ⟨Q.quiver.underlyingGraph, Q.bipartition.underlying⟩

end StructuredQuiver

structure StructuredColoredQuiver (C : Type) where
  colored : ColoredQuiver C
  bipartition : colored.1.Bipartition

namespace StructuredColoredQuiver

def underlyingQuiver {C : Type} (Q : StructuredColoredQuiver C) : StructuredQuiver :=
  ⟨Q.colored.1, Q.bipartition⟩

def underlyingGraph {C : Type} (Q : StructuredColoredQuiver C) : StructuredGraph :=
  ⟨Q.colored.1.underlyingGraph, Q.bipartition.underlying⟩

def colVacSlot {C : Type} (Q : StructuredColoredQuiver C) : Set (Q.colored.1.Vert × C) :=
  Q.colored.ColVacSlot Q.bipartition

def restrict {C : Type} (Q : StructuredColoredQuiver C)
    (H : Q.colored.1.Subquiver) : StructuredColoredQuiver C where
  colored := ⟨H.toQuiver, fun e => Q.colored.QCol e.val⟩
  bipartition := Q.bipartition.restrictSubquiver H

/-- The manuscript's structured colored quiver together with its representation. -/
def representation {C : Type} (Q : StructuredColoredQuiver C)
    (R : ColoredRepresentation Q.colored) : BipartiteColRep C :=
  ⟨Q.colored, Q.bipartition, R⟩

def cIsomClass {C : Type} (Q : StructuredColoredQuiver C)
    (R : ColoredRepresentation Q.colored) : Set (BipartiteColRep C) :=
  CIsomClass (Q.representation R)

def markedCIsom {C : Type} (Q : StructuredColoredQuiver C)
    (R : ColoredRepresentation Q.colored) {k : ℕ} (s : Fin k → Q.colored.1.Vert × C)
    (hs : ∀ j, s j ∈ Q.colVacSlot) : Set (MarkedObject C k) :=
  MarkedCIsom ⟨Q.representation R, s, hs⟩

/-- The reflected quiver and zero-sum representation retain the tree's coloring and partition. -/
def ofColoredTree (T : Graph.ColoredSourceTrivalentTree) : StructuredColoredQuiver (Fin 3) :=
  ⟨T.Q, T.bipartition⟩

def ofColoredTreeZeroSum (T : Graph.ColoredSourceTrivalentTree) : BipartiteColRep (Fin 3) :=
  (ofColoredTree T).representation T.ZS

@[simp] theorem underlyingGraph_sources {C : Type} (Q : StructuredColoredQuiver C) :
    Q.underlyingGraph.sources = Q.bipartition.sources := rfl
@[simp] theorem underlyingGraph_sinks {C : Type} (Q : StructuredColoredQuiver C) :
    Q.underlyingGraph.sinks = Q.bipartition.sinks := rfl
@[simp] theorem restrict_color {C : Type} (Q : StructuredColoredQuiver C)
    (H : Q.colored.1.Subquiver) (e : H.toQuiver.Edge) :
    (Q.restrict H).colored.QCol e = Q.colored.QCol e.val := rfl

end StructuredColoredQuiver
end KroneckerManuscriptQuiverDefinitions
