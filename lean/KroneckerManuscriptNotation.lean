import KroneckerManuscriptRevision

noncomputable section
open Classical
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions

namespace Graph
 def AdjVert (G : Graph) (v : G.Vert) : Set G.Vert :=
   {u | ∃ e, G.boundary e = s(v,u)}
 def SrcAdj {G : Graph} (B : G.Bipartition) (i : G.Vert) : Set G.Vert :=
   G.AdjVert i ∩ B.sources
 def SnkAdj {G : Graph} (B : G.Bipartition) (v : G.Vert) : Set G.Vert :=
   G.AdjVert v ∩ B.sinks
 def IncEdge (G : Graph) (v : G.Vert) : Set G.Edge :=
   {e | ∃ u, G.boundary e = s(v,u)}
 abbrev Flow (G : Graph) := G.Edge → ℝ
 def FlowSumEquations (G : Graph) [Fintype G.Edge] (B : G.Bipartition)
     (α ξ : G.Vert → ℝ) (f : G.Flow) : Prop :=
   (∀ v ∈ B.sources, ∑ e : G.Edge, (if e ∈ G.IncEdge v then f e else 0) = α v) ∧
   (∀ i ∈ B.sinks, ∑ e : G.Edge, (if e ∈ G.IncEdge i then f e else 0) = ξ i)
 def FlowWithSums (G : Graph) [Fintype G.Edge] (B : G.Bipartition)
     (α ξ : G.Vert → ℝ) : Set G.Flow := {f | G.FlowSumEquations B α ξ f}
end Graph
namespace Quiver
 def AdjVert (Q : Quiver) (v : Q.Vert) : Set Q.Vert := Q.underlyingGraph.AdjVert v
 def SrcAdj {Q : Quiver} (B : Q.Bipartition) (i : Q.Vert) : Set Q.Vert :=
   Q.AdjVert i ∩ B.sources
 def SnkAdj {Q : Quiver} (B : Q.Bipartition) (v : Q.Vert) : Set Q.Vert :=
   Q.AdjVert v ∩ B.sinks
 def IncEdgeQuiv (Q : Quiver) (v : Q.Vert) : Set Q.Edge :=
   {e | Q.source e = v ∨ Q.target e = v}
end Quiver
namespace ColoredQuiver
 def ColVacSlot {C : Type} (Q : ColoredQuiver C) (B : Q.1.Bipartition) :
     Set (Q.1.Vert × C) :=
   {p | p.1 ∈ B.sinks ∧ ∀ e, Q.1.target e = p.1 → Q.QCol e ≠ p.2}
end ColoredQuiver

/-- A bipartite colored representation; the bipartition is part of the data. -/
structure BipartiteColRep (C : Type) where
  quiver : ColoredQuiver C
  bipartition : quiver.1.Bipartition
  representation : ColoredRepresentation quiver

def CIsomClass {C : Type} (R : BipartiteColRep C) : Set (BipartiteColRep C) :=
  {S | ∃ f : ColoredRepresentationIso R.representation S.representation,
    R.bipartition.Iso S.bipartition f.coloredIso.quiverIso}

structure MarkedObject (C : Type) (k : ℕ) extends BipartiteColRep C where
  marking : Fin k → quiver.1.Vert × C
  vacant : ∀ j, marking j ∈ quiver.ColVacSlot bipartition

def MarkedCIsom {C : Type} {k : ℕ} (R : MarkedObject C k) : Set (MarkedObject C k) :=
  {S | ∃ f : ColoredRepresentationIso R.representation S.representation,
    R.bipartition.Iso S.bipartition f.coloredIso.quiverIso ∧
    ∀ j, (f.coloredIso.quiverIso.vertexEquiv (R.marking j).1, (R.marking j).2) = S.marking j}

/-- The fixed colored-quiver and fixed ordered marking category. -/
structure MarkedColRep {C : Type} (Q : ColoredQuiver C) (B : Q.1.Bipartition)
    {k : ℕ} (s : Fin k → Q.1.Vert × C)
    (hs : ∀ j, s j ∈ Q.ColVacSlot B) where
  representation : ColoredRepresentation Q
namespace MarkedColRep
variable {C : Type} {Q : ColoredQuiver C} {B : Q.1.Bipartition}
  {k : ℕ} {s : Fin k → Q.1.Vert × C} {hs : ∀ j, s j ∈ Q.ColVacSlot B}
structure Hom (R S : MarkedColRep Q B s hs) where
  map : ColoredRepresentationHom R.representation S.representation
  sources : ∀ v ∈ B.sources, map.coloredHom.quiverHom.vertex v ∈ B.sources
  sinks : ∀ v ∈ B.sinks, map.coloredHom.quiverHom.vertex v ∈ B.sinks
  fixes : ∀ j, map.coloredHom.quiverHom.vertex (s j).1 = (s j).1
 def Hom.id (R : MarkedColRep Q B s hs) : Hom R R :=
   ⟨ColoredRepresentationHom.id R.representation, fun _ h => h, fun _ h => h, fun _ => rfl⟩
 def Hom.comp {R S T : MarkedColRep Q B s hs} (g : Hom S T) (f : Hom R S) : Hom R T where
   map := g.map.comp f.map
   sources v h := g.sources _ (f.sources v h)
   sinks v h := g.sinks _ (f.sinks v h)
   fixes j := (congrArg g.map.coloredHom.quiverHom.vertex (f.fixes j)).trans (g.fixes j)
 @[ext] theorem Hom.ext {R S : MarkedColRep Q B s hs} {f g : Hom R S}
     (h : f.map = g.map) : f = g := by
   cases f; cases g; cases h; rfl
 instance category : CategoryTheory.Category (MarkedColRep Q B s hs) where
   Hom := Hom
   id := Hom.id
   comp f g := g.comp f
   id_comp f := by apply Hom.ext; exact ColoredRepresentationHom.comp_id f.map
   comp_id f := by apply Hom.ext; exact ColoredRepresentationHom.id_comp f.map
   assoc f g h := by apply Hom.ext; exact (ColoredRepresentationHom.comp_assoc h.map g.map f.map).symm
end MarkedColRep
end KroneckerManuscriptQuiverDefinitions
