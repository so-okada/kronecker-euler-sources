import KroneckerManuscriptArrowOperators
import KroneckerChainBlockNeighbors
noncomputable section
open Classical
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions

namespace Representation
abbrev RepSupp {Q : Quiver} (R : Representation Q) := R.support
end Representation

def VecSupp {V : Type} (d : V → ℕ) : Set V := {v | 0 < d v}
theorem repSupp_eq_vecSupp {Q : Quiver} (R : Representation Q) :
    R.RepSupp = VecSupp R.dimension := by
  ext v
  exact R.mem_support_iff_dimension_pos v

namespace Graph
def DelEdge (G : Graph) (e : G.Edge) : Graph where
  Vert := G.Vert
  Edge := {f : G.Edge // f ≠ e}
  boundary f := G.boundary f.val
/-- The component containing v, written CtdComp(G;v) in the manuscript. -/
abbrev CtdCompAt (G : Graph) (v : G.Vert) := G.connectedComponent v
/-- The set of connected components, written CtdComp(G). -/
def CtdComp (G : Graph) : Set Graph := Set.range G.CtdCompAt
theorem ctdCompAt_mem (G : Graph) (v : G.Vert) : G.CtdCompAt v ∈ G.CtdComp := ⟨v,rfl⟩
theorem ctdComp_eq_empty (G : Graph) [IsEmpty G.Vert] : G.CtdComp = ∅ := by
  ext H
  constructor
  · rintro ⟨v,_⟩; exact isEmptyElim v
  · intro h; exact False.elim h
private theorem sink_exists {G : Graph} (B : G.Bipartition) (e : G.Edge) :
    ∃ b ∈ B.sinks, ∃ x ∈ B.sources, G.boundary e = s(x,b) := by
  obtain ⟨x,hx,b,hb,he⟩ := B.endpoints e
  exact ⟨b,hb,x,hx,he⟩
def sinkEnd {G : Graph} (B : G.Bipartition) (e : G.Edge) : G.Vert :=
  Classical.choose (sink_exists B e)
def SnkCtdComp (G : Graph) (B : G.Bipartition) (e : G.Edge) : Graph :=
  (G.DelEdge e).CtdCompAt (sinkEnd (G := G) B e)
@[simp] theorem delete_boundary (G : Graph) (e : G.Edge) (f : (G.DelEdge e).Edge) :
    (G.DelEdge e).boundary f = G.boundary f.val := rfl
end Graph

namespace LabeledChain
open KroneckerChainIncidence
/-- Parameter n denotes c-1; source i denotes x_(i+1), axial block j denotes z_j,
and middle block i denotes y_(i+1). -/
def Ch (n : ℕ) : Graph := Graph.ofSimpleGraph (KroneckerBipartiteIncidence.incidenceGraph (incidence (n:=n)))
def LeftEdge {n : ℕ} (i : Connector n) : (Ch n).Edge :=
  ⟨s(Sum.inl i, Sum.inr (portBlock i 0)),
    (KroneckerBipartiteIncidence.incidenceGraph incidence).mem_edgeSet.mpr (port_incident i 0)⟩
def MidEdge {n : ℕ} (i : Connector n) : (Ch n).Edge :=
  ⟨s(Sum.inl i, Sum.inr (portBlock i 1)),
    (KroneckerBipartiteIncidence.incidenceGraph incidence).mem_edgeSet.mpr (port_incident i 1)⟩
def RightEdge {n : ℕ} (i : Connector n) : (Ch n).Edge :=
  ⟨s(Sum.inl i, Sum.inr (portBlock i 2)),
    (KroneckerBipartiteIncidence.incidenceGraph incidence).mem_edgeSet.mpr (port_incident i 2)⟩
theorem source_degree {n : ℕ} (i : Connector n) : Fintype.card {j // incidence i j} = 3 :=
  connector_degree i
end LabeledChain

namespace Quiver
structure Embedding (Q T : Quiver) extends Hom Q T where
  vertex_injective : Function.Injective vertex
  arrow_injective : Function.Injective edge

def sourceFiberMap {Q T : Quiver} (p : Hom Q T) (v : Q.Vert) :
    {a : Q.Arrow // Q.source a = v} → {a : T.Arrow // T.source a = p.vertex v} :=
  fun a => ⟨p.edge a.val, (p.map_source a.val).trans (congrArg p.vertex a.property)⟩
def targetFiberMap {Q T : Quiver} (p : Hom Q T) (v : Q.Vert) :
    {a : Q.Arrow // Q.target a = v} → {a : T.Arrow // T.target a = p.vertex v} :=
  fun a => ⟨p.edge a.val, (p.map_target a.val).trans (congrArg p.vertex a.property)⟩
structure Covering (Q T : Quiver) extends Hom Q T where
  surjective_vertices : Function.Surjective vertex
  source_bijective : ∀ v, Function.Bijective (sourceFiberMap toHom v)
  target_bijective : ∀ v, Function.Bijective (targetFiberMap toHom v)
def Covering.IsUniversal {Q T : Quiver} (_p : Covering Q T) : Prop := Q.underlyingGraph.IsTree
structure Deck {Q T : Quiver} (p : Hom Q T) where
  iso : Q.Iso Q
  vertex_over : ∀ v, p.vertex (iso.vertexEquiv v) = p.vertex v
  arrow_over : ∀ a, p.edge (iso.arrowEquiv a) = p.edge a

def DeckAction {Q T : Quiver} {p : Hom Q T} (δ : Deck p) (d : Q.Vert → ℕ) : Q.Vert → ℕ :=
  fun v => d (δ.iso.vertexEquiv.symm v)
def DeckClass {Q T : Quiver} (p : Hom Q T) (d : Q.Vert → ℕ) : Set (Q.Vert → ℕ) :=
  {e | ∃ δ : Deck p, e = DeckAction δ d}
@[simp] theorem deck_action_at_image {Q T : Quiver} {p : Hom Q T}
    (δ : Deck p) (d : Q.Vert → ℕ) (v : Q.Vert) :
    DeckAction δ d (δ.iso.vertexEquiv v) = d v := by simp [DeckAction]
theorem deck_action_support {Q T : Quiver} {p : Hom Q T}
    (δ : Deck p) (d : Q.Vert → ℕ) :
    VecSupp (DeckAction δ d) = δ.iso.vertexEquiv '' VecSupp d := by
  ext v
  constructor
  · intro hv
    exact ⟨δ.iso.vertexEquiv.symm v, hv, δ.iso.vertexEquiv.apply_symm_apply v⟩
  · rintro ⟨w, hw, rfl⟩
    simpa [VecSupp, DeckAction] using hw
theorem deck_action_finite_support {Q T : Quiver} {p : Hom Q T}
    (δ : Deck p) (d : Q.Vert → ℕ) (h : (VecSupp d).Finite) :
    (VecSupp (DeckAction δ d)).Finite := by
  rw [deck_action_support]
  exact h.image _
end Quiver

def DimVecFin (Q : Quiver) := {d : Q.Vert → ℕ // (VecSupp d).Finite}
def VecSrcDim {Q : Quiver} (B : Q.Bipartition) (d : DimVecFin Q) : ℕ :=
  ∑ v ∈ d.property.toFinset, if v ∈ B.sources then d.val v else 0
def VecSnkDim {Q : Quiver} (B : Q.Bipartition) (d : DimVecFin Q) : ℕ :=
  ∑ v ∈ d.property.toFinset, if v ∈ B.sinks then d.val v else 0
def CovDim {Q : Quiver} (B : Q.Bipartition) (a b : ℕ) : Set (DimVecFin Q) :=
  {d | VecSrcDim B d = a ∧ VecSnkDim B d = b}
def CoverWeight {Q : Quiver} (B : Q.Bipartition) (a b : ℕ) (e : DimVecFin Q) : ℤ :=
  (a : ℤ) * VecSnkDim B e - (b : ℤ) * VecSrcDim B e

theorem compatible_weight_zero {Q : Quiver} (B : Q.Bipartition) (a b : ℕ)
    (d : DimVecFin Q) (h : d ∈ CovDim B a b) : CoverWeight B a b d = 0 := by
  rcases h with ⟨hs,ht⟩
  simp [CoverWeight,hs,ht,mul_comm]
end KroneckerManuscriptQuiverDefinitions
