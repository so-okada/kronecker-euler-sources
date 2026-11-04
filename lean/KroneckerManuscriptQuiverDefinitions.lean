import KroneckerFiniteSupportDeckRepresentationTransport
import KroneckerStablePositiveSupportConnected
import KroneckerManuscriptGraphDefinitions
import KroneckerProperBipartiteQuiver
import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Finite

/-! Definitions 7.2--7.8 of the recovered manuscript. The graph endpoint map
retains loops and parallel edges. A colored quiver is a pair consisting of an
uncolored quiver and an arrow-color map. Conversion maps connect these objects
to the typed-quiver and coordinate-representation models used in the proofs. -/

set_option autoImplicit false
noncomputable section
namespace KroneckerManuscriptQuiverDefinitions

open KroneckerAbelianCover
open KroneckerFiniteSupportDeckRepresentationTransport

structure Graph where
  Vert : Type
  Edge : Type
  boundary : Edge → Sym2 Vert

namespace Graph

def IsSimple (G : Graph) : Prop :=
  (∀ e v, G.boundary e ≠ s(v, v)) ∧ Function.Injective G.boundary

structure Iso (G H : Graph) where
  vertexEquiv : G.Vert ≃ H.Vert
  edgeEquiv : G.Edge ≃ H.Edge
  map_boundary : ∀ e, H.boundary (edgeEquiv e) = Sym2.map vertexEquiv (G.boundary e)

def degree (G : Graph) (v : G.Vert) : Cardinal :=
  Cardinal.mk {e : G.Edge // ∃ u, u ≠ v ∧ G.boundary e = s(v, u)} +
    2 * Cardinal.mk {e : G.Edge // G.boundary e = s(v, v)}

def Leaf (G : Graph) (v : G.Vert) : Prop := G.degree v = 1

def simpleGraph (G : Graph) (h : G.IsSimple) : SimpleGraph G.Vert where
  Adj u v := ∃ e, G.boundary e = s(u, v)
  symm := by
    constructor
    rintro u v ⟨e, he⟩
    exact ⟨e, he.trans Sym2.eq_swap⟩
  loopless := by
    constructor
    rintro v ⟨e, he⟩
    exact h.1 e v he

def IsTree (G : Graph) : Prop := ∃ h : G.IsSimple, (G.simpleGraph h).IsTree

structure Bipartition (G : Graph) where
  sources : Set G.Vert
  sinks : Set G.Vert
  disjoint : Disjoint sources sinks
  exhaustive : sources ∪ sinks = Set.univ
  endpoints : ∀ e, ∃ u ∈ sources, ∃ v ∈ sinks, G.boundary e = s(u, v)

def IsBipartite (G : Graph) : Prop := Nonempty G.Bipartition

theorem iso_endpoints {G H : Graph} (f : G.Iso H) (e : G.Edge)
    (u v : G.Vert) (h : G.boundary e = s(u, v)) :
    H.boundary (f.edgeEquiv e) = s(f.vertexEquiv u, f.vertexEquiv v) := by
  rw [f.map_boundary, h]
  rfl

@[reducible] def ofSimpleGraph {V : Type} (G : SimpleGraph V) : Graph where
  Vert := V
  Edge := G.edgeSet
  boundary := Subtype.val

theorem ofSimpleGraph_simple {V : Type} (G : SimpleGraph V) :
    (ofSimpleGraph G).IsSimple := by
  refine ⟨?_, Subtype.val_injective⟩
  intro e v he
  have hv : s(v, v) ∈ G.edgeSet := he ▸ e.property
  exact G.loopless.irrefl v (G.mem_edgeSet.mp hv)

@[simp] theorem simpleGraph_ofSimpleGraph {V : Type} (G : SimpleGraph V) :
    (ofSimpleGraph G).simpleGraph (ofSimpleGraph_simple G) = G := by
  ext u v
  change (∃ e : G.edgeSet, e.val = s(u, v)) ↔ G.Adj u v
  simp

end Graph

structure Quiver where
  Vert : Type
  Edge : Type
  delta : Edge → Vert × Vert

namespace Quiver

def source (Q : Quiver) (e : Q.Edge) : Q.Vert := (Q.delta e).1
def target (Q : Quiver) (e : Q.Edge) : Q.Vert := (Q.delta e).2

@[simp] theorem delta_eq (Q : Quiver) (e : Q.Edge) :
    Q.delta e = (Q.source e, Q.target e) := rfl

def underlyingGraph (Q : Quiver) : Graph where
  Vert := Q.Vert
  Edge := Q.Edge
  boundary e := Sym2.mk (Q.delta e).1 (Q.delta e).2

@[simp] theorem underlying_endpoints (Q : Quiver) (e : Q.Edge) :
    Q.underlyingGraph.boundary e = s(Q.source e, Q.target e) := rfl

def degree (Q : Quiver) (v : Q.Vert) : Cardinal := Q.underlyingGraph.degree v

@[reducible] def toTyped (Q : Quiver) : TypedQuiver where
  V := Q.Vert
  A := Q.Edge
  source := Q.source
  target := Q.target

def ofTyped (Q : TypedQuiver) : Quiver where
  Vert := Q.V
  Edge := Q.A
  delta e := (Q.source e, Q.target e)

@[simp] theorem ofTyped_toTyped (Q : Quiver) : ofTyped Q.toTyped = Q := by
  cases Q
  rfl

@[simp] theorem toTyped_ofTyped (Q : TypedQuiver) : (ofTyped Q).toTyped = Q := by
  cases Q
  rfl

def typedEquiv : Quiver ≃ TypedQuiver where
  toFun := toTyped
  invFun := ofTyped
  left_inv := ofTyped_toTyped
  right_inv := toTyped_ofTyped

abbrev Iso (Q R : Quiver) := TypedQuiverIso Q.toTyped R.toTyped

def Iso.refl (Q : Quiver) : Q.Iso Q where
  vertexEquiv := Equiv.refl _
  arrowEquiv := Equiv.refl _
  map_source _ := rfl
  map_target _ := rfl

def Iso.trans {Q R S : Quiver} (f : Q.Iso R) (g : R.Iso S) : Q.Iso S where
  vertexEquiv := f.vertexEquiv.trans g.vertexEquiv
  arrowEquiv := f.arrowEquiv.trans g.arrowEquiv
  map_source a := by
    exact (g.map_source (f.arrowEquiv a)).trans
      (congrArg g.vertexEquiv (f.map_source a))
  map_target a := by
    exact (g.map_target (f.arrowEquiv a)).trans
      (congrArg g.vertexEquiv (f.map_target a))

theorem Iso.map_delta {Q R : Quiver} (f : Q.Iso R) (e : Q.Edge) :
    R.delta (f.arrowEquiv e) = (f.vertexEquiv (Q.source e), f.vertexEquiv (Q.target e)) :=
  Prod.ext (f.map_source e) (f.map_target e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def Iso.graphIso {Q R : Quiver} (f : Q.Iso R) : Q.underlyingGraph.Iso R.underlyingGraph where
  vertexEquiv := f.vertexEquiv
  edgeEquiv := f.arrowEquiv
  map_boundary e := by
    change Sym2.mk (R.delta (f.arrowEquiv e)).1 (R.delta (f.arrowEquiv e)).2 = s(f.vertexEquiv (Q.source e), f.vertexEquiv (Q.target e))
    rw [f.map_delta]

structure Bipartition (Q : Quiver) where
  sources : Set Q.Vert
  sinks : Set Q.Vert
  disjoint : Disjoint sources sinks
  exhaustive : sources ∪ sinks = Set.univ
  source_mem : ∀ e, Q.source e ∈ sources
  target_mem : ∀ e, Q.target e ∈ sinks

def IsBipartite (Q : Quiver) : Prop := Nonempty Q.Bipartition

theorem Bipartition.endpoints_ne {Q : Quiver} (B : Q.Bipartition) (e : Q.Edge) :
    Q.source e ≠ Q.target e := by
  intro h
  exact Set.disjoint_left.mp B.disjoint (B.source_mem e) (h ▸ B.target_mem e)

def Bipartition.underlying {Q : Quiver} (B : Q.Bipartition) :
    Q.underlyingGraph.Bipartition where
  sources := B.sources
  sinks := B.sinks
  disjoint := B.disjoint
  exhaustive := B.exhaustive
  endpoints e := ⟨Q.source e, B.source_mem e, Q.target e, B.target_mem e, rfl⟩

theorem Bipartition.underlying_simple {Q : Quiver} (B : Q.Bipartition)
    (h : Function.Injective Q.delta) : Q.underlyingGraph.IsSimple := by
  constructor
  · intro e v he
    rcases Sym2.eq_iff.mp he with hv | hv
    · exact B.endpoints_ne e (hv.1.trans hv.2.symm)
    · exact B.endpoints_ne e (hv.1.trans hv.2.symm)
  · intro e f hef
    rcases Sym2.eq_iff.mp hef with heq | hswap
    · exact h (Prod.ext heq.1 heq.2)
    · exfalso
      have hs : Q.source e = Q.target f := hswap.1
      have ht : Q.source e ∈ B.sinks := by simpa only [hs] using B.target_mem f
      exact Set.disjoint_left.mp B.disjoint (B.source_mem e) ht

def Bipartition.Iso {Q R : Quiver} (B : Q.Bipartition) (D : R.Bipartition)
    (f : Q.Iso R) : Prop :=
  (∀ v, f.vertexEquiv v ∈ D.sources ↔ v ∈ B.sources) ∧
    (∀ v, f.vertexEquiv v ∈ D.sinks ↔ v ∈ B.sinks)

def fullSubquiver (Q : Quiver) (U : Set Q.Vert) : Quiver where
  Vert := U
  Edge := {e : Q.Edge // Q.source e ∈ U ∧ Q.target e ∈ U}
  delta e := (⟨Q.source e.val, e.property.1⟩, ⟨Q.target e.val, e.property.2⟩)

end Quiver

def ColoredQuiver (C : Type) := Σ Q : Quiver, Q.Edge → C

namespace ColoredQuiver

def QCol {C : Type} (Q : ColoredQuiver C) : Q.1.Edge → C := Q.2

def fullSubquiver {C : Type} (Q : ColoredQuiver C) (U : Set Q.1.Vert) : ColoredQuiver C :=
  ⟨Q.1.fullSubquiver U, fun e => Q.2 e.val⟩

structure Iso {C : Type} (Q R : ColoredQuiver C) where
  quiverIso : Q.1.Iso R.1
  preserves_color : ∀ e, R.QCol (quiverIso.arrowEquiv e) = Q.QCol e

def Iso.refl {C : Type} (Q : ColoredQuiver C) : Q.Iso Q where
  quiverIso := Quiver.Iso.refl _
  preserves_color _ := rfl

def Iso.symm {C : Type} {Q R : ColoredQuiver C} (f : Q.Iso R) : R.Iso Q where
  quiverIso := f.quiverIso.symm
  preserves_color e := by
    have h := (f.preserves_color (f.quiverIso.arrowEquiv.symm e)).symm
    rw [Equiv.apply_symm_apply] at h
    exact h

def Iso.trans {C : Type} {Q R S : ColoredQuiver C} (f : Q.Iso R) (g : R.Iso S) :
    Q.Iso S where
  quiverIso := Quiver.Iso.trans f.quiverIso g.quiverIso
  preserves_color e := (g.preserves_color (f.quiverIso.arrowEquiv e)).trans (f.preserves_color e)

def isoSetoid (C : Type) : Setoid (ColoredQuiver C) where
  r Q R := Nonempty (Q.Iso R)
  iseqv := ⟨fun Q => ⟨Iso.refl Q⟩,
    fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

def IsBipartite {C : Type} (Q : ColoredQuiver C) : Prop := Q.1.IsBipartite

@[simp] theorem fullSubquiver_color {C : Type} (Q : ColoredQuiver C)
    (U : Set Q.1.Vert) (e : (Q.1.fullSubquiver U).Edge) :
    (Q.fullSubquiver U).QCol e = Q.QCol e.val := rfl

def ofProperColoring {Q : TypedQuiver} (C : KroneckerProperBipartiteQuiver.Coloring Q) :
    ColoredQuiver KroneckerReducedColorWords.Color := ⟨Quiver.ofTyped Q, C.color⟩

def properBipartition {Q : TypedQuiver} (C : KroneckerProperBipartiteQuiver.Coloring Q) :
    (ofProperColoring C).1.Bipartition where
  sources := {v | C.side v = 0}
  sinks := {v | C.side v = 1}
  disjoint := Set.disjoint_left.mpr (by intro v h0 h1; dsimp at h0 h1; omega)
  exhaustive := by
    ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have h := C.side_lt v
    omega
  source_mem := C.source_side
  target_mem := C.target_side

@[simp] theorem ofProperColoring_color {Q : TypedQuiver}
    (C : KroneckerProperBipartiteQuiver.Coloring Q) (a : Q.A) :
    (ofProperColoring C).QCol a = C.color a := rfl

end ColoredQuiver

structure Representation (Q : Quiver) where
  Space : Q.Vert → Type
  [spaceAddCommGroup : ∀ v, AddCommGroup (Space v)]
  [spaceModule : ∀ v, Module ℂ (Space v)]
  [spaceFiniteDimensional : ∀ v, FiniteDimensional ℂ (Space v)]
  arrow : ∀ e, Space (Q.source e) →ₗ[ℂ] Space (Q.target e)

attribute [instance] Representation.spaceAddCommGroup Representation.spaceModule
attribute [instance] Representation.spaceFiniteDimensional

namespace Representation

def dimension {Q : Quiver} (R : Representation Q) (v : Q.Vert) : ℕ :=
  Module.finrank ℂ (R.Space v)

def support {Q : Quiver} (R : Representation Q) : Set Q.Vert :=
  {v | Nontrivial (R.Space v)}

theorem mem_support_iff_dimension_pos {Q : Quiver} (R : Representation Q) (v : Q.Vert) :
    v ∈ R.support ↔ 0 < R.dimension v := Module.finrank_pos_iff.symm

def supportQuiver {Q : Quiver} (R : Representation Q) : Quiver :=
  Q.fullSubquiver R.support

def restrictToSupport {Q : Quiver} (R : Representation Q) : Representation R.supportQuiver where
  Space v := R.Space v.val
  arrow e := R.arrow e.val

@[simp] theorem restrictToSupport_arrow {Q : Quiver} (R : Representation Q)
    (e : R.supportQuiver.Edge) : (R.restrictToSupport).arrow e = R.arrow e.val := rfl

def toRepresentationOn {Q : Quiver} (R : Representation Q) :
    KroneckerFiniteQuiverHom.RepresentationOn Q.source Q.target R.Space where
  arrow := R.arrow

def coordinates {Q : Quiver} (R : Representation Q) (v : Q.Vert) :
    R.Space v ≃ₗ[ℂ] KroneckerFiniteQuiverHom.Space (R.dimension v) :=
  (Module.finBasis ℂ (R.Space v)).equivFun

def toCoordinates {Q : Quiver} (R : Representation Q) :
    KroneckerFiniteQuiverHom.Representation Q.source Q.target R.dimension :=
  KroneckerFiniteQuiverHom.inCoordinates R.coordinates R.toRepresentationOn

theorem coordinate_arrow {Q : Quiver} (R : Representation Q) (e : Q.Edge)
    (x : R.Space (Q.source e)) :
    R.toCoordinates.arrow e (R.coordinates (Q.source e) x) =
      R.coordinates (Q.target e) (R.arrow e x) := by
  simp [toCoordinates, KroneckerFiniteQuiverHom.inCoordinates,
    toRepresentationOn, LinearMap.comp_apply]

def coordinateSubrepEquiv {Q : Quiver} (R : Representation Q) :
    KroneckerFiniteQuiverHom.SubrepOn R.toRepresentationOn ≃
      KroneckerFiniteQuiverHom.Subrep R.toCoordinates :=
  KroneckerFiniteQuiverHom.coordinateSubrepEquiv R.coordinates R.toRepresentationOn

def ofCoordinates {Q : Quiver} (d : Q.Vert → ℕ)
    (R : KroneckerFiniteQuiverHom.Representation Q.source Q.target d) : Representation Q where
  Space v := KroneckerFiniteQuiverHom.Space (d v)
  arrow := R.arrow

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem ofCoordinates_dimension {Q : Quiver} (d : Q.Vert → ℕ)
    (R : KroneckerFiniteQuiverHom.Representation Q.source Q.target d) (v : Q.Vert) :
    (ofCoordinates d R).dimension v = d v := by
  simp [dimension, ofCoordinates, KroneckerFiniteQuiverHom.Space]

def spaceCast {Q : Quiver} (R : Representation Q) {u v : Q.Vert} (h : u = v) :
    R.Space u ≃ₗ[ℂ] R.Space v := by
  subst v
  exact LinearEquiv.refl ℂ _

def arrowOver {Q T : Quiver} (R : Representation T) (f : Q.Iso T) (e : Q.Edge) :
    R.Space (f.vertexEquiv (Q.source e)) →ₗ[ℂ] R.Space (f.vertexEquiv (Q.target e)) :=
  (R.spaceCast (f.map_target e)).toLinearMap.comp
    ((R.arrow (f.arrowEquiv e)).comp (R.spaceCast (f.map_source e)).symm.toLinearMap)

structure Iso {Q T : Quiver} (R : Representation Q) (S : Representation T)
    (f : Q.Iso T) where
  vertexIso : ∀ v, R.Space v ≃ₗ[ℂ] S.Space (f.vertexEquiv v)
  commutes : ∀ e, (vertexIso (Q.target e)).toLinearMap.comp (R.arrow e) =
    (S.arrowOver f e).comp (vertexIso (Q.source e)).toLinearMap

def Iso.refl {Q : Quiver} (R : Representation Q) : Iso R R (Quiver.Iso.refl Q) where
  vertexIso v := LinearEquiv.refl ℂ (R.Space v)
  commutes _ := rfl

def ofCoordinateIso {Q : Quiver} {d : Q.Vert → ℕ}
    {R S : KroneckerFiniteQuiverHom.Representation Q.source Q.target d}
    (f : KroneckerFiniteQuiverHom.Iso R S) :
    Iso (ofCoordinates d R) (ofCoordinates d S) (Quiver.Iso.refl Q) where
  vertexIso := f.map
  commutes e := by
    ext x
    exact f.commutes e x

end Representation

abbrev ColoredRepresentation {C : Type} (Q : ColoredQuiver C) := Representation Q.1

def ColoredRepresentation.supportQuiver {C : Type} {Q : ColoredQuiver C}
    (R : ColoredRepresentation Q) : ColoredQuiver C := Q.fullSubquiver R.support

structure ColoredRepresentationIso {C : Type} {Q T : ColoredQuiver C}
    (R : ColoredRepresentation Q) (S : ColoredRepresentation T) where
  coloredIso : Q.Iso T
  representationIso : R.Iso S coloredIso.quiverIso

end KroneckerManuscriptQuiverDefinitions
