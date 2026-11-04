import KroneckerManuscriptNotation
noncomputable section
open Classical
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions
namespace Quiver
abbrev Arrow (Q : Quiver) := Q.Edge
/-- A distinct copy of the arrow type for undirected edges. -/
structure UndirectedEdge (Q : Quiver) where
  arrow : Q.Arrow
def UnderG (Q : Quiver) : Graph where
  Vert := Q.Vert
  Edge := UndirectedEdge Q
  boundary e := s(Q.source e.arrow, Q.target e.arrow)
def underGIso (Q : Quiver) : Q.UnderG.Iso Q.underlyingGraph where
  vertexEquiv := Equiv.refl _
  edgeEquiv := ⟨UndirectedEdge.arrow, UndirectedEdge.mk, fun _ => rfl, fun _ => rfl⟩
  map_boundary _ := rfl
@[reducible] def DelArrow (Q : Quiver) (a : Q.Arrow) : Quiver where
  Vert := Q.Vert
  Edge := {e : Q.Arrow // e ≠ a}
  delta e := Q.delta e.val
@[reducible] def AddArrow (Q : Quiver) (x v : Q.Vert) : Quiver where
  Vert := Q.Vert
  Edge := Option Q.Arrow
  delta := fun e => match e with | some a => Q.delta a | none => (x,v)
end Quiver
namespace ColoredQuiver
def ColArrow {C : Type} (Q : ColoredQuiver C) (v : Q.1.Vert) (d : C) : Set Q.1.Arrow :=
  {a | Q.1.target a = v ∧ Q.QCol a = d}
theorem vacant_iff {C : Type} (Q : ColoredQuiver C) (B : Q.1.Bipartition)
    (v : Q.1.Vert) (d : C) :
    (v,d) ∈ Q.ColVacSlot B ↔ v ∈ B.sinks ∧ Q.ColArrow v d = ∅ := by
  simp only [ColVacSlot, ColArrow, Set.mem_ofPred_eq, Set.eq_empty_iff_forall_notMem]
  simp only [not_and]
def DelArrow {C : Type} (Q : ColoredQuiver C) (a : Q.1.Arrow) : ColoredQuiver C :=
  ⟨Q.1.DelArrow a, fun e => Q.QCol e.val⟩
def AddArrow {C : Type} (Q : ColoredQuiver C) (x v : Q.1.Vert) (d : C) : ColoredQuiver C :=
  ⟨Q.1.AddArrow x v, fun e => match e with | some a => Q.QCol a | none => d⟩
@[simp] theorem added_color {C : Type} (Q : ColoredQuiver C) (x v : Q.1.Vert) (d : C) :
    (Q.AddArrow x v d).QCol none = d := rfl
@[simp] theorem added_mem {C : Type} (Q : ColoredQuiver C) (x v : Q.1.Vert) (d : C) :
    none ∈ (Q.AddArrow x v d).ColArrow v d := ⟨rfl,rfl⟩
end ColoredQuiver
namespace Representation
def DelArrow {Q : Quiver} (R : Representation Q) (a : Q.Arrow) : Representation (Q.DelArrow a) where
  Space := R.Space
  arrow e := R.arrow e.val
def AddArrow {Q : Quiver} (R : Representation Q) (x v : Q.Vert)
    (f : R.Space x →ₗ[ℂ] R.Space v) : Representation (Q.AddArrow x v) where
  Space := R.Space
  arrow e := match e with | some a => R.arrow a | none => f
@[simp] theorem added_map {Q : Quiver} (R : Representation Q) (x v : Q.Vert)
    (f : R.Space x →ₗ[ℂ] R.Space v) : (R.AddArrow x v f).arrow none = f := rfl
@[simp] theorem retained_map {Q : Quiver} (R : Representation Q) (x v : Q.Vert)
    (f : R.Space x →ₗ[ℂ] R.Space v) (a : Q.Arrow) :
    (R.AddArrow x v f).arrow (some a) = R.arrow a := rfl
end Representation

/-- Explicit inputs to gluing; the manuscript specializes the blocks to zero-sum representations. -/
structure GlueData (C : Type) where
  S : Graph.SourceTrivalentTree
  block : S.Sink → ColoredQuiver C
  representation : ∀ b, ColoredRepresentation (block b)
  bipartition : ∀ b, (block b).1.Bipartition
  vertex : ∀ e : {p : S.Source × S.Sink // S.incidence p.1 p.2}, (block e.val.2).1.Vert
  color : {p : S.Source × S.Sink // S.incidence p.1 p.2} → C
  vacant : ∀ e, (vertex e, color e) ∈ (block e.val.2).ColVacSlot (bipartition e.val.2)
  map : ∀ e, ℂ →ₗ[ℂ] (representation e.val.2).Space (vertex e)
  nonzero : ∀ e, map e ≠ 0
namespace GlueData
variable {C : Type}
abbrev NewArrow (D : GlueData C) := {p : D.S.Source × D.S.Sink // D.S.incidence p.1 p.2}
@[reducible] def quiver (D : GlueData C) : ColoredQuiver C :=
  ⟨{ Vert := D.S.Source ⊕ (Σ b, (D.block b).1.Vert)
     Edge := (Σ b, (D.block b).1.Arrow) ⊕ D.NewArrow
     delta := fun a => match a with
       | .inl ⟨b,a⟩ => (.inr ⟨b,(D.block b).1.source a⟩, .inr ⟨b,(D.block b).1.target a⟩)
       | .inr e => (.inl e.val.1, .inr ⟨e.val.2,D.vertex e⟩) },
    fun a => match a with | .inl ⟨b,a⟩ => (D.block b).QCol a | .inr e => D.color e⟩
@[reducible] def Space (D : GlueData C) : D.quiver.1.Vert → Type :=
  Sum.elim (fun _ => ℂ) (fun p => (D.representation p.1).Space p.2)
@[reducible] instance (D : GlueData C) (v : D.quiver.1.Vert) : AddCommGroup (D.Space v) :=
  match v with
  | .inl _ => inferInstanceAs (AddCommGroup ℂ)
  | .inr p => inferInstanceAs (AddCommGroup ((D.representation p.1).Space p.2))
@[reducible] instance (D : GlueData C) (v : D.quiver.1.Vert) : Module ℂ (D.Space v) :=
  match v with
  | .inl _ => inferInstanceAs (Module ℂ ℂ)
  | .inr p => inferInstanceAs (Module ℂ ((D.representation p.1).Space p.2))
instance (D : GlueData C) (v : D.quiver.1.Vert) : FiniteDimensional ℂ (D.Space v) :=
  match v with
  | .inl _ => inferInstanceAs (FiniteDimensional ℂ ℂ)
  | .inr p => inferInstanceAs (FiniteDimensional ℂ ((D.representation p.1).Space p.2))
def Glue (D : GlueData C) : ColoredRepresentation D.quiver where
  Space := D.Space
  arrow a := match a with | .inl ⟨b,a⟩ => (D.representation b).arrow a | .inr e => D.map e
@[simp] theorem block_map (D : GlueData C) (b : D.S.Sink) (a : (D.block b).1.Arrow) :
    D.Glue.arrow (.inl ⟨b,a⟩) = (D.representation b).arrow a := rfl
@[simp] theorem new_map (D : GlueData C) (e : D.NewArrow) :
    D.Glue.arrow (.inr e) = D.map e := rfl
theorem new_map_nonzero (D : GlueData C) (e : D.NewArrow) :
    D.Glue.arrow (.inr e) ≠ 0 := D.nonzero e
end GlueData
namespace Graph.ColoredSourceTrivalentTree
open KroneckerReflectionKernel
abbrev InternalSink (T : Graph.ColoredSourceTrivalentTree) :=
  {b : T.Sink // 2 ≤ Fintype.card {x // T.incidence x b}}
@[reducible] def Q (T : Graph.ColoredSourceTrivalentTree) : ColoredQuiver (Fin 3) :=
  ⟨{ Vert := T.InternalSink ⊕ T.Source
     Edge := {p : T.InternalSink × T.Source // T.incidence p.2 p.1.val}
     delta e := (.inl e.val.1, .inr e.val.2) },
   fun e => T.color ⟨(e.val.2,e.val.1.val),e.property⟩⟩
@[reducible] def ZSSpace (T : Graph.ColoredSourceTrivalentTree) : T.Q.1.Vert → Type :=
  Sum.elim (fun b => Kernel {x // T.incidence x b.val}) (fun _ => ℂ)
@[reducible] instance (T : Graph.ColoredSourceTrivalentTree) (v : T.Q.1.Vert) : AddCommGroup (T.ZSSpace v) :=
  match v with
  | .inl b => inferInstanceAs (AddCommGroup (Kernel {x // T.incidence x b.val}))
  | .inr _ => inferInstanceAs (AddCommGroup ℂ)
@[reducible] instance (T : Graph.ColoredSourceTrivalentTree) (v : T.Q.1.Vert) : Module ℂ (T.ZSSpace v) :=
  match v with
  | .inl b => inferInstanceAs (Module ℂ (Kernel {x // T.incidence x b.val}))
  | .inr _ => inferInstanceAs (Module ℂ ℂ)
instance (T : Graph.ColoredSourceTrivalentTree) (v : T.Q.1.Vert) : FiniteDimensional ℂ (T.ZSSpace v) :=
  match v with
  | .inl b => inferInstanceAs (FiniteDimensional ℂ (Kernel {x // T.incidence x b.val}))
  | .inr _ => inferInstanceAs (FiniteDimensional ℂ ℂ)
def ZS (T : Graph.ColoredSourceTrivalentTree) : ColoredRepresentation T.Q where
  Space := T.ZSSpace
  arrow e := projection (ι := {x // T.incidence x e.val.1.val}) ⟨e.val.2,e.property⟩
def bipartition (T : Graph.ColoredSourceTrivalentTree) : T.Q.1.Bipartition where
  sources := Set.range Sum.inl
  sinks := Set.range Sum.inr
  disjoint := Set.disjoint_left.mpr (by
    rintro v ⟨x,hx⟩ ⟨y,hy⟩
    cases hx.trans hy.symm)
  exhaustive := by ext v; cases v <;> simp
  source_mem e := ⟨e.val.1,rfl⟩
  target_mem e := ⟨e.val.2,rfl⟩
end Graph.ColoredSourceTrivalentTree

/-- Exactly the inputs of manuscript Definition 7.25, including the colored trees. -/
structure ZeroSumGlueData where
  S : Graph.SourceTrivalentTree
  T : S.Sink → Graph.ColoredSourceTrivalentTree
  vertex : ∀ e : {p : S.Source × S.Sink // S.incidence p.1 p.2}, (T e.val.2).Q.1.Vert
  color : {p : S.Source × S.Sink // S.incidence p.1 p.2} → Fin 3
  vacant : ∀ e, (vertex e,color e) ∈ (T e.val.2).Q.ColVacSlot (T e.val.2).bipartition
  map : ∀ e, ℂ →ₗ[ℂ] (T e.val.2).ZS.Space (vertex e)
  nonzero : ∀ e, map e ≠ 0
namespace ZeroSumGlueData
def toGlueData (D : ZeroSumGlueData) : GlueData (Fin 3) where
  S := D.S
  block b := (D.T b).Q
  representation b := (D.T b).ZS
  bipartition b := (D.T b).bipartition
  vertex := D.vertex
  color := D.color
  vacant := D.vacant
  map := D.map
  nonzero := D.nonzero
def Glue (D : ZeroSumGlueData) := D.toGlueData.Glue
@[simp] theorem block_map (D : ZeroSumGlueData) (b : D.S.Sink) (a : (D.T b).Q.1.Arrow) :
    D.Glue.arrow (.inl ⟨b,a⟩) = (D.T b).ZS.arrow a := rfl
@[simp] theorem new_map (D : ZeroSumGlueData) (e : D.toGlueData.NewArrow) :
    D.Glue.arrow (.inr e) = D.map e := rfl
end ZeroSumGlueData
end KroneckerManuscriptQuiverDefinitions
