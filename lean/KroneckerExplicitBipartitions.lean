import KroneckerManuscriptPriorityDefinitions
import KroneckerManuscriptDimensions

/-! An ordered pair is an explicit argument; no graph is assigned a canonical
bipartition. These predicates identify the revised manuscript definitions with
the existing structured partitions used by the proofs. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptQuiverDefinitions
namespace Graph

def IsBipartiteOn (G : Graph) (I J : Set G.Vert) : Prop :=
  Disjoint I J ∧ I ∪ J = Set.univ ∧
    ∀ e, ∃ u ∈ I, ∃ v ∈ J, G.boundary e = s(u,v)

def IsBipartiteOn.toBipartition {G : Graph} {I J : Set G.Vert}
    (h : G.IsBipartiteOn I J) : G.Bipartition :=
  ⟨I,J,h.1,h.2.1,h.2.2⟩

theorem Bipartition.isBipartiteOn {G : Graph} (B : G.Bipartition) :
    G.IsBipartiteOn B.sources B.sinks := ⟨B.disjoint,B.exhaustive,B.endpoints⟩

theorem isBipartiteOn_iff (G : Graph) (I J : Set G.Vert) :
    G.IsBipartiteOn I J ↔ ∃ B : G.Bipartition, B.sources = I ∧ B.sinks = J := by
  constructor
  · intro h; exact ⟨h.toBipartition,rfl,rfl⟩
  · rintro ⟨B,rfl,rfl⟩; exact B.isBipartiteOn

theorem isBipartite_iff_exists_pair (G : Graph) :
    G.IsBipartite ↔ ∃ I J, G.IsBipartiteOn I J := by
  constructor
  · rintro ⟨B⟩; exact ⟨B.sources,B.sinks,B.isBipartiteOn⟩
  · rintro ⟨I,J,h⟩; exact ⟨h.toBipartition⟩

theorem IsBipartiteOn.swap {G : Graph} {I J : Set G.Vert}
    (h : G.IsBipartiteOn I J) : G.IsBipartiteOn J I := by
  refine ⟨h.1.symm, by simpa [Set.union_comm] using h.2.1, ?_⟩
  intro e
  obtain ⟨u,hu,v,hv,he⟩ := h.2.2 e
  exact ⟨v,hv,u,hu,he.trans Sym2.eq_swap⟩

def SrcAdjOn (G : Graph) (I _J : Set G.Vert) (v : G.Vert) : Set G.Vert :=
  G.AdjVert v ∩ I
def SnkAdjOn (G : Graph) (_I J : Set G.Vert) (v : G.Vert) : Set G.Vert :=
  G.AdjVert v ∩ J

@[simp] theorem srcAdjOn_eq {G : Graph} {I J : Set G.Vert}
    (h : G.IsBipartiteOn I J) (v : G.Vert) :
    G.SrcAdjOn I J v = SrcAdj h.toBipartition v := rfl
@[simp] theorem snkAdjOn_eq {G : Graph} {I J : Set G.Vert}
    (h : G.IsBipartiteOn I J) (v : G.Vert) :
    G.SnkAdjOn I J v = SnkAdj h.toBipartition v := rfl
@[simp] theorem srcAdjOn_swap (G : Graph) (I J : Set G.Vert) (v : G.Vert) :
    G.SrcAdjOn J I v = G.SnkAdjOn I J v := rfl

theorem Bipartition.eq_of_parts {G : Graph} (B C : G.Bipartition)
    (hI : B.sources = C.sources) (hJ : B.sinks = C.sinks) : B = C := by
  cases B; cases C; cases hI; cases hJ; rfl

theorem snkCtdComp_eq_of_parts {G : Graph} (B C : G.Bipartition)
    (hI : B.sources = C.sources) (hJ : B.sinks = C.sinks) (e : G.Edge) :
    G.SnkCtdComp B e = G.SnkCtdComp C e := by
  rw [B.eq_of_parts C hI hJ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def Bipartition.restrictSubgraph {G : Graph} (B : G.Bipartition)
    (H : G.Subgraph) : H.toGraph.Bipartition where
  sources := {v | v.val ∈ B.sources}
  sinks := {v | v.val ∈ B.sinks}
  disjoint := Set.disjoint_left.mpr (fun _ hu hv => Set.disjoint_left.mp B.disjoint hu hv)
  exhaustive := by
    ext v
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have h : v.val ∈ B.sources ∪ B.sinks := B.exhaustive.symm ▸ Set.mem_univ v.val
    exact h
  endpoints := by
    intro e
    obtain ⟨u,hu,v,hv,he⟩ := H.endpoints e.val e.property
    obtain ⟨a,ha,b,hb,hab⟩ := B.endpoints e.val
    rcases Sym2.eq_iff.mp (he.symm.trans hab) with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · refine ⟨⟨u,hu⟩,by simpa only [Set.mem_ofPred_eq, h1] using ha,⟨v,hv⟩,by simpa only [Set.mem_ofPred_eq, h2] using hb,?_⟩
      apply Sym2.map.injective Subtype.val_injective
      exact (H.map_boundary e).trans he
    · refine ⟨⟨v,hv⟩,by simpa only [Set.mem_ofPred_eq, h2] using ha,⟨u,hu⟩,by simpa only [Set.mem_ofPred_eq, h1] using hb,?_⟩
      apply Sym2.map.injective Subtype.val_injective
      exact (H.map_boundary e).trans (he.trans Sym2.eq_swap)

@[simp] theorem restricted_sources {G : Graph} (B : G.Bipartition)
    (H : G.Subgraph) : (B.restrictSubgraph H).sources = {v | v.val ∈ B.sources} := rfl
@[simp] theorem restricted_sinks {G : Graph} (B : G.Bipartition)
    (H : G.Subgraph) : (B.restrictSubgraph H).sinks = {v | v.val ∈ B.sinks} := rfl

end Graph
namespace Quiver

def IsBipartiteOn (Q : Quiver) (I J : Set Q.Vert) : Prop :=
  Disjoint I J ∧ I ∪ J = Set.univ ∧
    (∀ e, Q.source e ∈ I) ∧ (∀ e, Q.target e ∈ J)

def IsBipartiteOn.toBipartition {Q : Quiver} {I J : Set Q.Vert}
    (h : Q.IsBipartiteOn I J) : Q.Bipartition :=
  ⟨I,J,h.1,h.2.1,h.2.2.1,h.2.2.2⟩

theorem Bipartition.isBipartiteOn {Q : Quiver} (B : Q.Bipartition) :
    Q.IsBipartiteOn B.sources B.sinks :=
  ⟨B.disjoint,B.exhaustive,B.source_mem,B.target_mem⟩

theorem isBipartiteOn_iff (Q : Quiver) (I J : Set Q.Vert) :
    Q.IsBipartiteOn I J ↔ ∃ B : Q.Bipartition, B.sources = I ∧ B.sinks = J := by
  constructor
  · intro h; exact ⟨h.toBipartition,rfl,rfl⟩
  · rintro ⟨B,rfl,rfl⟩; exact B.isBipartiteOn

theorem isBipartite_iff_exists_pair (Q : Quiver) :
    Q.IsBipartite ↔ ∃ I J, Q.IsBipartiteOn I J := by
  constructor
  · rintro ⟨B⟩; exact ⟨B.sources,B.sinks,B.isBipartiteOn⟩
  · rintro ⟨I,J,h⟩; exact ⟨h.toBipartition⟩

theorem IsBipartiteOn.underlying {Q : Quiver} {I J : Set Q.Vert}
    (h : Q.IsBipartiteOn I J) : Q.underlyingGraph.IsBipartiteOn I J :=
  h.toBipartition.underlying.isBipartiteOn

def SrcAdjOn (Q : Quiver) (I _J : Set Q.Vert) (v : Q.Vert) : Set Q.Vert :=
  Q.AdjVert v ∩ I
def SnkAdjOn (Q : Quiver) (_I J : Set Q.Vert) (v : Q.Vert) : Set Q.Vert :=
  Q.AdjVert v ∩ J
@[simp] theorem srcAdjOn_eq {Q : Quiver} {I J : Set Q.Vert}
    (h : Q.IsBipartiteOn I J) (v : Q.Vert) :
    Q.SrcAdjOn I J v = SrcAdj h.toBipartition v := rfl
@[simp] theorem snkAdjOn_eq {Q : Quiver} {I J : Set Q.Vert}
    (h : Q.IsBipartiteOn I J) (v : Q.Vert) :
    Q.SnkAdjOn I J v = SnkAdj h.toBipartition v := rfl
theorem Bipartition.eq_of_parts {Q : Quiver} (B C : Q.Bipartition)
    (hI : B.sources = C.sources) (hJ : B.sinks = C.sinks) : B = C := by
  cases B; cases C; cases hI; cases hJ; rfl

def Bipartition.restrictVertices {Q : Quiver} (B : Q.Bipartition)
    (U : Set Q.Vert) : (Q.fullSubquiver U).Bipartition where
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
namespace ColoredQuiver
theorem colVacSlot_eq_of_parts {C : Type} (Q : ColoredQuiver C)
    (B D : Q.1.Bipartition) (hI : B.sources = D.sources) (hJ : B.sinks = D.sinks) :
    Q.ColVacSlot B = Q.ColVacSlot D := by rw [B.eq_of_parts D hI hJ]
end ColoredQuiver
namespace Representation
theorem srcDim_eq_of_parts {Q : Quiver} [Fintype Q.Vert] (R : Representation Q)
    (B D : Q.Bipartition) (hI : B.sources = D.sources) (hJ : B.sinks = D.sinks) :
    R.SrcDim B = R.SrcDim D := by rw [B.eq_of_parts D hI hJ]
theorem snkDim_eq_of_parts {Q : Quiver} [Fintype Q.Vert] (R : Representation Q)
    (B D : Q.Bipartition) (hI : B.sources = D.sources) (hJ : B.sinks = D.sinks) :
    R.SnkDim B = R.SnkDim D := by rw [B.eq_of_parts D hI hJ]
end Representation
end KroneckerManuscriptQuiverDefinitions
