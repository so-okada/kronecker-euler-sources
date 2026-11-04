import KroneckerLeafDeletedSourceBranch

/- Original module: KroneckerRootedVertexDecomposition -/
section
set_option autoImplicit false
namespace KroneckerRootedVertexDecomposition
open SimpleGraph KroneckerTreeCutComponents KroneckerRootedEdgePartition
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} {G : SimpleGraph V}

def outgoingVertexMap (hT : G.IsTree) (r : V)
    (p : Σ v : G.neighborSet r,{x // cutSide G r v.1 x}) : {x : V // x≠r} :=
  ⟨p.2.1,by
    intro h
    have hx : cutSide G r p.1.1 p.2.1 := p.2.2
    rw [h] at hx
    exact tree_cut_excludes_source hT p.1.2 hx⟩

theorem outgoing_vertex_bijective (hT : G.IsTree) (r : V) :
    Function.Bijective (outgoingVertexMap hT r) := by
  constructor
  · rintro ⟨v,x⟩ ⟨w,y⟩ h
    have hxy : x.1=y.1 := congrArg Subtype.val h
    have hvw : v=w := Subtype.ext (branch_neighbor_unique hT v.2 w.2
      (hxy ▸ x.2) y.2)
    subst w
    have he : x=y := Subtype.ext hxy
    subst y
    rfl
  · intro x
    obtain ⟨v,hv,_⟩ := unique_outgoing_branch hT r x.2
    exact ⟨⟨v,⟨x.1,hv⟩⟩,rfl⟩

/-- This equivalence partitions actual vertices, with no formal branch grammar assumed. -/
noncomputable def outgoingVertexEquiv (hT : G.IsTree) (r : V) :
    (Σ v : G.neighborSet r,{x // cutSide G r v.1 x}) ≃ {x : V // x≠r} :=
  Equiv.ofBijective (outgoingVertexMap hT r) (outgoing_vertex_bijective hT r)



end KroneckerRootedVertexDecomposition
end

/- Original module: KroneckerIncomingSourceBranches -/
section
set_option autoImplicit false
namespace KroneckerIncomingSourceBranches
open SimpleGraph KroneckerBipartiteIncidence KroneckerFiniteColoredTables
open KroneckerColoredTableRestrictions KroneckerTreeCutComponents KroneckerRootedBranchTrees
open KroneckerLeafDeletedSourceBranch

variable {I J : Type} (T : ColoredTable I J)

def cutSource (u v : I ⊕ J) (i : I) : Prop := cutSide (incidenceGraph (Incidence T)) u v (.inl i)
def cutSink (u v : I ⊕ J) (j : J) : Prop := cutSide (incidenceGraph (Incidence T)) u v (.inr j)

def cutTable (u v : I ⊕ J) : ColoredTable {i // cutSource T u v i} {j // cutSink T u v j} :=
  restrictTable T (cutSource T u v) (cutSink T u v)

theorem cut_table_tree (hT : (incidenceGraph (Incidence T)).IsTree) {u v : I ⊕ J}
    (h : (incidenceGraph (Incidence T)).Adj u v) :
    (incidenceGraph (Incidence (cutTable T u v))).IsTree := by
  apply (restrictionGraphIso T (cutSource T u v) (cutSink T u v)).isTree_iff.mpr
  have he : {w | Sum.elim (cutSource T u v) (cutSink T u v) w}=
      {w | cutSide (incidenceGraph (Incidence T)) u v w} := by
    ext w
    cases w <;> rfl
  rw [he]
  exact outgoing_branch_is_tree hT h

def sourceCutRoot (i : I) (j : J) : {k // cutSource T (.inr j) (.inl i) k} :=
  ⟨i,cut_side_contains_target _ _ _⟩

/-- Cutting an incoming edge produces a genuine source branch whenever its sources were saturated. -/
theorem incoming_source_is_branch (hT : (incidenceGraph (Incidence T)).IsTree)
    {i : I} {j : J} {d : Fin 3} (hij : T.code i j=some d)
    (hfull : ∀ k,cutSource T (.inr j) (.inl i) k → ∀ e,∃ l,T.code k l=some e) :
    IsSourceBranch (cutTable T (.inr j) (.inl i)) (sourceCutRoot T i j) d := by
  have hadj : (incidenceGraph (Incidence T)).Adj (.inr j) (.inl i) := ⟨d,hij⟩
  refine ⟨cut_table_tree T hT hadj,?_⟩
  intro k e
  constructor
  · rintro ⟨l,hl⟩
    change T.code k.val l.val = some e at hl
    by_contra hn
    push Not at hn
    have hk : k.1=i := congrArg Subtype.val hn.1
    have he : l.1=j := T.atSource i l.1 j d (by simpa only [←hk,←hn.2] using hl) hij
    have hc : cutSide (incidenceGraph (Incidence T)) (.inr j) (.inl i) (.inr l.1) := l.2
    rw [he] at hc
    exact tree_cut_excludes_source hT hadj hc
  · intro hn
    obtain ⟨l,hl⟩ := hfull k.1 k.2 e
    have hmem : cutSink T (.inr j) (.inl i) l := by
      by_contra hout
      have he := crossing_is_removed_edge (G:=incidenceGraph (Incidence T))
        (.inr j) (.inl i) (w:=.inr l) (z:=.inl k.1) (show Incidence T k.1 l from ⟨e,hl⟩) hout k.2
      have hp : l=j ∧ k.1=i := by simpa [Sym2.eq_iff] using he
      have hc : e=d := Option.some.inj (hl.symm.trans (by rw [hp.1,hp.2]; exact hij))
      rcases hn with hn | hn
      · exact hn (Subtype.ext hp.2)
      · exact hn hc
    exact ⟨⟨l,hmem⟩,hl⟩

end KroneckerIncomingSourceBranches
end
