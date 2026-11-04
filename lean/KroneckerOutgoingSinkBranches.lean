import KroneckerIncomingSourceBranches

set_option autoImplicit false
namespace KroneckerOutgoingSinkBranches
open SimpleGraph KroneckerBipartiteIncidence KroneckerFiniteColoredTables
open KroneckerTreeCutComponents KroneckerRootedBranchTrees KroneckerIncomingSourceBranches

variable {I J : Type}

/-- A sink branch has saturated sources and omits its prescribed parent color at its root. -/
def IsSinkBranch (T : ColoredTable I J) (r : J) (d : Fin 3) : Prop :=
  (incidenceGraph (Incidence T)).IsTree ∧
    (∀ i e,∃ j,T.code i j=some e) ∧ (∀ i,T.code i r≠some d)

def sinkCutRoot (T : ColoredTable I J) (i : I) (j : J) :
    {l // cutSink T (.inl i) (.inr j) l} := ⟨j,cut_side_contains_target _ _ _⟩

/-- The outgoing component at a sink is the actual sink-branch object of the manuscript. -/
theorem outgoing_sink_is_branch (T : ColoredTable I J)
    (hT : (incidenceGraph (Incidence T)).IsTree)
    {i : I} {j : J} {d : Fin 3} (hij : T.code i j=some d)
    (hfull : ∀ k,cutSource T (.inl i) (.inr j) k → ∀ e,∃ l,T.code k l=some e) :
    IsSinkBranch (cutTable T (.inl i) (.inr j)) (sinkCutRoot T i j) d := by
  have hadj : (incidenceGraph (Incidence T)).Adj (.inl i) (.inr j) := ⟨d,hij⟩
  refine ⟨cut_table_tree T hT hadj,?_,?_⟩
  · intro k e
    obtain ⟨l,hl⟩ := hfull k.1 k.2 e
    have hm : cutSink T (.inl i) (.inr j) l :=
      branch_closed_away_from_root k.2 (show Incidence T k.1 l from ⟨e,hl⟩) (by simp)
    exact ⟨⟨l,hm⟩,hl⟩
  · intro k hk
    have he : k.1=i := T.atSink k.1 i j d hk hij
    have hc : cutSide (incidenceGraph (Incidence T)) (.inl i) (.inr j) (.inl k.1) := k.2
    rw [he] at hc
    exact tree_cut_excludes_source hT hadj hc

end KroneckerOutgoingSinkBranches
