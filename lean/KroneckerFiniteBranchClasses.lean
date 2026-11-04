import KroneckerBranchIsomorphismInvariance
import KroneckerSourceBranchDegrees

section

/- Original module: KroneckerSinkBranchSizes -/
section
set_option autoImplicit false
namespace KroneckerSinkBranchSizes
open SimpleGraph KroneckerFiniteColoredTables KroneckerOutgoingSinkBranches
open KroneckerBipartiteIncidence KroneckerSaturatedTreeDimensions
attribute [local instance] Classical.propDecidable

variable {I J : Type} {T : ColoredTable I J} {r : J} {d : Fin 3}

theorem sink_branch_source_degrees [Fintype J] (h : IsSinkBranch T r d) (i : I) :
    Fintype.card {j // Incidence T i j}=3 := by
  have hs : Function.Surjective (fun j : {j // Incidence T i j} => (coloring T).color i j j.2) := by
    intro e
    obtain ⟨j,hj⟩ := h.2.1 i e
    exact ⟨⟨j,⟨e,hj⟩⟩,Option.some.inj ((code_color T i j ⟨e,hj⟩).symm.trans hj)⟩
  exact (Fintype.card_congr (Equiv.ofBijective _ ⟨(coloring T).at_source i,hs⟩)).trans
    (Fintype.card_fin 3)

theorem sink_branch_sink_count [Fintype I] [Fintype J] (h : IsSinkBranch T r d) :
    Fintype.card J=2*Fintype.card I+1 :=
  saturated_tree_sink_count (Incidence T) h.1 (sink_branch_source_degrees h)




end KroneckerSinkBranchSizes
end

/- Original module: KroneckerFiniteBranchObjects -/
section
set_option autoImplicit false
namespace KroneckerFiniteBranchObjects
open KroneckerFiniteColoredTables KroneckerLeafDeletedSourceBranch KroneckerOutgoingSinkBranches
open KroneckerSourceBranchDegrees KroneckerSinkBranchSizes
attribute [local instance] Classical.propDecidable

/-- Representatives are actual properly colored incidence tables with a distinguished root. -/
def SourceObject (I J : Type) (d : Fin 3) :=
  {p : ColoredTable I J × I // IsSourceBranch p.1 p.2 d}
def SinkObject (I J : Type) (d : Fin 3) :=
  {p : ColoredTable I J × J // IsSinkBranch p.1 p.2 d}

noncomputable instance {I J : Type} [Fintype I] [Fintype J] (d : Fin 3) :
    Fintype (SourceObject I J d) := inferInstanceAs (Fintype (Subtype _))
noncomputable instance {I J : Type} [Fintype I] [Fintype J] (d : Fin 3) :
    Fintype (SinkObject I J d) := inferInstanceAs (Fintype (Subtype _))

theorem source_object_dimensions {I J : Type} [Fintype I] [Fintype J]
    {d : Fin 3} (T : SourceObject I J d) : Fintype.card J=2*Fintype.card I :=
  source_branch_sink_count T.2

theorem sink_object_dimensions {I J : Type} [Fintype I] [Fintype J]
    {d : Fin 3} (T : SinkObject I J d) : Fintype.card J=2*Fintype.card I+1 :=
  sink_branch_sink_count T.2




end KroneckerFiniteBranchObjects
end
end

section

/- Original module: KroneckerBranchClassRelations -/
section
set_option autoImplicit false
namespace KroneckerBranchClassRelations
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerColoredIncidenceIso

variable {I J : Type} (d : Fin 3)

def SourceRel (T U : SourceObject I J d) : Prop :=
  ∃ e : ColoredIso (coloring T.1.1) (coloring U.1.1),e.source T.1.2=U.1.2
def SinkRel (T U : SinkObject I J d) : Prop :=
  ∃ e : ColoredIso (coloring T.1.1) (coloring U.1.1),e.sink T.1.2=U.1.2

theorem source_rel_equivalence : Equivalence (SourceRel (I:=I) (J:=J) d) := by
  constructor
  · intro T; exact ⟨1,rfl⟩
  · rintro T U ⟨e,he⟩
    exact ⟨e.symm,by change e.source.symm U.1.2=T.1.2; rw [←he,Equiv.symm_apply_apply]⟩
  · rintro T U V ⟨e,he⟩ ⟨f,hf⟩
    exact ⟨e.trans f,by change f.source (e.source T.1.2)=V.1.2; rw [he,hf]⟩

theorem sink_rel_equivalence : Equivalence (SinkRel (I:=I) (J:=J) d) := by
  constructor
  · intro T; exact ⟨1,rfl⟩
  · rintro T U ⟨e,he⟩
    exact ⟨e.symm,by change e.sink.symm U.1.2=T.1.2; rw [←he,Equiv.symm_apply_apply]⟩
  · rintro T U V ⟨e,he⟩ ⟨f,hf⟩
    exact ⟨e.trans f,by change f.sink (e.sink T.1.2)=V.1.2; rw [he,hf]⟩

def sourceSetoid (I J : Type) (d : Fin 3) : Setoid (SourceObject I J d) :=
  ⟨SourceRel d,source_rel_equivalence d⟩
def sinkSetoid (I J : Type) (d : Fin 3) : Setoid (SinkObject I J d) :=
  ⟨SinkRel d,sink_rel_equivalence d⟩

abbrev SourceClass (I J : Type) (d : Fin 3) := Quotient (sourceSetoid I J d)
abbrev SinkClass (I J : Type) (d : Fin 3) := Quotient (sinkSetoid I J d)

theorem source_class_eq_iff (T U : SourceObject I J d) :
    (Quotient.mk'' T : SourceClass I J d)=Quotient.mk'' U ↔ SourceRel d T U := Quotient.eq
theorem sink_class_eq_iff (T U : SinkObject I J d) :
    (Quotient.mk'' T : SinkClass I J d)=Quotient.mk'' U ↔ SinkRel d T U := Quotient.eq

end KroneckerBranchClassRelations
end

/- Original module: KroneckerFiniteBranchClasses -/
section
set_option autoImplicit false
namespace KroneckerFiniteBranchClasses
open KroneckerFiniteBranchObjects KroneckerBranchClassRelations
attribute [local instance] Classical.propDecidable

noncomputable instance {I J : Type} [Fintype I] [Fintype J] (d : Fin 3) :
    Fintype (SourceClass I J d) := Fintype.ofFinite _
noncomputable instance {I J : Type} [Fintype I] [Fintype J] (d : Fin 3) :
    Fintype (SinkClass I J d) := Fintype.ofFinite _

abbrev SourceDegreeClass (n : ℕ) (d : Fin 3) := SourceClass (Fin n) (Fin (2*n)) d
abbrev SinkDegreeClass (n : ℕ) (d : Fin 3) := SinkClass (Fin n) (Fin (2*n+1)) d



/-- Source-degree zero is absent from the actual source-branch class space. -/
theorem source_degree_zero (d : Fin 3) : Fintype.card (SourceDegreeClass 0 d)=0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun q => ?_⟩
  obtain ⟨S,rfl⟩ := Quotient.mk''_surjective q
  exact Fin.elim0 S.1.2

end KroneckerFiniteBranchClasses
end
end

