import KroneckerLeafCompletionInverse
import KroneckerFiniteBranchClasses
import KroneckerMarkedClassIsomorphisms

/- Original module: KroneckerLeafDeletionNaturality -/
section
set_option autoImplicit false
namespace KroneckerLeafDeletionNaturality
open KroneckerFiniteColoredTables KroneckerColoredTableRestrictions KroneckerTableIsomorphisms
open KroneckerColoredIncidenceIso KroneckerTableLeafMarks KroneckerLeafDeletedColors

variable {I J I' J' : Type} {T : ColoredTable I J} {U : ColoredTable I' J'}

/-- An isomorphism carrying the distinguished leaf restricts to the actual deleted tables. -/
noncomputable def deleteMarkedIso (e : ColoredIso (coloring T) (coloring U))
    {l : J} {l' : J'} (hl : e.sink l=l') :
    ColoredIso (coloring (restrictSinkTable T (fun j => j≠l)))
      (coloring (restrictSinkTable U (fun j => j≠l'))) := by
  let t : {j // j≠l} ≃ {j // j≠l'} := Equiv.subtypeEquiv e.sink (by
    intro j
    rw [←hl,e.sink.injective.ne_iff])
  apply isoOfCode _ _ e.source t
  intro i j
  exact iso_preserves_code T U e i j.1

/-- The root source obtained by leaf deletion is transported by the original isomorphism. -/
theorem leaf_owner_natural [Fintype I] [Fintype I']
    (e : ColoredIso (coloring T) (coloring U)) {l : J} {l' : J'} {d : Fin 3}
    (hl : LeafMark T d l) (hl' : LeafMark U d l') (he : e.sink l=l') :
    e.source (leafOwner T hl)=leafOwner U hl' := by
  apply (leaf_incidence_iff_owner U hl' _).mp
  refine ⟨d,?_⟩
  rw [←he]
  exact (iso_preserves_code T U e _ l).trans (leaf_owner_code T hl)


end KroneckerLeafDeletionNaturality
end

/- Original module: KroneckerBranchCompletionIsomorphisms -/
section
set_option autoImplicit false
namespace KroneckerBranchCompletionIsomorphisms
open KroneckerFiniteColoredTables KroneckerColoredIncidenceIso KroneckerTableIsomorphisms
open KroneckerLeafDeletedSourceBranch KroneckerColoredLeafExtension KroneckerSourceBranchCompletion
open KroneckerLeafCompletionInverse KroneckerLeafDeletionNaturality KroneckerUnrootedColoredRigidity
attribute [local instance] Classical.propDecidable

variable {I J I' J' : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
variable {T : ColoredTable I J} {U : ColoredTable I' J'} {r : I} {s : I'} {d : Fin 3}

noncomputable def extendBranchIso (h : IsSourceBranch T r d) (h' : IsSourceBranch U s d)
    (e : ColoredIso (coloring T) (coloring U)) (hr : e.source r=s) :
    ColoredIso (coloring (completeBranch T r d h).1) (coloring (completeBranch U s d h').1) := by
  apply isoOfCode _ _ e.source e.sink.optionCongr
  intro i j
  cases j with
  | none =>
    change (if e.source i=s then some d else none)=(if i=r then some d else none)
    have he : e.source i=s ↔ i=r := by rw [←hr,e.source.injective.eq_iff]
    simp only [he]
  | some j => exact iso_preserves_code T U e i j

/-- Completion identifies branch-root isomorphisms with marked-parent isomorphisms. -/
theorem completed_marked_iso_iff (h : IsSourceBranch T r d) (h' : IsSourceBranch U s d) :
    (∃ e : ColoredIso (coloring (completeBranch T r d h).1)
      (coloring (completeBranch U s d h').1),e.sink none=none) ↔
    ∃ e : ColoredIso (coloring T) (coloring U),e.source r=s := by
  constructor
  · rintro ⟨e,he⟩
    let f := (deleteCompletedIso T r d h).symm.trans
      ((deleteMarkedIso e he).trans (deleteCompletedIso U s d h'))
    refine ⟨f,?_⟩
    have hr := leaf_owner_natural e (completed_parent_leaf T r d h)
      (completed_parent_leaf U s d h') he
    rw [completed_parent_owner,completed_parent_owner] at hr
    exact hr
  · rintro ⟨e,he⟩
    exact ⟨extendBranchIso h h' e he,rfl⟩

noncomputable def completionIsoMap (h : IsSourceBranch T r d) (h' : IsSourceBranch U s d) :
    {e : ColoredIso (coloring T) (coloring U) // e.source r=s} →
      {e : ColoredIso (coloring (completeBranch T r d h).1)
        (coloring (completeBranch U s d h').1) // e.sink none=none} :=
  fun e => ⟨extendBranchIso h h' e.1 e.2,rfl⟩

/-- The correspondence is bijective on the actual maps, not only on existence of maps. -/
theorem completion_iso_bijective (h : IsSourceBranch T r d) (h' : IsSourceBranch U s d) :
    Function.Bijective (completionIsoMap h h') := by
  constructor
  · intro e f _
    exact Subtype.ext (tree_iso_unique h.1 e.1 f.1)
  · intro e
    obtain ⟨f,hf⟩ := (completed_marked_iso_iff h h').mp ⟨e.1,e.2⟩
    refine ⟨⟨f,hf⟩,?_⟩
    exact Subtype.ext (tree_iso_unique (completeBranch T r d h).2.1 _ _)

noncomputable def completionIsoEquiv (h : IsSourceBranch T r d) (h' : IsSourceBranch U s d) :
    {e : ColoredIso (coloring T) (coloring U) // e.source r=s} ≃
      {e : ColoredIso (coloring (completeBranch T r d h).1)
        (coloring (completeBranch U s d h').1) // e.sink none=none} :=
  Equiv.ofBijective (completionIsoMap h h') (completion_iso_bijective h h')

end KroneckerBranchCompletionIsomorphisms
end

/- Original module: KroneckerSourceCompletionObjects -/
section
set_option autoImplicit false
namespace KroneckerSourceCompletionObjects
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerMarkedTableAction
open KroneckerSourceBranchCompletion KroneckerColoredIncidenceIso KroneckerBranchCompletionIsomorphisms

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

noncomputable def completeSourceObject (S : SourceObject I J d) : MarkedTable I (Option J) d :=
  ⟨(completeBranch S.1.1 S.1.2 d S.2,none),completed_parent_leaf S.1.1 S.1.2 d S.2⟩

/-- Completion respects and reflects exactly the pointed isomorphisms used in the branch quotient. -/
theorem completion_objects_iso_iff (S T : SourceObject I J d) :
    (∃ e : ColoredIso (coloring (completeSourceObject S).1.1.1)
      (coloring (completeSourceObject T).1.1.1),e.sink (completeSourceObject S).1.2=
        (completeSourceObject T).1.2) ↔
    ∃ e : ColoredIso (coloring S.1.1) (coloring T.1.1),e.source S.1.2=T.1.2 :=
  completed_marked_iso_iff S.2 T.2

end KroneckerSourceCompletionObjects
end
