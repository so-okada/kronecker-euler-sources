import KroneckerSourceCompletionObjects
import KroneckerBranchObjectTransport

/- Original module: KroneckerCompletionClassInjection -/
section
set_option autoImplicit false
namespace KroneckerCompletionClassInjection
open KroneckerFiniteBranchObjects KroneckerBranchClassRelations KroneckerFiniteBranchClasses
open KroneckerSourceCompletionObjects KroneckerMarkedClassIsomorphisms KroneckerMarkedTreeClassCount

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

noncomputable def completeOnClasses : SourceClass I J d → MarkedClass I (Option J) d :=
  Quotient.lift (fun S => Quotient.mk'' (completeSourceObject S)) (by
    intro S T h
    exact (marked_class_eq_iff _ _).mpr ((completion_objects_iso_iff S T).mpr h))

/-- No automorphism or labeling multiplicity is lost by completion on actual classes. -/
theorem completion_classes_injective : Function.Injective (completeOnClasses (I:=I) (J:=J) (d:=d)) := by
  intro q q'
  induction q using Quotient.inductionOn with | _ S =>
    induction q' using Quotient.inductionOn with | _ T =>
      intro h
      apply Quotient.sound
      exact (completion_objects_iso_iff S T).mp ((marked_class_eq_iff _ _).mp h)

end KroneckerCompletionClassInjection
end

/- Original module: KroneckerLeafDeletionNormalForm -/
section
set_option autoImplicit false
namespace KroneckerLeafDeletionNormalForm
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerMarkedTableAction
open KroneckerColoredTableRestrictions KroneckerLeafDeletedColors KroneckerLeafDeletedSourceBranch
open KroneckerBranchObjectTransport KroneckerColoredTableTransport KroneckerSourceCompletionObjects
open KroneckerBranchCompletionIsomorphisms KroneckerLeafCompletionInverse KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

noncomputable def deleteMarkedObject (M : MarkedTable I J d) :
    SourceObject I {j : J // j≠M.1.2} d :=
  ⟨(restrictSinkTable M.1.1.1 (fun j => j≠M.1.2),leafOwner M.1.1.1 M.2),
    leaf_delete_is_source_branch M.1.1 M.2⟩

theorem deletion_option_sink_card (M : MarkedTable I (Option J) d) :
    Fintype.card {j : Option J // j≠M.1.2}=Fintype.card J := by simp

noncomputable def deletionSinkEquiv (M : MarkedTable I (Option J) d) :
    {j : Option J // j≠M.1.2} ≃ J := Fintype.equivOfCardEq (deletion_option_sink_card M)

noncomputable def normalizedDeletion (M : MarkedTable I (Option J) d) : SourceObject I J d :=
  transportSourceObject (deleteMarkedObject M) (Equiv.refl I) (deletionSinkEquiv M)

/-- Relabeling the deleted sink carrier does not weaken the exact reconstruction of the marked tree. -/
noncomputable def normalizedRestorationIso (M : MarkedTable I (Option J) d) :
    ColoredIso (coloring (completeSourceObject (normalizedDeletion M)).1.1.1) (coloring M.1.1.1) :=
  (extendBranchIso (normalizedDeletion M).2 (deleteMarkedObject M).2
    (transportIso (deleteMarkedObject M).1.1 (Equiv.refl I) (deletionSinkEquiv M)).symm rfl).trans
      (restoreMarkedLeafIso M.1.1 M.2)

theorem normalized_restoration_mark (M : MarkedTable I (Option J) d) :
    (normalizedRestorationIso M).sink (completeSourceObject (normalizedDeletion M)).1.2=M.1.2 := rfl

end KroneckerLeafDeletionNormalForm
end

/- Original module: KroneckerCompletionClassEquivalence -/
section
set_option autoImplicit false
namespace KroneckerCompletionClassEquivalence
open KroneckerFiniteBranchObjects KroneckerBranchClassRelations KroneckerFiniteBranchClasses
open KroneckerSourceCompletionObjects KroneckerMarkedClassIsomorphisms KroneckerMarkedTreeClassCount
open KroneckerCompletionClassInjection KroneckerLeafDeletionNormalForm
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

/-- Every actual marked tree class comes from deletion and completion of a source branch. -/
theorem completion_classes_surjective : Function.Surjective (completeOnClasses (I:=I) (J:=J) (d:=d)) := by
  intro q
  induction q using Quotient.inductionOn with | _ M =>
    refine ⟨Quotient.mk'' (normalizedDeletion M),?_⟩
    exact (marked_class_eq_iff _ _).mpr ⟨normalizedRestorationIso M,normalized_restoration_mark M⟩

noncomputable def completionClassEquiv : SourceClass I J d ≃ MarkedClass I (Option J) d :=
  Equiv.ofBijective completeOnClasses ⟨completion_classes_injective,completion_classes_surjective⟩


end KroneckerCompletionClassEquivalence
end
