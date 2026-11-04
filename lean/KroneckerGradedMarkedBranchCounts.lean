import KroneckerCompletionClassEquivalence
import KroneckerTreeLeafEnumerator

/- Original module: KroneckerMarkedCarrierTransport -/
section
set_option autoImplicit false
namespace KroneckerMarkedCarrierTransport
open KroneckerFiniteColoredTables KroneckerSaturatedTableAction KroneckerMarkedTableAction
open KroneckerMarkedTreeClassCount KroneckerMarkedClassIsomorphisms KroneckerColoredTableTransport
open KroneckerTableLeafMarks KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

variable {I J I' J' : Type} [Fintype I] [Fintype J] [Fintype I'] [Fintype J'] {d : Fin 3}

noncomputable def transportSaturated (T : SaturatedTable I J) (s : I ≃ I') (t : J ≃ J') :
    SaturatedTable I' J' :=
  ⟨transportTable T.1 s t,(transportIso T.1 s t).graphIso.isTree_iff.mp T.2.1,by
    intro i
    obtain ⟨i,rfl⟩ := s.surjective i
    exact ((transportIso T.1 s t).source_degree i).trans (T.2.2 i)⟩

noncomputable def transportMarked (M : MarkedTable I J d) (s : I ≃ I') (t : J ≃ J') :
    MarkedTable I' J' d :=
  ⟨(transportSaturated M.1.1 s t,t M.1.2),(leaf_mark_transport (transportIso M.1.1.1 s t) d M.1.2).mpr M.2⟩

theorem marked_transport_inverse (M : MarkedTable I J d) (s : I ≃ I') (t : J ≃ J') :
    transportMarked (transportMarked M s t) s.symm t.symm=M := by
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (transport_table_roundtrip M.1.1.1 s t)
  · exact t.symm_apply_apply M.1.2

theorem marked_transport_class_equal (s : I ≃ I') (t : J ≃ J') (M N : MarkedTable I J d)
    (h : (Quotient.mk'' M : MarkedClass I J d)=Quotient.mk'' N) :
    (Quotient.mk'' (transportMarked M s t) : MarkedClass I' J' d)=
      Quotient.mk'' (transportMarked N s t) := by
  obtain ⟨e,he⟩ := (marked_class_eq_iff M N).mp h
  apply (marked_class_eq_iff _ _).mpr
  refine ⟨(transportIso M.1.1.1 s t).symm.trans (e.trans (transportIso N.1.1.1 s t)),?_⟩
  change t (e.sink (t.symm (t M.1.2)))=t N.1.2
  rw [Equiv.symm_apply_apply,he]

noncomputable def transportMarkedClasses (s : I ≃ I') (t : J ≃ J') :
    MarkedClass I J d → MarkedClass I' J' d :=
  Quotient.lift (fun M => Quotient.mk'' (transportMarked M s t))
    (fun M N h => marked_transport_class_equal s t M N (Quotient.sound h))

theorem marked_class_transport_inverse (s : I ≃ I') (t : J ≃ J') (q : MarkedClass I J d) :
    transportMarkedClasses s.symm t.symm (transportMarkedClasses s t q)=q := by
  induction q using Quotient.inductionOn with | _ M =>
    exact congrArg Quotient.mk'' (marked_transport_inverse M s t)

/-- Changing finite vertex carriers induces a true equivalence of marked isomorphism classes. -/
noncomputable def markedCarrierEquiv (s : I ≃ I') (t : J ≃ J') :
    MarkedClass I J d ≃ MarkedClass I' J' d where
  toFun := transportMarkedClasses s t
  invFun := transportMarkedClasses s.symm t.symm
  left_inv := marked_class_transport_inverse s t
  right_inv := marked_class_transport_inverse s.symm t.symm


end KroneckerMarkedCarrierTransport
end

/- Original module: KroneckerGradedMarkedBranchCounts -/
section
set_option autoImplicit false
namespace KroneckerGradedMarkedBranchCounts
open KroneckerFiniteBranchClasses KroneckerMarkedTreeClassCount KroneckerCompletionClassEquivalence
open KroneckerMarkedCarrierTransport KroneckerTreeLeafEnumerator
open MvPolynomial
attribute [local instance] Classical.propDecidable

noncomputable def optionFinSinkEquiv (n : ℕ) : Option (Fin (2*n)) ≃ Fin (2*n+1) :=
  Fintype.equivOfCardEq (by simp)

/-- The graded source-branch count is the actual marked saturated-tree count, not an assigned binomial expression. -/
theorem source_degree_marked_count (n : ℕ) (d : Fin 3) :
    Fintype.card (SourceDegreeClass n d)=Fintype.card (MarkedClass (Fin n) (Fin (2*n+1)) d) := by
  simp only [←Nat.card_eq_fintype_card]
  exact Nat.card_congr ((completionClassEquiv (I:=Fin n) (J:=Fin (2*n)) (d:=d)).trans
    (markedCarrierEquiv (d:=d) (Equiv.refl (Fin n)) (optionFinSinkEquiv n)))


end KroneckerGradedMarkedBranchCounts
end
