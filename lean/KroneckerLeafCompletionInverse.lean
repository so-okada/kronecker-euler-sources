import KroneckerSourceBranchDegrees
import Mathlib.Logic.Equiv.Option

/- Original module: KroneckerBipartiteLeafExtension -/
section
set_option autoImplicit false
namespace KroneckerBipartiteLeafExtension
open SimpleGraph KroneckerBipartiteIncidence KroneckerUnrootedColoredRigidity
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I J : Type}

def extendIncidence (R : I → J → Prop) (r : I) : I → Option J → Prop
  | i,none => i=r
  | i,some j => R i j

def oldVertex (v : I ⊕ J) : I ⊕ Option J :=
  match v with
  | .inl i => .inl i
  | .inr j => .inr (some j)

def oldVertexHom (R : I → J → Prop) (r : I) :
    incidenceGraph R →g incidenceGraph (extendIncidence R r) where
  toFun := oldVertex
  map_rel' := by intro u v h; cases u <;> cases v <;> exact h

theorem leaf_extension_connected (R : I → J → Prop) (r : I)
    (h : (incidenceGraph R).Connected) : (incidenceGraph (extendIncidence R r)).Connected := by
  have hr : ∀ v,(incidenceGraph (extendIncidence R r)).Reachable (.inl r) v := by
    intro v
    cases v with
    | inl i => exact (h (.inl r) (.inl i)).map (oldVertexHom R r)
    | inr j => cases j with
      | none => exact (show (incidenceGraph (extendIncidence R r)).Adj (.inl r) (.inr none) from rfl).reachable
      | some j => exact (h (.inl r) (.inr j)).map (oldVertexHom R r)
  exact { preconnected := fun u v => (hr u).symm.trans (hr v), nonempty := ⟨.inl r⟩ }

def leafExtensionEdgeEquiv (R : I → J → Prop) (r : I) :
    {p : I × Option J // extendIncidence R r p.1 p.2} ≃
      Option {p : I × J // R p.1 p.2} where
  toFun p := match p with
    | ⟨(i,none),_⟩ => none
    | ⟨(i,some j),h⟩ => some ⟨(i,j),h⟩
  invFun p := match p with
    | none => ⟨(r,none),rfl⟩
    | some p => ⟨(p.1.1,some p.1.2),p.2⟩
  left_inv := by
    rintro ⟨⟨i,j⟩,h⟩
    cases j with
    | none => change i=r at h; subst i; rfl
    | some j => rfl
  right_inv := by intro p; cases p <;> rfl

/-- Adding a new sink leaf to an actual finite bipartite tree gives an actual tree. -/
theorem leaf_extension_tree [Fintype I] [Fintype J] (R : I → J → Prop) (r : I)
    (h : (incidenceGraph R).IsTree) : (incidenceGraph (extendIncidence R r)).IsTree := by
  classical
  apply isTree_iff_connected_and_card.mpr
  refine ⟨leaf_extension_connected R r h.connected,?_⟩
  have hc := tree_incidence_card R h
  have he := Fintype.card_congr (leafExtensionEdgeEquiv R r)
  rw [Fintype.card_option] at he
  have hs := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (extendIncidence R r))
  rw [Fintype.card_sigma] at hs
  have hd := (incidenceGraph (extendIncidence R r)).sum_degrees_eq_twice_card_edges
  rw [incidence_degree_sum] at hd
  rw [Nat.card_eq_fintype_card,←edgeFinset_card,Nat.card_eq_fintype_card,
    Fintype.card_sum,Fintype.card_option]
  omega

end KroneckerBipartiteLeafExtension
end

/- Original module: KroneckerColoredLeafExtension -/
section
set_option autoImplicit false
namespace KroneckerColoredLeafExtension
open KroneckerFiniteColoredTables KroneckerBipartiteLeafExtension
open KroneckerBipartiteIncidence KroneckerLeafDeletedSourceBranch
attribute [local instance] Classical.propDecidable

variable {I J : Type}

noncomputable def extendColoredTable (T : ColoredTable I J) (r : I) (d : Fin 3)
    (hd : ∀ j,T.code r j≠some d) : ColoredTable I (Option J) where
  code i j := match j with
    | none => if i=r then some d else none
    | some j => T.code i j
  atSource := by
    intro i j k e hj hk
    cases j with
    | none => cases k with
      | none => rfl
      | some k =>
        by_cases hi : i=r
        · subst i
          simp at hj
          exact False.elim (hd k (hk.trans (congrArg some hj.symm)))
        · simp [hi] at hj
    | some j => cases k with
      | none =>
        by_cases hi : i=r
        · subst i
          simp at hk
          exact False.elim (hd j (hj.trans (congrArg some hk.symm)))
        · simp [hi] at hk
      | some k => exact congrArg some (T.atSource i j k e hj hk)
  atSink := by
    intro i k j e hi hk
    cases j with
    | none =>
      have hir : i=r := by by_contra h; simp [h] at hi
      have hkr : k=r := by by_contra h; simp [h] at hk
      exact hir.trans hkr.symm
    | some j => exact T.atSink i k j e hi hk

theorem extended_colored_incidence (T : ColoredTable I J) (r : I) (d : Fin 3)
    (hd : ∀ j,T.code r j≠some d) (i : I) (j : Option J) :
    Incidence (extendColoredTable T r d hd) i j ↔ extendIncidence (Incidence T) r i j := by
  cases j with
  | none =>
    simp only [Incidence,extendColoredTable,extendIncidence]
    by_cases h : i=r <;> simp [h]
  | some j => rfl

theorem extended_colored_graph (T : ColoredTable I J) (r : I) (d : Fin 3)
    (hd : ∀ j,T.code r j≠some d) :
    incidenceGraph (Incidence (extendColoredTable T r d hd))=
      incidenceGraph (extendIncidence (Incidence T) r) := by
  have he : Incidence (extendColoredTable T r d hd)=extendIncidence (Incidence T) r := by
    funext i j
    exact propext (extended_colored_incidence T r d hd i j)
  rw [he]

/-- Parent-leaf completion preserves both the proper coloring and the actual tree. -/
theorem extended_colored_tree [Fintype I] [Fintype J]
    (T : ColoredTable I J) (r : I) (d : Fin 3) (h : IsSourceBranch T r d) :
    (incidenceGraph (Incidence (extendColoredTable T r d
      (source_branch_parent_color_absent h)))).IsTree := by
  rw [extended_colored_graph]
  exact leaf_extension_tree (Incidence T) r h.1

end KroneckerColoredLeafExtension
end

/- Original module: KroneckerSourceBranchCompletion -/
section
set_option autoImplicit false
namespace KroneckerSourceBranchCompletion
open KroneckerFiniteColoredTables KroneckerColoredLeafExtension KroneckerLeafDeletedSourceBranch
open KroneckerSaturatedTableAction KroneckerTableLeafMarks KroneckerLeafDeletedColors
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem completed_source_degrees (T : ColoredTable I J) (r : I) (d : Fin 3)
    (h : IsSourceBranch T r d) (i : I) :
    Fintype.card {j // Incidence (extendColoredTable T r d
      (source_branch_parent_color_absent h)) i j}=3 := by
  let E := extendColoredTable T r d (source_branch_parent_color_absent h)
  have hs : Function.Surjective (fun j : {j // Incidence E i j} => (coloring E).color i j j.2) := by
    intro e
    have he : ∃ j,E.code i j=some e := by
      by_cases hi : i=r
      · by_cases hd : e=d
        · exact ⟨none,by simp [E,extendColoredTable,hi,hd]⟩
        · obtain ⟨j,hj⟩ := (h.2 i e).mpr (Or.inr hd)
          exact ⟨some j,hj⟩
      · obtain ⟨j,hj⟩ := (h.2 i e).mpr (Or.inl hi)
        exact ⟨some j,hj⟩
    obtain ⟨j,hj⟩ := he
    exact ⟨⟨j,⟨e,hj⟩⟩,Option.some.inj ((code_color E i j ⟨e,hj⟩).symm.trans hj)⟩
  exact (Fintype.card_congr (Equiv.ofBijective _ ⟨(coloring E).at_source i,hs⟩)).trans
    (Fintype.card_fin 3)

noncomputable def completeBranch (T : ColoredTable I J) (r : I) (d : Fin 3)
    (h : IsSourceBranch T r d) : SaturatedTable I (Option J) :=
  ⟨extendColoredTable T r d (source_branch_parent_color_absent h),
    extended_colored_tree T r d h,completed_source_degrees T r d h⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completed parent is an actual marked leaf of the specified color. -/
theorem completed_parent_leaf (T : ColoredTable I J) (r : I) (d : Fin 3)
    (h : IsSourceBranch T r d) : LeafMark (completeBranch T r d h).1 d none := by
  refine ⟨?_,⟨r,by simp [completeBranch,extendColoredTable]⟩⟩
  have hc := Fintype.card_congr (Equiv.subtypeEquivRight (fun i =>
    extended_colored_incidence T r d (source_branch_parent_color_absent h) i none))
  simpa [completeBranch,KroneckerBipartiteLeafExtension.extendIncidence] using hc

theorem completed_parent_owner (T : ColoredTable I J) (r : I) (d : Fin 3)
    (h : IsSourceBranch T r d) :
    leafOwner (completeBranch T r d h).1 (completed_parent_leaf T r d h)=r := by
  symm
  apply (leaf_incidence_iff_owner _ (completed_parent_leaf T r d h) r).mp
  exact ⟨d,by simp [completeBranch,extendColoredTable]⟩

end KroneckerSourceBranchCompletion
end

/- Original module: KroneckerLeafCompletionInverse -/
section
set_option autoImplicit false
namespace KroneckerLeafCompletionInverse
open KroneckerFiniteColoredTables KroneckerColoredTableRestrictions KroneckerLeafDeletedColors
open KroneckerLeafDeletedSourceBranch KroneckerSourceBranchCompletion KroneckerColoredLeafExtension
open KroneckerSaturatedTableAction KroneckerTableLeafMarks KroneckerTableIsomorphisms
open KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I] [Fintype J]

omit [Fintype J] in
theorem marked_leaf_column (T : ColoredTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T d l) (i : I) :
    T.code i l=if i=leafOwner T hl then some d else none := by
  by_cases hi : i=leafOwner T hl
  · simpa [hi] using leaf_owner_code T hl
  · rw [ite_eq_right hi]
    cases hc : T.code i l with
    | none => rfl
    | some e => exact False.elim (hi ((leaf_incidence_iff_owner T hl i).mp ⟨e,hc⟩))

/-- Deletion followed by parent completion reconstructs the entire original colored tree. -/
noncomputable def restoreMarkedLeafIso (T : SaturatedTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T.1 d l) :
    ColoredIso
      (coloring (completeBranch (restrictSinkTable T.1 (fun j => j≠l))
        (leafOwner T.1 hl) d (leaf_delete_is_source_branch T hl)).1)
      (coloring T.1) := by
  classical
  apply isoOfCode _ _ (Equiv.refl I) (Equiv.optionSubtypeNe l)
  intro i j
  cases j with
  | none => exact marked_leaf_column T.1 hl i
  | some j => rfl

theorem restored_mark (T : SaturatedTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T.1 d l) : (restoreMarkedLeafIso T hl).sink none=l := rfl

def someSubtypeEquiv (J : Type) : J ≃ {j : Option J // j≠none} where
  toFun j := ⟨some j,by simp⟩
  invFun
    | ⟨none,h⟩ => False.elim (h rfl)
    | ⟨some j,_⟩ => j
  left_inv _ := rfl
  right_inv := by
    rintro ⟨j,h⟩
    cases j with
    | none => exact False.elim (h rfl)
    | some j => rfl

/-- Completion followed by deletion recovers every branch incidence and every color. -/
noncomputable def deleteCompletedIso (T : ColoredTable I J) (r : I) (d : Fin 3)
    (h : IsSourceBranch T r d) :
    ColoredIso
      (coloring (restrictSinkTable (completeBranch T r d h).1 (fun j => j≠none)))
      (coloring T) := by
  apply isoOfCode _ _ (Equiv.refl I) (someSubtypeEquiv J).symm
  intro i j
  rcases j with ⟨j,hj⟩
  cases j with
  | none => exact False.elim (hj rfl)
  | some j => rfl

theorem restored_branch_root (T : ColoredTable I J) (r : I) (d : Fin 3)
    (h : IsSourceBranch T r d) : (deleteCompletedIso T r d h).source r=r := rfl

end KroneckerLeafCompletionInverse
end
