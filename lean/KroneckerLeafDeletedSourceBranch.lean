import KroneckerColoredTableTransport
import KroneckerTableLeafMarks
import KroneckerRootedBranchTrees

/- Original module: KroneckerLeafDeletedColors -/
section
set_option autoImplicit false
namespace KroneckerLeafDeletedColors
open KroneckerFiniteColoredTables KroneckerColoredTableRestrictions KroneckerTableLeafMarks
open KroneckerSaturatedTableAction KroneckerVacantSlotLeaves
attribute [local instance] Classical.propDecidable

variable {I J : Type} [Fintype I]

noncomputable def leafOwner (T : ColoredTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T d l) : I := Classical.choose hl.2

theorem leaf_owner_code (T : ColoredTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T d l) : T.code (leafOwner T hl) l=some d := Classical.choose_spec hl.2

/-- A marked leaf has one actual source owner, independently of how its incidence is witnessed. -/
theorem leaf_incidence_iff_owner (T : ColoredTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T d l) (i : I) : Incidence T i l ↔ i=leafOwner T hl := by
  haveI : Subsingleton {i // Incidence T i l} :=
    Fintype.card_le_one_iff_subsingleton.mp hl.1.le
  constructor
  · intro hi
    exact congrArg Subtype.val (Subsingleton.elim (⟨i,hi⟩ : {i // Incidence T i l})
      ⟨leafOwner T hl,⟨d,leaf_owner_code T hl⟩⟩)
  · intro he
    exact he ▸ ⟨d,leaf_owner_code T hl⟩

/-- Leaf deletion removes precisely its parent color at its owner, and no other source color. -/
theorem leaf_deleted_source_colors [Fintype J] (T : SaturatedTable I J) {d : Fin 3} {l : J}
    (hl : LeafMark T.1 d l) (i : I) (e : Fin 3) :
    (∃ j, (restrictSinkTable T.1 (fun j => j≠l)).code i j=some e) ↔
      i≠leafOwner T.1 hl ∨ e≠d := by
  constructor
  · rintro ⟨j,hj⟩
    by_contra h
    push Not at h
    have he : j.1=l := T.1.atSource i j.1 l e hj
      (by rw [h.1,h.2]; exact leaf_owner_code T.1 hl)
    exact j.2 he
  · intro h
    obtain ⟨j,hj⟩ := (source_color_bijective (coloring T.1) T.2.2 i).2 e
    have hc : T.1.code i j=some e := (code_color T.1 i j j.2).trans (congrArg some hj)
    have hn : j.1≠l := by
      intro he
      have hi : i=leafOwner T.1 hl := (leaf_incidence_iff_owner T.1 hl i).mp (he ▸ j.2)
      have hd : e=d := Option.some.inj (hc.symm.trans (by rw [he,hi]; exact leaf_owner_code T.1 hl))
      rcases h with h | h
      · exact h hi
      · exact h hd
    exact ⟨⟨j,hn⟩,hc⟩

end KroneckerLeafDeletedColors
end

/- Original module: KroneckerSingleLeafPruning -/
section
set_option autoImplicit false
namespace KroneckerSingleLeafPruning
open SimpleGraph KroneckerTreeCutComponents KroneckerRootedEdgePartition KroneckerRootedBranchTrees

variable {V : Type*} {G : SimpleGraph V}

/-- Deleting the only edge of a leaf leaves every other vertex on the neighbor side. -/
theorem leaf_cut_complement (hT : G.IsTree) {l r x : V}
    (hl : ∀ v,G.Adj l v ↔ v=r) : cutSide G l r x ↔ x≠l := by
  have hr : G.Adj l r := (hl r).mpr rfl
  constructor
  · intro hx he
    exact tree_cut_excludes_source hT hr (he ▸ hx)
  · intro hx
    obtain ⟨v,hv,_⟩ := unique_outgoing_branch hT l hx
    have he : v.1=r := (hl v).mp v.2
    simpa only [he] using hv

/-- Removing one specified leaf preserves the actual tree on all remaining vertices. -/
theorem prune_single_leaf_is_tree (hT : G.IsTree) {l r : V}
    (hl : ∀ v,G.Adj l v ↔ v=r) : (G.induce {x | x≠l}).IsTree := by
  have he : {x | cutSide G l r x}={x | x≠l} := Set.ext (fun _ => leaf_cut_complement hT hl)
  rw [←he]
  exact outgoing_branch_is_tree hT ((hl r).mpr rfl)

end KroneckerSingleLeafPruning
end

/- Original module: KroneckerLeafDeletedSourceBranch -/
section
set_option autoImplicit false
namespace KroneckerLeafDeletedSourceBranch
open SimpleGraph KroneckerFiniteColoredTables KroneckerColoredTableRestrictions
open KroneckerTableLeafMarks KroneckerSaturatedTableAction KroneckerLeafDeletedColors
open KroneckerBipartiteIncidence KroneckerSingleLeafPruning
attribute [local instance] Classical.propDecidable

variable {I J : Type}

/-- A source-rooted actual colored tree with exactly its parent color omitted. -/
def IsSourceBranch (T : ColoredTable I J) (r : I) (d : Fin 3) : Prop :=
  (incidenceGraph (Incidence T)).IsTree ∧
    ∀ i e,(∃ j,T.code i j=some e) ↔ i≠r ∨ e≠d

theorem source_branch_parent_color_absent {T : ColoredTable I J} {r : I} {d : Fin 3}
    (h : IsSourceBranch T r d) (j : J) : T.code r j≠some d := by
  intro hj
  have hf := (h.2 r d).mp ⟨j,hj⟩
  simp at hf

/-- Marking and deleting a leaf produces the required actual source branch. -/
theorem leaf_delete_is_source_branch [Fintype I] [Fintype J]
    (T : SaturatedTable I J) {d : Fin 3} {l : J} (hl : LeafMark T.1 d l) :
    IsSourceBranch (restrictSinkTable T.1 (fun j => j≠l)) (leafOwner T.1 hl) d := by
  refine ⟨?_,leaf_deleted_source_colors T hl⟩
  apply (sinkRestrictionGraphIso T.1 (fun j => j≠l)).isTree_iff.mpr
  have he : {v : I ⊕ J | Sum.elim (fun _ => True) (fun j => j≠l) v}=
      {v | v≠Sum.inr l} := by
    ext v
    cases v <;> simp
  rw [he]
  apply prune_single_leaf_is_tree T.2.1 (r:=Sum.inl (leafOwner T.1 hl))
  intro v
  cases v with
  | inl i => simpa [incidenceGraph] using leaf_incidence_iff_owner T.1 hl i
  | inr j => simp [incidenceGraph]

end KroneckerLeafDeletedSourceBranch
end
