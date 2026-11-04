import Mathlib.Data.Fintype.Pi
import Mathlib.RingTheory.PowerSeries.Basic
import KroneckerSinkClassAssembly
import Mathlib.Algebra.BigOperators.Ring.Finset

section

/- Original module: KroneckerSourceBranchPorts -/
section
set_option autoImplicit false
namespace KroneckerSourceBranchPorts
open SimpleGraph KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerLeafDeletedSourceBranch KroneckerSourceBranchDegrees
open KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches KroneckerTreeCutComponents

variable {I J : Type} {T : ColoredTable I J} {r : I} {d : Fin 3}

/-- The two sink ports of a source branch are indexed by the two other colors. -/
noncomputable def sourcePortEquiv (h : IsSourceBranch T r d) :
    {j // Incidence T r j} ≃ {e : Fin 3 // e≠d} :=
  (branchSourceColorEquiv h r).trans (Equiv.subtypeEquivRight (fun _ => by simp))

/-- Every port carries an actual outgoing sink branch, with the edge color as parent color. -/
theorem source_port_sink_branch (h : IsSourceBranch T r d) (j : {j // Incidence T r j}) :
    IsSinkBranch (cutTable T (.inl r) (.inr j.1)) (sinkCutRoot T r j.1)
      ((coloring T).color r j.1 j.2) := by
  apply outgoing_sink_is_branch T h.1 (code_color T r j.1 j.2)
  intro i hi e
  have hn : i≠r := by
    intro he
    have hx : cutSide (incidenceGraph (Incidence T)) (.inl r) (.inr j.1) (.inl i) := hi
    rw [he] at hx
    exact tree_cut_excludes_source h.1 (show (incidenceGraph (Incidence T)).Adj (.inl r) (.inr j.1) from j.2) hx
  exact (h.2 i e).mpr (Or.inl hn)

end KroneckerSourceBranchPorts
end

/- Original module: KroneckerActualSourceCutFamily -/
section
set_option autoImplicit false
namespace KroneckerActualSourceCutFamily
open SimpleGraph KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerTreeCutComponents KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches
open KroneckerColoredSourceAttachment

variable {I J : Type}

abbrev SourcePort (T : ColoredTable I J) (r : I) := {j // Incidence T r j}
def cutFamily (T : ColoredTable I J) (r : I) (p : SourcePort T r) :=
  cutTable T (.inl r) (.inr p.1)
def cutRoots (T : ColoredTable I J) (r : I) (p : SourcePort T r) := sinkCutRoot T r p.1
noncomputable def cutColors (T : ColoredTable I J) (r : I) (p : SourcePort T r) :=
  (coloring T).color r p.1 p.2

theorem cut_colors_injective (T : ColoredTable I J) (r : I) : Function.Injective (cutColors T r) :=
  (coloring T).at_source r

theorem cut_parent_color_absent (T : ColoredTable I J)
    (hT : (incidenceGraph (Incidence T)).IsTree) (r : I) (p : SourcePort T r)
    (i : {i // cutSource T (.inl r) (.inr p.1) i}) :
    (cutFamily T r p).code i (cutRoots T r p)≠some (cutColors T r p) := by
  intro h
  have he : i.1=r := T.atSink i.1 r p.1 (cutColors T r p) h (code_color T r p.1 p.2)
  have hi := i.2
  change cutSide (incidenceGraph (Incidence T)) (.inl r) (.inr p.1) (.inl i.1) at hi
  rw [he] at hi
  exact tree_cut_excludes_source hT (u:=.inl r) (v:=.inr p.1) p.2 hi


noncomputable def assembleActualCuts (T : ColoredTable I J)
    (hT : (incidenceGraph (Incidence T)).IsTree) (r : I) :=
  sourceAttachment (cutFamily T r) (cutRoots T r) (cutColors T r)
    (cut_colors_injective T r) (cut_parent_color_absent T hT r)

end KroneckerActualSourceCutFamily
end

/- Original module: KroneckerActualCutVertexBijections -/
section
set_option autoImplicit false
namespace KroneckerActualCutVertexBijections
open SimpleGraph KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerIncomingSourceBranches KroneckerTreeCutComponents KroneckerRootedEdgePartition
open KroneckerActualSourceCutFamily

variable {I J : Type} (T : ColoredTable I J)
variable (hT : (incidenceGraph (Incidence T)).IsTree) (r : I)

def actualSourceMap : Option (Σ p : SourcePort T r,{i // cutSource T (.inl r) (.inr p.1) i}) → I
  | none => r
  | some p => p.2.1

include hT

theorem actual_source_map_bijective : Function.Bijective (actualSourceMap T r) := by
  constructor
  · intro a b hab
    cases a with
    | none => cases b with
      | none => rfl
      | some b =>
        have hb := b.2.2
        change r=b.2.1 at hab
        change cutSide (incidenceGraph (Incidence T)) (.inl r) (.inr b.1.1) (.inl b.2.1) at hb
        rw [←hab] at hb
        exact False.elim (tree_cut_excludes_source hT (u:=.inl r) (v:=.inr b.1.1) b.1.2 hb)
    | some a => cases b with
      | none =>
        have ha := a.2.2
        change a.2.1=r at hab
        change cutSide (incidenceGraph (Incidence T)) (.inl r) (.inr a.1.1) (.inl a.2.1) at ha
        rw [hab] at ha
        exact False.elim (tree_cut_excludes_source hT (u:=.inl r) (v:=.inr a.1.1) a.1.2 ha)
      | some b =>
        rcases a with ⟨p,i⟩; rcases b with ⟨q,j⟩
        change i.1=j.1 at hab
        have he : p=q := Subtype.ext (Sum.inr.inj
          (branch_neighbor_unique hT (r:=.inl r) (v:=.inr p.1) (w:=.inr q.1) p.2 q.2 (hab ▸ i.2) j.2))
        subst q
        have hi : i=j := Subtype.ext hab
        subst j; rfl
  · intro i
    by_cases hi : i=r
    · exact ⟨none,hi.symm⟩
    · obtain ⟨v,hv,_⟩ := unique_outgoing_branch hT (.inl r) (x:=.inl i) (by simpa using hi)
      rcases v with ⟨v,hv'⟩
      cases v with
      | inl k => exact False.elim hv'
      | inr j => exact ⟨some ⟨⟨j,hv'⟩,⟨i,hv⟩⟩,rfl⟩

noncomputable def actualSourceEquiv (hT : (incidenceGraph (Incidence T)).IsTree) (r : I) :
    Option (Σ p : SourcePort T r,{i // cutSource T (.inl r) (.inr p.1) i}) ≃ I :=
  Equiv.ofBijective (actualSourceMap T r) (actual_source_map_bijective T hT r)

theorem actual_sink_map_bijective : Function.Bijective
    (fun p : Σ p : SourcePort T r,{j // cutSink T (.inl r) (.inr p.1) j} => p.2.1) := by
  constructor
  · rintro ⟨p,i⟩ ⟨q,j⟩ hab
    change i.1=j.1 at hab
    have he : p=q := Subtype.ext (Sum.inr.inj
      (branch_neighbor_unique hT (r:=.inl r) (v:=.inr p.1) (w:=.inr q.1) p.2 q.2 (hab ▸ i.2) j.2))
    subst q
    have hi : i=j := Subtype.ext hab
    subst j; rfl
  · intro j
    obtain ⟨v,hv,_⟩ := unique_outgoing_branch hT (.inl r) (x:=.inr j) (by simp)
    rcases v with ⟨v,hv'⟩
    cases v with
    | inl k => exact False.elim hv'
    | inr k => exact ⟨⟨⟨k,hv'⟩,⟨j,hv⟩⟩,rfl⟩

noncomputable def actualSinkEquiv (hT : (incidenceGraph (Incidence T)).IsTree) (r : I) :
    (Σ p : SourcePort T r,{j // cutSink T (.inl r) (.inr p.1) j}) ≃ J :=
  Equiv.ofBijective (fun p => p.2.1) (actual_sink_map_bijective T hT r)

end KroneckerActualCutVertexBijections
end

/- Original module: KroneckerRootedBranchAdjacency -/
section
set_option autoImplicit false
namespace KroneckerRootedBranchAdjacency
open SimpleGraph KroneckerTreeCutComponents KroneckerRootedEdgePartition KroneckerRootedBranchTrees

variable {V : Type*} {G : SimpleGraph V}

/-- Each outgoing component meets the root through its specified first vertex only. -/
theorem branch_root_adjacency_iff (hT : G.IsTree) {r v x : V}
    (hv : G.Adj r v) (hx : cutSide G r v x) : G.Adj r x ↔ x=v := by
  constructor
  · intro ha
    exact (branch_neighbor_unique hT hv ha hx (cut_side_contains_target G r x)).symm
  · rintro rfl
    exact hv

/-- An edge between two nonroot vertices belongs to a single outgoing component. -/
theorem adjacent_branch_indices_equal (hT : G.IsTree) {r v w x y : V}
    (hv : G.Adj r v) (hw : G.Adj r w)
    (hx : cutSide G r v x) (hy : cutSide G r w y) (hxy : G.Adj x y) : v=w := by
  have hne : y≠r := by
    intro he
    exact tree_cut_excludes_source hT hw (he ▸ hy)
  exact branch_neighbor_unique hT hv hw (branch_closed_away_from_root hx hxy hne) hy


end KroneckerRootedBranchAdjacency
end

/- Original module: KroneckerActualCutColorRecovery -/
section
set_option autoImplicit false
namespace KroneckerActualCutColorRecovery
open SimpleGraph KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerActualSourceCutFamily KroneckerActualCutVertexBijections
open KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches KroneckerRootedBranchAdjacency
open KroneckerColoredSourceAttachment KroneckerColoredIncidenceIso KroneckerTableIsomorphisms
attribute [local instance] Classical.propDecidable

variable {I J : Type} (T : ColoredTable I J)
variable (hT : (incidenceGraph (Incidence T)).IsTree) (r : I)

include hT

theorem actual_cut_root_code (p : SourcePort T r)
    (j : {j // cutSink T (.inl r) (.inr p.1) j}) :
    T.code r j.1=if j=cutRoots T r p then some (cutColors T r p) else none := by
  by_cases hj : j=cutRoots T r p
  · rw [ite_eq_left hj,hj]
    exact code_color T r p.1 p.2
  · rw [ite_eq_right hj]
    cases he : T.code r j.1 with
    | none => rfl
    | some d =>
      have hv : j.1=p.1 := Sum.inr.inj
        ((branch_root_adjacency_iff hT (r:=.inl r) (v:=.inr p.1) (x:=.inr j.1)
          p.2 j.2).mp ⟨d,he⟩)
      exact False.elim (hj (Subtype.ext hv))

theorem actual_cross_cut_code {p q : SourcePort T r} (hpq : p≠q)
    (i : {i // cutSource T (.inl r) (.inr p.1) i})
    (j : {j // cutSink T (.inl r) (.inr q.1) j}) : T.code i.1 j.1=none := by
  cases he : T.code i.1 j.1 with
  | none => rfl
  | some d =>
    have hv := adjacent_branch_indices_equal hT (r:=.inl r)
      (v:=.inr p.1) (w:=.inr q.1) (x:=.inl i.1) (y:=.inr j.1)
      p.2 q.2 i.2 j.2 (show (incidenceGraph (Incidence T)).Adj (.inl i.1) (.inr j.1) from ⟨d,he⟩)
    exact False.elim (hpq (Subtype.ext (Sum.inr.inj hv)))

/-- Reassembling the actual colored cut tables gives the original colored tree, with its root fixed. -/
noncomputable def actualCutsIso :
    ColoredIso (coloring (assembleActualCuts T hT r)) (coloring T) := by
  apply isoOfCode _ _ (actualSourceEquiv T hT r) (actualSinkEquiv T hT r)
  intro i j
  rcases j with ⟨q,j⟩
  cases i with
  | none =>
    change T.code r j.1=(assembleActualCuts T hT r).code none ⟨q,j⟩
    rw [actual_cut_root_code T hT r]
    unfold assembleActualCuts
    rw [attachment_root_code]
    split_ifs <;> rfl
  | some p =>
    rcases p with ⟨p,i⟩
    change T.code i.1 j.1=(assembleActualCuts T hT r).code (some ⟨p,i⟩) ⟨q,j⟩
    by_cases hpq : p=q
    · subst q
      exact (attachment_internal_code (cutFamily T r) (cutRoots T r) (cutColors T r)
        (cut_colors_injective T r) (cut_parent_color_absent T hT r) p i j).symm
    · rw [actual_cross_cut_code T hT r hpq i j]
      exact (attachment_cross_code (cutFamily T r) (cutRoots T r) (cutColors T r)
        (cut_colors_injective T r) (cut_parent_color_absent T hT r) hpq i j).symm


end KroneckerActualCutColorRecovery
end
end

section

set_option autoImplicit false
namespace KroneckerFiniteDegreePartitions
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Finite degree partitions retain the complete port indexing. -/
def DegreePartition (K : Type) [Fintype K] (n : ℕ) := {a : K → ℕ // ∑ k,a k=n}

variable {K : Type} [Fintype K] {n : ℕ}

theorem part_le_total (a : DegreePartition K n) (k : K) : a.1 k≤n := by
  classical
  calc
    a.1 k ≤ ∑ j,a.1 j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    _ = n := a.2

def boundedPartition (a : DegreePartition K n) : K → Fin (n+1) :=
  fun k => ⟨a.1 k,Nat.lt_succ_of_le (part_le_total a k)⟩

theorem bounded_partition_injective : Function.Injective (boundedPartition (K:=K) (n:=n)) := by
  intro a b h
  apply Subtype.ext
  funext k
  exact congrArg Fin.val (congrFun h k)

instance : Finite (DegreePartition K n) := Finite.of_injective boundedPartition bounded_partition_injective
noncomputable instance : Fintype (DegreePartition K n) := Fintype.ofFinite _


end KroneckerFiniteDegreePartitions
end

section

/- Original module: KroneckerCanonicalSourceChildren -/
section
set_option autoImplicit false
namespace KroneckerCanonicalSourceChildren
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerSourceClassAssembly
open KroneckerSourceBranchPorts KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches
open KroneckerActualSourceCutFamily KroneckerActualCutColorRecovery
open KroneckerAttachmentIsomorphisms KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3}

noncomputable def sourceChildPort (S : SourceObject I J d) (k : OtherColors d) :
    SourcePort S.1.1 S.1.2 := (sourcePortEquiv S.2).symm k

omit [Fintype I] [Fintype J] in
theorem source_child_color (S : SourceObject I J d) (k : OtherColors d) :
    cutColors S.1.1 S.1.2 (sourceChildPort S k)=k.1 :=
  congrArg Subtype.val ((sourcePortEquiv S.2).apply_symm_apply k)

abbrev ChildSource (S : SourceObject I J d) (k : OtherColors d) :=
  {i // cutSource S.1.1 (.inl S.1.2) (.inr (sourceChildPort S k).1) i}
abbrev ChildSink (S : SourceObject I J d) (k : OtherColors d) :=
  {j // cutSink S.1.1 (.inl S.1.2) (.inr (sourceChildPort S k).1) j}

noncomputable def sourceChild (S : SourceObject I J d) (k : OtherColors d) :
    SinkObject (ChildSource S k) (ChildSink S k) k.1 :=
  ⟨(cutFamily S.1.1 S.1.2 (sourceChildPort S k),cutRoots S.1.1 S.1.2 (sourceChildPort S k)),by
    have h := source_port_sink_branch S.2 (sourceChildPort S k)
    change KroneckerOutgoingSinkBranches.IsSinkBranch _ _ (cutColors S.1.1 S.1.2 (sourceChildPort S k)) at h
    rw [source_child_color] at h
    exact h⟩

/-- Reindexing actual cuts by their colors preserves the exact colored reconstruction. -/
noncomputable def sourceChildrenIso (S : SourceObject I J d) :
    ColoredIso (coloring (assembleSourceObjects (sourceChild S)).1.1) (coloring S.1.1) :=
  (sourceAttachmentIso (T:=fun k => (sourceChild S k).1.1) (U:=cutFamily S.1.1 S.1.2)
    Subtype.val_injective (fun k => (sourceChild S k).2.2.2)
    (cut_colors_injective S.1.1 S.1.2) (cut_parent_color_absent S.1.1 S.2.1 S.1.2)
    (sourcePortEquiv S.2).symm (fun k => by
      change ColoredIso (coloring (cutFamily S.1.1 S.1.2 ((sourcePortEquiv S.2).symm k)))
        (coloring (cutFamily S.1.1 S.1.2 ((sourcePortEquiv S.2).symm k)))
      exact 1) (fun _ => rfl) (source_child_color S)).trans
      (actualCutsIso S.1.1 S.2.1 S.1.2)

theorem source_children_root (S : SourceObject I J d) :
    (sourceChildrenIso S).source none=S.1.2 := rfl

theorem source_children_grading (S : SourceObject I J d) :
    (∑ k,Fintype.card (ChildSource S k))+1=Fintype.card I := by
  simpa only [Fintype.card_option,Fintype.card_sigma] using
    Fintype.card_congr (sourceChildrenIso S).source

end KroneckerCanonicalSourceChildren
end

/- Original module: KroneckerSourceDegreeAssembly -/
section
set_option autoImplicit false
namespace KroneckerSourceDegreeAssembly
open KroneckerFiniteDegreePartitions KroneckerFiniteBranchClasses KroneckerCanonicalBranchClasses
open KroneckerSourceClassAssembly KroneckerFiniteBranchObjects KroneckerBranchClassWeights
open KroneckerSourceAssemblyWeights KroneckerBranchWeights KroneckerColoredSourceAttachment
attribute [local instance] Classical.propDecidable
open scoped BigOperators

abbrev SourceTuple (d : Fin 3) (n : ℕ) :=
  Σ a : DegreePartition (OtherColors d) n,∀ k,SinkDegreeClass (a.1 k) k.1

variable {d : Fin 3} {n : ℕ}

noncomputable def sourceTupleClass (p : SourceTuple d n) : SourceDegreeClass (n+1) d :=
  sourceClassOf (assembleSourceObjects (fun k => (p.2 k).out)) (by
    simp only [Fintype.card_option,Fintype.card_sigma,Fintype.card_fin,p.1.2])

/-- The assembled class remembers both the ordered degree partition and every child class. -/
theorem source_tuple_class_injective : Function.Injective (sourceTupleClass (d:=d) (n:=n)) := by
  rintro ⟨a,q⟩ ⟨b,q'⟩ h
  have hc := (source_objects_class_iff _ _ _ _).mp h
  have hab : a=b := by
    apply Subtype.ext
    funext k
    obtain ⟨e,_⟩ := hc k
    simpa only [Fintype.card_fin] using Fintype.card_congr e.source
  subst b
  have hq : q=q' := by
    funext k
    have he : (Quotient.mk'' (q k).out : SinkDegreeClass (a.1 k) k.1)=Quotient.mk'' (q' k).out :=
      Quotient.sound (hc k)
    simpa only [Quotient.out_eq'] using he
  subst q'
  rfl

theorem source_tuple_class_weight {R : Type*} [CommSemiring R]
    (p : SourceTuple d n) (x : R) (y : Fin 3 → R) :
    sourceClassWeight x y (sourceTupleClass p)=x*∏ k,sinkClassWeight x y (p.2 k) := by
  rw [sourceTupleClass,canonical_source_weight]
  dsimp only [assembleSourceObjects]
  rw [source_assembly_weight]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  exact congrArg (sinkClassWeight x y) (Quotient.out_eq' (p.2 k))

end KroneckerSourceDegreeAssembly
end

/- Original module: KroneckerSourceTupleSurjectivity -/
section
set_option autoImplicit false
namespace KroneckerSourceTupleSurjectivity
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerFiniteBranchClasses
open KroneckerBranchClassRelations KroneckerCanonicalBranchClasses KroneckerColoredIncidenceIso
open KroneckerSourceClassAssembly KroneckerSourceDegreeAssembly KroneckerCanonicalSourceChildren
open KroneckerFiniteDegreePartitions KroneckerAttachmentIsomorphisms
attribute [local instance] Classical.propDecidable
open scoped BigOperators

section Representatives
variable {I J : Type} [Fintype I] [Fintype J] {d : Fin 3} {n : ℕ}

theorem source_class_out_iso (S : SourceObject I J d) (h : Fintype.card I=n) :
    ∃ e : ColoredIso (coloring (sourceClassOf S h).out.1.1) (coloring S.1.1),
      e.source (sourceClassOf S h).out.1.2=S.1.2 := by
  have hq : SourceRel d (sourceClassOf S h).out (sourceAtDegree S h) :=
    Quotient.exact (Quotient.out_eq' (sourceClassOf S h))
  obtain ⟨e,he⟩ := hq
  obtain ⟨f,hf⟩ := source_at_degree_iso S h
  refine ⟨e.trans f.symm,?_⟩
  change f.source.symm (e.source (sourceClassOf S h).out.1.2)=S.1.2
  rw [he,←hf,Equiv.symm_apply_apply]

theorem sink_class_out_iso (S : SinkObject I J d) (h : Fintype.card I=n) :
    ∃ e : ColoredIso (coloring (sinkClassOf S h).out.1.1) (coloring S.1.1),
      e.sink (sinkClassOf S h).out.1.2=S.1.2 := by
  have hq : SinkRel d (sinkClassOf S h).out (sinkAtDegree S h) :=
    Quotient.exact (Quotient.out_eq' (sinkClassOf S h))
  obtain ⟨e,he⟩ := hq
  obtain ⟨f,hf⟩ := sink_at_degree_iso S h
  refine ⟨e.trans f.symm,?_⟩
  change f.sink.symm (e.sink (sinkClassOf S h).out.1.2)=S.1.2
  rw [he,←hf,Equiv.symm_apply_apply]
end Representatives

variable {d : Fin 3} {n : ℕ}

noncomputable def sourceTupleOfObject (S : SourceObject (Fin (n+1)) (Fin (2*(n+1))) d) :
    SourceTuple d n := by
  let a : DegreePartition (OtherColors d) n := ⟨fun k => Fintype.card (ChildSource S k),by
    have h := source_children_grading S
    simpa only [Fintype.card_fin,Nat.add_left_inj] using h⟩
  exact ⟨a,fun k => sinkClassOf (sourceChild S k) rfl⟩

/-- Canonical normalization of each actual cut does not lose its parent branch class. -/
theorem source_tuple_of_object_recovers (S : SourceObject (Fin (n+1)) (Fin (2*(n+1))) d) :
    sourceTupleClass (sourceTupleOfObject S)=Quotient.mk'' S := by
  rw [←source_class_of_canonical S]
  unfold sourceTupleClass
  apply (source_class_of_eq_iff _ _ _ _).mpr
  have h : ∀ k,∃ e : ColoredIso (coloring ((sourceTupleOfObject S).2 k).out.1.1)
      (coloring (sourceChild S k).1.1),
      e.sink ((sourceTupleOfObject S).2 k).out.1.2=(sourceChild S k).1.2 :=
    fun k => sink_class_out_iso (sourceChild S k) rfl
  choose e he using h
  let g := sourceAttachmentIso Subtype.val_injective
    (fun k => ((sourceTupleOfObject S).2 k).out.2.2.2)
    Subtype.val_injective (fun k => (sourceChild S k).2.2.2)
    (Equiv.refl (OtherColors d)) e he (fun _ => rfl)
  refine ⟨g.trans (sourceChildrenIso S),?_⟩
  change (sourceChildrenIso S).source (g.source none)=S.1.2
  have hg : g.source none=none := rfl
  rw [hg,source_children_root]

theorem source_tuple_class_surjective : Function.Surjective (sourceTupleClass (d:=d) (n:=n)) := by
  intro q
  induction q using Quotient.inductionOn with | _ S =>
    exact ⟨sourceTupleOfObject S,source_tuple_of_object_recovers S⟩

/-- The domain uses actual finite degree partitions and actual child isomorphism classes. -/
noncomputable def sourceDegreeEquiv : SourceTuple d n ≃ SourceDegreeClass (n+1) d :=
  Equiv.ofBijective sourceTupleClass ⟨source_tuple_class_injective,source_tuple_class_surjective⟩

end KroneckerSourceTupleSurjectivity
end
end

section

/- Original module: KroneckerPartitionCauchyProduct -/
section
set_option autoImplicit false
namespace KroneckerPartitionCauchyProduct
open KroneckerFiniteDegreePartitions
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K : Type} [Fintype K]

noncomputable def partitionAntidiagEquiv (n : ℕ) :
    DegreePartition K n ≃ {f : K →₀ ℕ // f∈Finset.finsuppAntidiag Finset.univ n} where
  toFun a := ⟨Finsupp.equivFunOnFinite.symm a.1,by
    simp only [Finset.mem_finsuppAntidiag,Finset.subset_univ,and_true]
    exact a.2⟩
  invFun f := ⟨f.1,(Finset.mem_finsuppAntidiag.mp f.2).1⟩
  left_inv _ := rfl
  right_inv f := by apply Subtype.ext; exact Finsupp.equivFunOnFinite.symm_apply_apply f.1

/-- Finite degree partitions give exactly the coefficient formula for an arbitrary finite product. -/
theorem coeff_product_partitions {R : Type*} [CommSemiring R]
    (f : K → PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (∏ k,f k)=
      ∑ a : DegreePartition K n,∏ k,PowerSeries.coeff (a.1 k) (f k) := by
  classical
  rw [PowerSeries.coeff_prod]
  calc
    _ = ∑ l : {f : K →₀ ℕ // f∈Finset.finsuppAntidiag Finset.univ n},
        ∏ k,PowerSeries.coeff (l.1 k) (f k) := by
      rw [←Finset.sum_coe_sort]
    _ = _ := (Equiv.sum_comp (partitionAntidiagEquiv (K:=K) n) _).symm

end KroneckerPartitionCauchyProduct
end

/- Original module: KroneckerTransposeCutDictionary -/
section
set_option autoImplicit false
namespace KroneckerTransposeCutDictionary
open KroneckerFiniteColoredTables KroneckerColoredTableTranspose KroneckerColoredCutTransport
open KroneckerTreeCutComponents KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches
open KroneckerColoredIncidenceIso KroneckerTableIsomorphisms

variable {I J : Type} (T : ColoredTable I J)

theorem transpose_cut_source (i : I) (j : J) (k : I) :
    cutSink (transposeTable T) (.inl j) (.inr i) k ↔ cutSource T (.inr j) (.inl i) k :=
  (cut_side_iso_iff (transposeGraphIso T) (.inl j) (.inr i) (.inr k)).symm

theorem transpose_cut_sink (i : I) (j : J) (l : J) :
    cutSource (transposeTable T) (.inl j) (.inr i) l ↔ cutSink T (.inr j) (.inl i) l :=
  (cut_side_iso_iff (transposeGraphIso T) (.inl j) (.inr i) (.inl l)).symm

/-- Transposed actual cut tables recover the original incoming colored cut, including its source root. -/
noncomputable def transposeCutIso (i : I) (j : J) :
    ColoredIso (coloring (transposeTable (cutTable (transposeTable T) (.inl j) (.inr i))))
      (coloring (cutTable T (.inr j) (.inl i))) :=
  isoOfCode _ _ (Equiv.subtypeEquivRight (transpose_cut_source T i j))
    (Equiv.subtypeEquivRight (transpose_cut_sink T i j)) (fun _ _ => rfl)

theorem transpose_cut_root (i : I) (j : J) :
    (transposeCutIso T i j).source (sinkCutRoot (transposeTable T) j i)=sourceCutRoot T i j := by
  apply Subtype.ext
  rfl

end KroneckerTransposeCutDictionary
end

/- Original module: KroneckerActualSinkReassembly -/
section
set_option autoImplicit false
namespace KroneckerActualSinkReassembly
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence KroneckerColoredIncidenceIso
open KroneckerColoredTableTranspose KroneckerActualSourceCutFamily KroneckerActualCutColorRecovery
open KroneckerTransposeCutDictionary

variable {I J : Type} (T : ColoredTable I J)
variable (hT : (incidenceGraph (Incidence T)).IsTree) (r : J)

noncomputable def assembleActualSinkCuts :=
  transposeTable (assembleActualCuts (transposeTable T) ((transpose_tree_iff T).mpr hT) r)

/-- The dual construction is an inverse on actual colored sink-rooted trees, not only their graphs. -/
noncomputable def actualSinkCutsIso :
    ColoredIso (coloring (assembleActualSinkCuts T hT r)) (coloring T) :=
  transposeColoredIso (actualCutsIso (transposeTable T) ((transpose_tree_iff T).mpr hT) r)



end KroneckerActualSinkReassembly
end

/- Original module: KroneckerSinkBranchPorts -/
section
set_option autoImplicit false
namespace KroneckerSinkBranchPorts
open KroneckerFiniteColoredTables KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches
open KroneckerLeafDeletedSourceBranch

variable {I J : Type} {T : ColoredTable I J} {r : J} {d : Fin 3}

/-- The occupied child ports are an actual subset of the two nonparent colors. -/
noncomputable def sinkPortEquiv (h : IsSinkBranch T r d) :
    {i // Incidence T i r} ≃ {e : Fin 3 // e≠d ∧ ∃ i,T.code i r=some e} := by
  let f : {i // Incidence T i r} → {e : Fin 3 // e≠d ∧ ∃ i,T.code i r=some e} :=
    fun i => ⟨(coloring T).color i r i.2,⟨by
      intro he
      exact h.2.2 i (by rw [←he]; exact code_color T i r i.2),⟨i,code_color T i r i.2⟩⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro i k he
    exact (coloring T).at_sink r (congrArg Subtype.val he)
  · intro e
    obtain ⟨i,hi⟩ := e.2.2
    refine ⟨⟨i,⟨e,hi⟩⟩,?_⟩
    apply Subtype.ext
    exact Option.some.inj ((code_color T i r ⟨e,hi⟩).symm.trans hi)

/-- Each occupied sink port carries the corresponding actual source branch. -/
theorem sink_port_source_branch (h : IsSinkBranch T r d) (i : {i // Incidence T i r}) :
    IsSourceBranch (cutTable T (.inr r) (.inl i.1)) (sourceCutRoot T i.1 r)
      ((coloring T).color i.1 r i.2) := by
  apply incoming_source_is_branch T h.1 (code_color T i.1 r i.2)
  exact fun k _ e => h.2.1 k e


end KroneckerSinkBranchPorts
end

/- Original module: KroneckerCanonicalSinkChildren -/
section
set_option autoImplicit false
namespace KroneckerCanonicalSinkChildren
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerSourceClassAssembly
open KroneckerSinkBranchPorts KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches
open KroneckerActualSourceCutFamily KroneckerActualSinkReassembly KroneckerTransposeCutDictionary
open KroneckerAttachmentIsomorphisms KroneckerColoredIncidenceIso KroneckerColoredTableTranspose
open KroneckerSinkClassAssembly KroneckerLeafDeletedSourceBranch
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I J : Type} {d : Fin 3}

noncomputable def occupiedPorts (S : SinkObject I J d) : Finset (OtherColors d) :=
  Finset.univ.filter (fun e => ∃ i,S.1.1.code i S.1.2=some e.1)

theorem mem_occupied_ports (S : SinkObject I J d) (e : OtherColors d) :
    e∈occupiedPorts S ↔ ∃ i,S.1.1.code i S.1.2=some e.1 := by
  simp only [occupiedPorts,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def sinkPortColors (S : SinkObject I J d) :
    {i // Incidence S.1.1 i S.1.2} ≃ occupiedPorts S :=
  (sinkPortEquiv S.2).trans {
    toFun := fun e => ⟨⟨e.1,e.2.1⟩,(mem_occupied_ports S _).mpr e.2.2⟩
    invFun := fun e => ⟨e.1.1,e.1.2,(mem_occupied_ports S _).mp e.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

noncomputable def sinkChildPort (S : SinkObject I J d) (k : occupiedPorts S) :
    {i // Incidence S.1.1 i S.1.2} := (sinkPortColors S).symm k

theorem sink_child_color (S : SinkObject I J d) (k : occupiedPorts S) :
    (coloring S.1.1).color (sinkChildPort S k).1 S.1.2 (sinkChildPort S k).2=
      occupiedColor (occupiedPorts S) k :=
  congrArg (fun e => e.1.1) ((sinkPortColors S).apply_symm_apply k)

abbrev SinkChildSource (S : SinkObject I J d) (k : occupiedPorts S) :=
  {i // cutSource S.1.1 (.inr S.1.2) (.inl (sinkChildPort S k).1) i}
abbrev SinkChildSink (S : SinkObject I J d) (k : occupiedPorts S) :=
  {j // cutSink S.1.1 (.inr S.1.2) (.inl (sinkChildPort S k).1) j}

noncomputable def sinkChild (S : SinkObject I J d) (k : occupiedPorts S) :
    SourceObject (SinkChildSource S k) (SinkChildSink S k) (occupiedColor (occupiedPorts S) k) :=
  ⟨(cutTable S.1.1 (.inr S.1.2) (.inl (sinkChildPort S k).1),
    sourceCutRoot S.1.1 (sinkChildPort S k).1 S.1.2),by
    have h := sink_port_source_branch S.2 (sinkChildPort S k)
    simpa only [sink_child_color] using h⟩

noncomputable def childTransposeIso (S : SinkObject I J d) (k : occupiedPorts S) :
    ColoredIso (coloring (transposeTable (sinkChild S k).1.1))
      (coloring (cutFamily (transposeTable S.1.1) S.1.2 (sinkChildPort S k))) :=
  transposeColoredIso (transposeCutIso S.1.1 (sinkChildPort S k).1 S.1.2).symm

theorem child_transpose_root (S : SinkObject I J d) (k : occupiedPorts S) :
    (childTransposeIso S k).sink (sinkChild S k).1.2=
      cutRoots (transposeTable S.1.1) S.1.2 (sinkChildPort S k) := by
  change (transposeCutIso S.1.1 (sinkChildPort S k).1 S.1.2).source.symm
    (sourceCutRoot S.1.1 (sinkChildPort S k).1 S.1.2)=_
  rw [←transpose_cut_root,Equiv.symm_apply_apply]
  rfl

variable [Fintype I] [Fintype J]

/-- The occupied colors reassemble all actual incoming cuts, including the empty root. -/
noncomputable def sinkChildrenIso (S : SinkObject I J d) :
    ColoredIso (coloring (assembleSinkObjects (occupiedPorts S) (sinkChild S)).1.1)
      (coloring S.1.1) :=
  (transposeColoredIso (sourceAttachmentIso
    (occupied_color_injective (occupiedPorts S))
    (fun k => source_branch_parent_color_absent (sinkChild S k).2)
    (cut_colors_injective (transposeTable S.1.1) S.1.2)
    (cut_parent_color_absent (transposeTable S.1.1) ((transpose_tree_iff S.1.1).mpr S.2.1) S.1.2)
    (sinkPortColors S).symm (childTransposeIso S) (child_transpose_root S)
    (sink_child_color S))).trans (actualSinkCutsIso S.1.1 S.2.1 S.1.2)

theorem sink_children_root (S : SinkObject I J d) :
    (sinkChildrenIso S).sink none=S.1.2 := rfl

theorem sink_children_grading (S : SinkObject I J d) :
    (∑ k,Fintype.card (SinkChildSource S k))=Fintype.card I := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (sinkChildrenIso S).source

end KroneckerCanonicalSinkChildren
end

/- Original module: KroneckerSinkDegreeAssembly -/
section
set_option autoImplicit false
namespace KroneckerSinkDegreeAssembly
open KroneckerFiniteColoredTables KroneckerColoredIncidenceIso KroneckerTableIsomorphisms
open KroneckerFiniteDegreePartitions KroneckerFiniteBranchClasses KroneckerCanonicalBranchClasses
open KroneckerSourceClassAssembly KroneckerSinkClassAssembly KroneckerBranchClassWeights
open KroneckerSinkAssemblyWeights KroneckerBranchWeights
attribute [local instance] Classical.propDecidable
open scoped BigOperators

abbrev SinkTuple (d : Fin 3) (n : ℕ) :=
  Σ s : Finset (OtherColors d),Σ a : DegreePartition s n,∀ k,SourceDegreeClass (a.1 k) (occupiedColor s k)

variable {d : Fin 3} {n : ℕ}

noncomputable def sinkTupleClass (p : SinkTuple d n) : SinkDegreeClass n d :=
  sinkClassOf (assembleSinkObjects p.1 (fun k => (p.2.2 k).out)) (by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using p.2.1.2)

theorem sink_root_color_transport {I J I' J' : Type}
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (f : ColoredIso (coloring T) (coloring U)) {r : J} {s : J'} (h : f.sink r=s) (c : Fin 3) :
    (∃ i,T.code i r=some c) ↔ ∃ i,U.code i s=some c := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨f.source i,?_⟩
    rw [←h,iso_preserves_code T U f]
    exact hi
  · rintro ⟨i,hi⟩
    obtain ⟨i,rfl⟩ := f.source.surjective i
    refine ⟨i,?_⟩
    rw [←h,iso_preserves_code T U f] at hi
    exact hi

/-- Even the occupied color subset is recovered by the actual assembled class. -/
theorem sink_tuple_class_injective : Function.Injective (sinkTupleClass (d:=d) (n:=n)) := by
  rintro ⟨s,a,q⟩ ⟨t,b,q'⟩ h
  obtain ⟨g,hg⟩ := (sink_class_of_eq_iff _ _ _ _).mp h
  have hst : s=t := by
    ext e
    rw [←sink_objects_occupied s (fun k => (q k).out) e,
      ←sink_objects_occupied t (fun k => (q' k).out) e]
    exact sink_root_color_transport g hg e.1
  subst t
  have hc := (sink_objects_class_iff _ _ _ _ _).mp h
  have hab : a=b := by
    apply Subtype.ext
    funext k
    obtain ⟨e,_⟩ := hc k
    simpa only [Fintype.card_fin] using Fintype.card_congr e.source
  subst b
  have hq : q=q' := by
    funext k
    have he : (Quotient.mk'' (q k).out : SourceDegreeClass (a.1 k) (occupiedColor s k))=
        Quotient.mk'' (q' k).out := Quotient.sound (hc k)
    simpa only [Quotient.out_eq'] using he
  subst q'
  rfl

theorem sink_tuple_class_weight {R : Type*} [CommSemiring R]
    (p : SinkTuple d n) (x : R) (y : Fin 3 → R) :
    sinkClassWeight x y (sinkTupleClass p)=
      if IsEmpty p.1 then y d else ∏ k,sourceClassWeight x y (p.2.2 k) := by
  rw [sinkTupleClass,canonical_sink_weight]
  dsimp only [assembleSinkObjects]
  rw [sink_assembly_weight]
  split_ifs
  · rfl
  · apply Finset.prod_congr rfl
    intro k _
    exact congrArg (sourceClassWeight x y) (Quotient.out_eq' (p.2.2 k))

end KroneckerSinkDegreeAssembly
end

/- Original module: KroneckerSinkTupleSurjectivity -/
section
set_option autoImplicit false
namespace KroneckerSinkTupleSurjectivity
open KroneckerFiniteColoredTables KroneckerFiniteBranchObjects KroneckerFiniteBranchClasses
open KroneckerCanonicalBranchClasses KroneckerColoredIncidenceIso KroneckerColoredTableTranspose
open KroneckerSourceClassAssembly KroneckerSinkClassAssembly KroneckerSinkDegreeAssembly
open KroneckerCanonicalSinkChildren KroneckerSourceTupleSurjectivity
open KroneckerFiniteDegreePartitions KroneckerAttachmentIsomorphisms KroneckerLeafDeletedSourceBranch
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {d : Fin 3} {n : ℕ}

noncomputable def sinkTupleOfObject (S : SinkObject (Fin n) (Fin (2*n+1)) d) : SinkTuple d n :=
  ⟨occupiedPorts S,⟨fun k => Fintype.card (SinkChildSource S k),by
    simpa only [Fintype.card_fin] using sink_children_grading S⟩,
    fun k => sourceClassOf (sinkChild S k) rfl⟩

/-- Every actual sink branch is recovered after canonical normalization of its actual cuts. -/
theorem sink_tuple_of_object_recovers (S : SinkObject (Fin n) (Fin (2*n+1)) d) :
    sinkTupleClass (sinkTupleOfObject S)=Quotient.mk'' S := by
  rw [←sink_class_of_canonical S]
  unfold sinkTupleClass
  apply (sink_class_of_eq_iff _ _ _ _).mpr
  have h : ∀ k,∃ e : ColoredIso (coloring ((sinkTupleOfObject S).2.2 k).out.1.1)
      (coloring (sinkChild S k).1.1),
      e.source ((sinkTupleOfObject S).2.2 k).out.1.2=(sinkChild S k).1.2 :=
    fun k => source_class_out_iso (sinkChild S k) rfl
  choose e he using h
  let g := transposeColoredIso (sourceAttachmentIso
    (T:=fun k => transposeTable ((sinkTupleOfObject S).2.2 k).out.1.1)
    (U:=fun k => transposeTable (sinkChild S k).1.1)
    (r:=fun k => ((sinkTupleOfObject S).2.2 k).out.1.2)
    (s:=fun k => (sinkChild S k).1.2)
    (occupied_color_injective (occupiedPorts S))
    (fun k => source_branch_parent_color_absent ((sinkTupleOfObject S).2.2 k).out.2)
    (occupied_color_injective (occupiedPorts S))
    (fun k => source_branch_parent_color_absent (sinkChild S k).2)
    (Equiv.refl (occupiedPorts S)) (fun k => transposeColoredIso (e k)) he (fun _ => rfl))
  refine ⟨g.trans (sinkChildrenIso S),?_⟩
  change (sinkChildrenIso S).sink (g.sink none)=S.1.2
  have hg : g.sink none=none := rfl
  rw [hg,sink_children_root]

theorem sink_tuple_class_surjective : Function.Surjective (sinkTupleClass (d:=d) (n:=n)) := by
  intro q
  induction q using Quotient.inductionOn with | _ S =>
    exact ⟨sinkTupleOfObject S,sink_tuple_of_object_recovers S⟩

/-- This equivalence includes the occupied color set and all child degrees as recoverable data. -/
noncomputable def sinkDegreeEquiv : SinkTuple d n ≃ SinkDegreeClass n d :=
  Equiv.ofBijective sinkTupleClass ⟨sink_tuple_class_injective,sink_tuple_class_surjective⟩

end KroneckerSinkTupleSurjectivity
end

/- Original module: KroneckerSinkClassConvolution -/
section
set_option autoImplicit false
namespace KroneckerSinkClassConvolution
open KroneckerFiniteBranchClasses KroneckerFiniteDegreePartitions KroneckerSourceClassAssembly
open KroneckerSinkClassAssembly KroneckerSinkDegreeAssembly KroneckerSinkTupleSurjectivity
open KroneckerBranchClassWeights
attribute [local instance] Classical.propDecidable
open scoped BigOperators


/-- Each occupied subset contributes its actual weighted child convolution. -/
theorem sink_class_weight_convolution {R : Type*} [CommSemiring R]
    (d : Fin 3) (n : ℕ) (x : R) (y : Fin 3 → R) :
    (∑ q : SinkDegreeClass n d,sinkClassWeight x y q)=
      ∑ s : Finset (OtherColors d),∑ a : DegreePartition s n,
        if IsEmpty s then (Fintype.card (∀ k : s,SourceDegreeClass (a.1 k) (occupiedColor s k)) : R)*y d
        else ∏ k,∑ q : SourceDegreeClass (a.1 k) (occupiedColor s k),sourceClassWeight x y q := by
  calc
    _ = ∑ p : SinkTuple d n,sinkClassWeight x y (sinkTupleClass p) :=
      (Equiv.sum_comp (sinkDegreeEquiv (d:=d) (n:=n)) _).symm
    _ = _ := by
      simp only [sink_tuple_class_weight,SinkTuple,Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro a _
      by_cases hs : IsEmpty s
      · simp only [ite_eq_left hs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      · simp only [ite_eq_right hs]
        exact (Fintype.prod_sum (fun k (q : SourceDegreeClass (a.1 k) (occupiedColor s k)) =>
          sourceClassWeight x y q)).symm

end KroneckerSinkClassConvolution
end

/- Original module: KroneckerSourceClassConvolution -/
section
set_option autoImplicit false
namespace KroneckerSourceClassConvolution
open KroneckerFiniteBranchClasses KroneckerFiniteDegreePartitions KroneckerSourceClassAssembly
open KroneckerSourceDegreeAssembly KroneckerSourceTupleSurjectivity KroneckerBranchClassWeights
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable (d : Fin 3) (n : ℕ)


theorem source_class_weight_convolution {R : Type*} [CommSemiring R]
    (x : R) (y : Fin 3 → R) :
    (∑ q : SourceDegreeClass (n+1) d,sourceClassWeight x y q)=
      x*∑ a : DegreePartition (OtherColors d) n,
        ∏ k,∑ q : SinkDegreeClass (a.1 k) k.1,sinkClassWeight x y q := by
  classical
  calc
    _ = ∑ p : SourceTuple d n,sourceClassWeight x y (sourceTupleClass p) :=
      (Equiv.sum_comp (sourceDegreeEquiv (d:=d) (n:=n)) (sourceClassWeight x y)).symm
    _ = _ := by
      simp only [source_tuple_class_weight,SourceTuple,Fintype.sum_sigma,←Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact (Fintype.prod_sum (fun k (q : SinkDegreeClass (a.1 k) k.1) => sinkClassWeight x y q)).symm

end KroneckerSourceClassConvolution
end

/- Original module: KroneckerActualBranchSeries -/
section
set_option autoImplicit false
namespace KroneckerActualBranchSeries
open KroneckerFiniteBranchClasses KroneckerBranchClassWeights
open KroneckerSourceClassConvolution KroneckerSourceClassAssembly
open KroneckerPartitionCauchyProduct
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

/-- Coefficients are sums over actual finite colored branch isomorphism classes. -/
noncomputable def sourceSeries (y : Fin 3 → R) (d : Fin 3) : PowerSeries R :=
  PowerSeries.mk (fun n => ∑ q : SourceDegreeClass n d,sourceClassWeight 1 y q)
noncomputable def sinkSeries (y : Fin 3 → R) (d : Fin 3) : PowerSeries R :=
  PowerSeries.mk (fun n => ∑ q : SinkDegreeClass n d,sinkClassWeight 1 y q)

theorem source_series_coeff (y : Fin 3 → R) (d : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (sourceSeries y d)=∑ q : SourceDegreeClass n d,sourceClassWeight 1 y q :=
  PowerSeries.coeff_mk n _
theorem sink_series_coeff (y : Fin 3 → R) (d : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (sinkSeries y d)=∑ q : SinkDegreeClass n d,sinkClassWeight 1 y q :=
  PowerSeries.coeff_mk n _

theorem source_series_constant (y : Fin 3 → R) (d : Fin 3) :
    PowerSeries.constantCoeff (sourceSeries y d)=0 := by
  let : IsEmpty (SourceDegreeClass 0 d) := Fintype.card_eq_zero_iff.mp (source_degree_zero d)
  rw [←PowerSeries.coeff_zero_eq_constantCoeff,source_series_coeff]
  simp

/-- The source grammar follows from the degree-preserving actual class bijection. -/
theorem source_series_equation (y : Fin 3 → R) (d : Fin 3) :
    sourceSeries y d=PowerSeries.X * ∏ k : OtherColors d,sinkSeries y k.1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff,source_series_constant]
  | succ n =>
    rw [show (PowerSeries.X : PowerSeries R)=PowerSeries.X^1 by rw [pow_one],
      PowerSeries.coeff_X_pow_mul,coeff_product_partitions,source_series_coeff]
    simpa only [sink_series_coeff,one_mul] using source_class_weight_convolution d n (1 : R) y

theorem source_series_counts (d : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (sourceSeries (fun _ => (1 : R)) d)=
      (Fintype.card (SourceDegreeClass n d) : R) := by
  rw [source_series_coeff,source_class_weight_sum_at_one]
theorem sink_series_counts (d : Fin 3) (n : ℕ) :
    PowerSeries.coeff n (sinkSeries (fun _ => (1 : R)) d)=
      (Fintype.card (SinkDegreeClass n d) : R) := by
  rw [sink_series_coeff,sink_class_weight_sum_at_one]

end KroneckerActualBranchSeries
end
end

