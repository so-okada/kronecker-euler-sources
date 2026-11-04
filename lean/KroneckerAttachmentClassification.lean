import KroneckerSourceAttachmentTree
import KroneckerColoredCutTransport

/- Original module: KroneckerAttachmentCutComponents -/
section
set_option autoImplicit false
namespace KroneckerAttachmentCutComponents
open SimpleGraph KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerColoredSourceAttachment KroneckerSourceAttachmentConnected KroneckerSourceAttachmentTree
open KroneckerTreeCutComponents KroneckerRootedEdgePartition
attribute [local instance] Classical.propDecidable

variable {K : Type} {I J : K → Type}
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))

noncomputable def attachmentDeletedHom (k l : K) : incidenceGraph (Incidence (T l)) →g
    (incidenceGraph (Incidence (sourceAttachment T r c hc hr))).deleteEdges
      {s(Sum.inl none,Sum.inr ⟨k,r k⟩)} where
  toFun := attachmentVertex l
  map_rel' := by
    intro u v h
    apply deleteEdges_adj.mpr
    refine ⟨(attachmentHom T r c hc hr l).map_rel' h,?_⟩
    cases u <;> cases v <;> simp [attachmentVertex]

theorem child_in_attachment_cut (hT : ∀ k,(incidenceGraph (Incidence (T k))).Connected)
    (k : K) (v : I k ⊕ J k) :
    cutSide (incidenceGraph (Incidence (sourceAttachment T r c hc hr)))
      (.inl none) (.inr ⟨k,r k⟩) (attachmentVertex k v) :=
  (hT k (.inr (r k)) v).map (attachmentDeletedHom T r c hc hr k k)

/-- Cutting a new attachment edge recovers exactly its own component, with no additional vertices. -/
theorem attachment_cut_index_iff [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
    (hT : ∀ k,(incidenceGraph (Incidence (T k))).IsTree) (k l : K) (v : I l ⊕ J l) :
    cutSide (incidenceGraph (Incidence (sourceAttachment T r c hc hr)))
      (.inl none) (.inr ⟨k,r k⟩) (attachmentVertex l v) ↔ k=l := by
  have ha : ∀ k,(incidenceGraph (Incidence (sourceAttachment T r c hc hr))).Adj
      (.inl none) (.inr ⟨k,r k⟩) := fun k => (attachment_root_incidence T r c hc hr k (r k)).mpr rfl
  constructor
  · intro h
    have he := branch_neighbor_unique (source_attachment_tree T r c hc hr hT) (ha k) (ha l)
      h (child_in_attachment_cut T r c hc hr (fun k => (hT k).connected) l v)
    exact congrArg Sigma.fst (Sum.inr.inj he)
  · intro he
    subst l
    exact child_in_attachment_cut T r c hc hr (fun k => (hT k).connected) k v

end KroneckerAttachmentCutComponents
end

/- Original module: KroneckerAttachmentCutRecovery -/
section
set_option autoImplicit false
namespace KroneckerAttachmentCutRecovery
open SimpleGraph KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerColoredSourceAttachment KroneckerSourceAttachmentTree KroneckerAttachmentCutComponents
open KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches KroneckerTreeCutComponents
open KroneckerColoredIncidenceIso KroneckerTableIsomorphisms

variable {K : Type} {I J : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))
variable (hT : ∀ k,(incidenceGraph (Incidence (T k))).IsTree)

noncomputable def cutAttachmentSources (k : K) : I k ≃
    {i // cutSource (sourceAttachment T r c hc hr) (.inl none) (.inr ⟨k,r k⟩) i} := by
  let f : I k → {i // cutSource (sourceAttachment T r c hc hr) (.inl none) (.inr ⟨k,r k⟩) i} :=
    fun i => ⟨some ⟨k,i⟩,child_in_attachment_cut T r c hc hr (fun k => (hT k).connected) k (.inl i)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact eq_of_heq (Sigma.mk.inj (Option.some.inj (congrArg Subtype.val h))).2
  · rintro ⟨i,hi⟩
    cases i with
    | none =>
      exact False.elim (tree_cut_excludes_source (source_attachment_tree T r c hc hr hT)
        (show (incidenceGraph (Incidence (sourceAttachment T r c hc hr))).Adj
          (.inl none) (.inr ⟨k,r k⟩) from (attachment_root_incidence T r c hc hr k (r k)).mpr rfl) hi)
    | some p =>
      rcases p with ⟨l,i⟩
      have he : k=l := (attachment_cut_index_iff T r c hc hr hT k l (.inl i)).mp hi
      subst l
      exact ⟨i,rfl⟩

noncomputable def cutAttachmentSinks (k : K) : J k ≃
    {j // cutSink (sourceAttachment T r c hc hr) (.inl none) (.inr ⟨k,r k⟩) j} := by
  let f : J k → {j // cutSink (sourceAttachment T r c hc hr) (.inl none) (.inr ⟨k,r k⟩) j} :=
    fun j => ⟨⟨k,j⟩,child_in_attachment_cut T r c hc hr (fun k => (hT k).connected) k (.inr j)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
  · rintro ⟨⟨l,j⟩,hj⟩
    have he : k=l := (attachment_cut_index_iff T r c hc hr hT k l (.inr j)).mp hj
    subst l
    exact ⟨j,rfl⟩

/-- The cut of an arbitrary assembled family is its original colored component. -/
noncomputable def cutAttachmentIso (hT : ∀ k,(incidenceGraph (Incidence (T k))).IsTree)
    (k : K) : ColoredIso (coloring (T k))
    (coloring (cutTable (sourceAttachment T r c hc hr) (.inl none) (.inr ⟨k,r k⟩))) :=
  isoOfCode _ _ (cutAttachmentSources T r c hc hr hT k) (cutAttachmentSinks T r c hc hr hT k)
    (fun i j => attachment_internal_code T r c hc hr k i j)

theorem cut_attachment_recovers_root (k : K) :
    (cutAttachmentIso T r c hc hr hT k).sink (r k)=
      sinkCutRoot (sourceAttachment T r c hc hr) none ⟨k,r k⟩ := by
  apply Subtype.ext
  rfl

include hT in
theorem cut_attachment_recovers_component (k : K) :
    ∃ e : ColoredIso (coloring (T k))
      (coloring (cutTable (sourceAttachment T r c hc hr) (.inl none) (.inr ⟨k,r k⟩))),
      e.sink (r k)=sinkCutRoot (sourceAttachment T r c hc hr) none ⟨k,r k⟩ :=
  ⟨cutAttachmentIso T r c hc hr hT k,cut_attachment_recovers_root T r c hc hr hT k⟩

end KroneckerAttachmentCutRecovery
end

/- Original module: KroneckerAttachmentIsomorphisms -/
section
set_option autoImplicit false
namespace KroneckerAttachmentIsomorphisms
open KroneckerFiniteColoredTables KroneckerColoredSourceAttachment
open KroneckerColoredIncidenceIso KroneckerTableIsomorphisms
attribute [local instance] Classical.propDecidable

variable {K L : Type} {I J : K → Type} {I' J' : L → Type}
variable {T : ∀ k,ColoredTable (I k) (J k)} {U : ∀ l,ColoredTable (I' l) (J' l)}
variable {r : ∀ k,J k} {s : ∀ l,J' l} {c : K → Fin 3} {c' : L → Fin 3}

/-- Component isomorphisms and a color-preserving port bijection assemble to an actual colored isomorphism. -/
noncomputable def sourceAttachmentIso
    (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))
    (hc' : Function.Injective c') (hr' : ∀ k i,(U k).code i (s k)≠some (c' k))
    (p : K ≃ L) (e : ∀ k,ColoredIso (coloring (T k)) (coloring (U (p k))))
    (he : ∀ k,(e k).sink (r k)=s (p k)) (hp : ∀ k,c' (p k)=c k) :
    ColoredIso (coloring (sourceAttachment T r c hc hr))
      (coloring (sourceAttachment U s c' hc' hr')) := by
  apply isoOfCode _ _ (Equiv.sigmaCongr p (fun k => (e k).source)).optionCongr
    (Equiv.sigmaCongr p (fun k => (e k).sink))
  intro i j
  rcases j with ⟨l,j⟩
  cases i with
  | none =>
    change (sourceAttachment U s c' hc' hr').code none ⟨p l,(e l).sink j⟩=_
    rw [attachment_root_code,attachment_root_code]
    have hi : (e l).sink j=s (p l) ↔ j=r l := by rw [←he l,(e l).sink.injective.eq_iff]
    simp only [hi,hp]
  | some i =>
    rcases i with ⟨k,i⟩
    change (sourceAttachment U s c' hc' hr').code (some ⟨p k,(e k).source i⟩)
      ⟨p l,(e l).sink j⟩=_
    by_cases h : k=l
    · subst l
      rw [attachment_internal_code,attachment_internal_code]
      exact iso_preserves_code (T k) (U (p k)) (e k) i j
    · rw [attachment_cross_code _ _ _ _ _ (fun he => h (p.injective he)),
        attachment_cross_code _ _ _ _ _ h]

theorem source_attachment_iso_root
    (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))
    (hc' : Function.Injective c') (hr' : ∀ k i,(U k).code i (s k)≠some (c' k))
    (p : K ≃ L) (e : ∀ k,ColoredIso (coloring (T k)) (coloring (U (p k))))
    (he : ∀ k,(e k).sink (r k)=s (p k)) (hp : ∀ k,c' (p k)=c k) :
    (sourceAttachmentIso hc hr hc' hr' p e he hp).source none=none := rfl


end KroneckerAttachmentIsomorphisms
end

/- Original module: KroneckerAttachmentPortRecovery -/
section
set_option autoImplicit false
namespace KroneckerAttachmentPortRecovery
open KroneckerFiniteColoredTables KroneckerColoredSourceAttachment
open KroneckerColoredIncidenceIso KroneckerTableIsomorphisms
attribute [local instance] Classical.propDecidable

variable {K : Type} {I J I' J' : K → Type}
variable {T : ∀ k,ColoredTable (I k) (J k)} {U : ∀ k,ColoredTable (I' k) (J' k)}
variable {r : ∀ k,J k} {s : ∀ k,J' k} {c : K → Fin 3}
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))
variable (hr' : ∀ k i,(U k).code i (s k)≠some (c k))

/-- Proper coloring forces a rooted isomorphism to preserve each prescribed color port. -/
theorem source_attachment_port_fixed
    (e : ColoredIso (coloring (sourceAttachment T r c hc hr))
      (coloring (sourceAttachment U s c hc hr')))
    (he : e.source none=none) (k : K) : e.sink ⟨k,r k⟩=⟨k,s k⟩ := by
  have h₁ := iso_preserves_code _ _ e none ⟨k,r k⟩
  rw [he,attachment_root_code T r c hc hr,ite_eq_left rfl] at h₁
  have h₂ : (sourceAttachment U s c hc hr').code none ⟨k,s k⟩=some (c k) := by
    rw [attachment_root_code,ite_eq_left rfl]
  exact (sourceAttachment U s c hc hr').atSource none _ _ _ h₁ h₂

end KroneckerAttachmentPortRecovery
end

/- Original module: KroneckerPointedCutIsomorphisms -/
section
set_option autoImplicit false
namespace KroneckerPointedCutIsomorphisms
open KroneckerFiniteColoredTables KroneckerColoredIncidenceIso KroneckerTableIsomorphisms
open KroneckerColoredCutTransport KroneckerIncomingSourceBranches KroneckerOutgoingSinkBranches

variable {I J I' J' : Type} {T : ColoredTable I J} {U : ColoredTable I' J'}

/-- Endpoint-aware transport avoids suppressing the root equations in a cut isomorphism. -/
noncomputable def pointedSinkCutIso (e : ColoredIso (coloring T) (coloring U))
    {i : I} {j : J} {i' : I'} {j' : J'} (hi : e.source i=i') (hj : e.sink j=j') :
    ColoredIso (coloring (cutTable T (.inl i) (.inr j)))
      (coloring (cutTable U (.inl i') (.inr j'))) := by
  let s : {k // cutSource T (.inl i) (.inr j) k} ≃
      {k // cutSource U (.inl i') (.inr j') k} :=
    Equiv.subtypeEquiv e.source (fun k => by
      rw [←hi,←hj]
      exact (cut_side_iso_iff e.graphIso (.inl i) (.inr j) (.inl k)).symm)
  let t : {l // cutSink T (.inl i) (.inr j) l} ≃
      {l // cutSink U (.inl i') (.inr j') l} :=
    Equiv.subtypeEquiv e.sink (fun l => by
      rw [←hi,←hj]
      exact (cut_side_iso_iff e.graphIso (.inl i) (.inr j) (.inr l)).symm)
  exact isoOfCode _ _ s t (fun k l => iso_preserves_code T U e k.1 l.1)

theorem pointed_sink_cut_root (e : ColoredIso (coloring T) (coloring U))
    {i : I} {j : J} {i' : I'} {j' : J'} (hi : e.source i=i') (hj : e.sink j=j') :
    (pointedSinkCutIso e hi hj).sink (sinkCutRoot T i j)=sinkCutRoot U i' j' := by
  apply Subtype.ext
  exact hj

end KroneckerPointedCutIsomorphisms
end

/- Original module: KroneckerAttachmentClassification -/
section
set_option autoImplicit false
namespace KroneckerAttachmentClassification
open KroneckerFiniteColoredTables KroneckerBipartiteIncidence KroneckerColoredIncidenceIso
open KroneckerColoredSourceAttachment KroneckerAttachmentIsomorphisms
open KroneckerAttachmentCutRecovery KroneckerAttachmentPortRecovery KroneckerPointedCutIsomorphisms

variable {K : Type} {I J I' J' : K → Type}
variable [Fintype K] [∀ k,Fintype (I k)] [∀ k,Fintype (J k)]
variable [∀ k,Fintype (I' k)] [∀ k,Fintype (J' k)]
variable (T : ∀ k,ColoredTable (I k) (J k)) (U : ∀ k,ColoredTable (I' k) (J' k))
variable (r : ∀ k,J k) (s : ∀ k,J' k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))
variable (hs : ∀ k i,(U k).code i (s k)≠some (c k))
variable (hT : ∀ k,(incidenceGraph (Incidence (T k))).IsTree)
variable (hU : ∀ k,(incidenceGraph (Incidence (U k))).IsTree)

noncomputable def recoverAttachmentIso
    (hT : ∀ k,(incidenceGraph (Incidence (T k))).IsTree)
    (hU : ∀ k,(incidenceGraph (Incidence (U k))).IsTree)
    (e : ColoredIso (coloring (sourceAttachment T r c hc hr))
      (coloring (sourceAttachment U s c hc hs))) (he : e.source none=none) (k : K) :
    ColoredIso (coloring (T k)) (coloring (U k)) :=
  (cutAttachmentIso T r c hc hr hT k).trans
    ((pointedSinkCutIso e he (source_attachment_port_fixed hc hr hs e he k)).trans
      (cutAttachmentIso U s c hc hs hU k).symm)

theorem recovered_attachment_root
    (e : ColoredIso (coloring (sourceAttachment T r c hc hr))
      (coloring (sourceAttachment U s c hc hs))) (he : e.source none=none) (k : K) :
    (recoverAttachmentIso T U r s c hc hr hs hT hU e he k).sink (r k)=s k := by
  apply (cutAttachmentIso U s c hc hs hU k).sink.injective
  change (cutAttachmentIso U s c hc hs hU k).sink
    ((cutAttachmentIso U s c hc hs hU k).sink.symm
      ((pointedSinkCutIso e he (source_attachment_port_fixed hc hr hs e he k)).sink
        ((cutAttachmentIso T r c hc hr hT k).sink (r k))))=_
  rw [Equiv.apply_symm_apply,cut_attachment_recovers_root,pointed_sink_cut_root,
    cut_attachment_recovers_root]

include hT hU

/-- The rooted colored isomorphism class of an assembly is determined exactly by its pointed component classes. -/
theorem source_attachment_iso_iff :
    (∃ e : ColoredIso (coloring (sourceAttachment T r c hc hr))
      (coloring (sourceAttachment U s c hc hs)),e.source none=none) ↔
    ∀ k,∃ e : ColoredIso (coloring (T k)) (coloring (U k)),e.sink (r k)=s k := by
  constructor
  · rintro ⟨e,he⟩ k
    exact ⟨recoverAttachmentIso T U r s c hc hr hs hT hU e he k,
      recovered_attachment_root T U r s c hc hr hs hT hU e he k⟩
  · intro h
    choose e he using h
    exact ⟨sourceAttachmentIso hc hr hc hs (Equiv.refl K) e he (fun _ => rfl),rfl⟩

end KroneckerAttachmentClassification
end
