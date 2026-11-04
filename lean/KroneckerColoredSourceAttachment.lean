import KroneckerFiniteColoredTables

/- Original module: KroneckerRelationalColoredTables -/
section
set_option autoImplicit false
namespace KroneckerRelationalColoredTables
open KroneckerFiniteColoredTables
attribute [local instance] Classical.propDecidable

variable {I J : Type}

/-- An edge-color relation must be functional at each pair as well as proper at both ends. -/
structure ProperEdgeRelation (E : I → J → Fin 3 → Prop) : Prop where
  functional : ∀ i j d e,E i j d → E i j e → d=e
  source : ∀ i j k d,E i j d → E i k d → j=k
  sink : ∀ i k j d,E i j d → E k j d → i=k

noncomputable def relationCode (E : I → J → Fin 3 → Prop) (i : I) (j : J) : Option (Fin 3) :=
  if h : ∃ d,E i j d then some (Classical.choose h) else none

theorem relation_code_iff (E : I → J → Fin 3 → Prop) (h : ProperEdgeRelation E)
    (i : I) (j : J) (d : Fin 3) : relationCode E i j=some d ↔ E i j d := by
  unfold relationCode
  split_ifs with he
  · constructor
    · intro hd
      simpa only [Option.some.inj hd] using Classical.choose_spec he
    · intro hd
      exact congrArg some (h.functional i j _ d (Classical.choose_spec he) hd)
  · simp only [false_iff]
    exact fun hd => he ⟨d,hd⟩

noncomputable def tableOfRelation (E : I → J → Fin 3 → Prop)
    (h : ProperEdgeRelation E) : ColoredTable I J where
  code := relationCode E
  atSource := by
    intro i j k d hj hk
    exact h.source i j k d ((relation_code_iff E h i j d).mp hj)
      ((relation_code_iff E h i k d).mp hk)
  atSink := by
    intro i k j d hi hk
    exact h.sink i k j d ((relation_code_iff E h i j d).mp hi)
      ((relation_code_iff E h k j d).mp hk)

theorem relational_table_incidence (E : I → J → Fin 3 → Prop)
    (h : ProperEdgeRelation E) (i : I) (j : J) :
    Incidence (tableOfRelation E h) i j ↔ ∃ d,E i j d := by
  simp only [Incidence,tableOfRelation,relation_code_iff E h]

theorem table_relation_roundtrip (T : ColoredTable I J) :
    tableOfRelation (fun i j d => T.code i j=some d)
      ⟨fun _ _ _ _ h k => Option.some.inj (h.symm.trans k),T.atSource,T.atSink⟩=T := by
  apply table_ext
  funext i j
  apply Option.ext
  intro d
  exact relation_code_iff (fun i j d => T.code i j=some d)
    ⟨fun _ _ _ _ h k => Option.some.inj (h.symm.trans k),T.atSource,T.atSink⟩ i j d

end KroneckerRelationalColoredTables
end

/- Original module: KroneckerSourceAttachmentEdges -/
section
set_option autoImplicit false
namespace KroneckerSourceAttachmentEdges
open KroneckerFiniteColoredTables KroneckerRelationalColoredTables

variable {K : Type} {I J : K → Type}

/-- Adjoin one source and connect it to one distinguished sink in each disjoint component. -/
inductive AttachEdge (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3) :
    Option (Σ k,I k) → (Σ k,J k) → Fin 3 → Prop
  | internal (k : K) (i : I k) (j : J k) (d : Fin 3) (h : (T k).code i j=some d) :
      AttachEdge T r c (some ⟨k,i⟩) ⟨k,j⟩ d
  | root (k : K) : AttachEdge T r c none ⟨k,r k⟩ (c k)

variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)

theorem attach_root_edge (k : K) (j : J k) (d : Fin 3) :
    AttachEdge T r c none ⟨k,j⟩ d ↔ j=r k ∧ c k=d := by
  constructor
  · intro h; cases h; exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩; exact AttachEdge.root k

theorem attach_internal_edge (k : K) (i : I k) (j : J k) (d : Fin 3) :
    AttachEdge T r c (some ⟨k,i⟩) ⟨k,j⟩ d ↔ (T k).code i j=some d := by
  constructor
  · intro h; cases h with | internal _ _ _ _ h => exact h
  · exact AttachEdge.internal k i j d

theorem attach_component_index {p : Σ k,I k} {q : Σ k,J k} {d : Fin 3}
    (h : AttachEdge T r c (some p) q d) : p.1=q.1 := by
  cases h; rfl

/-- Distinct port colors and absence of each parent color are exactly the local properness conditions. -/
theorem attachment_proper (hc : Function.Injective c)
    (hr : ∀ k i,(T k).code i (r k)≠some (c k)) : ProperEdgeRelation (AttachEdge T r c) := by
  constructor
  · intro i j d e h g
    cases h with
    | root k =>
      have hg := (attach_root_edge T r c k (r k) e).mp g
      exact hg.2
    | internal k i j d h =>
      exact Option.some.inj (h.symm.trans ((attach_internal_edge T r c k i j e).mp g))
  · intro i j l d h g
    cases h with
    | root k =>
      rcases l with ⟨l,t⟩
      obtain ⟨ht,he⟩ := (attach_root_edge T r c l t (c k)).mp g
      have hl : l=k := hc he
      subst l; subst t; rfl
    | internal k i j d h =>
      rcases l with ⟨l,t⟩
      have hl : k=l := attach_component_index T r c g
      subst l
      exact congrArg (Sigma.mk k) ((T k).atSource i j t d h
        ((attach_internal_edge T r c k i t d).mp g))
  · intro i l j d h g
    cases h with
    | root k =>
      cases l with
      | none => rfl
      | some p =>
        rcases p with ⟨l,t⟩
        have hl : l=k := attach_component_index T r c g
        subst l
        exact False.elim (hr k t ((attach_internal_edge T r c k t (r k) (c k)).mp g))
    | internal k i j d h =>
      cases l with
      | none =>
        obtain ⟨hj,he⟩ := (attach_root_edge T r c k j d).mp g
        subst j
        exact False.elim (hr k i (h.trans (congrArg some he.symm)))
      | some p =>
        rcases p with ⟨l,t⟩
        have hl : l=k := attach_component_index T r c g
        subst l
        exact congrArg (fun i => some (Sigma.mk k i)) ((T k).atSink i t j d h
          ((attach_internal_edge T r c k t j d).mp g))

end KroneckerSourceAttachmentEdges
end

/- Original module: KroneckerColoredSourceAttachment -/
section
set_option autoImplicit false
namespace KroneckerColoredSourceAttachment
open KroneckerFiniteColoredTables KroneckerRelationalColoredTables KroneckerSourceAttachmentEdges
attribute [local instance] Classical.propDecidable

variable {K : Type} {I J : K → Type}
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))

noncomputable def sourceAttachment : ColoredTable (Option (Σ k,I k)) (Σ k,J k) :=
  tableOfRelation (AttachEdge T r c) (attachment_proper T r c hc hr)

theorem attachment_code_iff (i : Option (Σ k,I k)) (j : Σ k,J k) (d : Fin 3) :
    (sourceAttachment T r c hc hr).code i j=some d ↔ AttachEdge T r c i j d :=
  relation_code_iff _ (attachment_proper T r c hc hr) i j d

theorem attachment_root_code (k : K) (j : J k) :
    (sourceAttachment T r c hc hr).code none ⟨k,j⟩=
      if j=r k then some (c k) else none := by
  apply Option.ext
  intro d
  rw [attachment_code_iff,attach_root_edge]
  by_cases h : j=r k <;> simp [h]

theorem attachment_internal_code (k : K) (i : I k) (j : J k) :
    (sourceAttachment T r c hc hr).code (some ⟨k,i⟩) ⟨k,j⟩=(T k).code i j := by
  apply Option.ext
  intro d
  rw [attachment_code_iff,attach_internal_edge]

theorem attachment_cross_code {k l : K} (h : k≠l) (i : I k) (j : J l) :
    (sourceAttachment T r c hc hr).code (some ⟨k,i⟩) ⟨l,j⟩=none := by
  cases he : (sourceAttachment T r c hc hr).code (some ⟨k,i⟩) ⟨l,j⟩ with
  | none => rfl
  | some d =>
    exact False.elim (h (attach_component_index T r c
      ((attachment_code_iff T r c hc hr _ _ d).mp he)))

theorem attachment_root_incidence (k : K) (j : J k) :
    Incidence (sourceAttachment T r c hc hr) none ⟨k,j⟩ ↔ j=r k := by
  simp only [Incidence,attachment_root_code]
  by_cases h : j=r k <;> simp [h]

theorem attachment_internal_incidence (k : K) (i : I k) (j : J k) :
    Incidence (sourceAttachment T r c hc hr) (some ⟨k,i⟩) ⟨k,j⟩ ↔ Incidence (T k) i j := by
  simp only [Incidence,attachment_internal_code]

end KroneckerColoredSourceAttachment
end
