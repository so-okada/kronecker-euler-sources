import KroneckerColoredSourceAttachment

/- Original module: KroneckerSourceAttachmentConnected -/
section
set_option autoImplicit false
namespace KroneckerSourceAttachmentConnected
open SimpleGraph KroneckerFiniteColoredTables KroneckerBipartiteIncidence
open KroneckerColoredSourceAttachment

variable {K : Type} {I J : K → Type}
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))

def attachmentVertex (k : K) : I k ⊕ J k → Option (Σ k,I k) ⊕ (Σ k,J k)
  | .inl i => .inl (some ⟨k,i⟩)
  | .inr j => .inr ⟨k,j⟩

noncomputable def attachmentHom (k : K) : incidenceGraph (Incidence (T k)) →g
    incidenceGraph (Incidence (sourceAttachment T r c hc hr)) where
  toFun := attachmentVertex k
  map_rel' := by
    intro u v h
    cases u <;> cases v
    · exact h
    · exact (attachment_internal_incidence T r c hc hr _ _ _).mpr h
    · exact (attachment_internal_incidence T r c hc hr _ _ _).mpr h
    · exact h

theorem attachment_vertex_injective (k : K) :
    Function.Injective (attachmentVertex (I:=I) (J:=J) k) := by
  intro u v h
  cases u <;> cases v <;> simp_all [attachmentVertex]

/-- Arbitrary connected components give a connected attachment, including the empty family. -/
theorem source_attachment_connected
    (hT : ∀ k,(incidenceGraph (Incidence (T k))).Connected) :
    (incidenceGraph (Incidence (sourceAttachment T r c hc hr))).Connected := by
  let G := incidenceGraph (Incidence (sourceAttachment T r c hc hr))
  have hp : ∀ k (v : I k ⊕ J k),G.Reachable (.inl none) (attachmentVertex k v) := by
    intro k v
    have he : G.Adj (.inl none) (.inr ⟨k,r k⟩) :=
      (attachment_root_incidence T r c hc hr k (r k)).mpr rfl
    exact he.reachable.trans ((hT k (.inr (r k)) v).map (attachmentHom T r c hc hr k))
  have hv : ∀ v,G.Reachable (.inl none) v := by
    intro v
    cases v with
    | inl i => cases i with
      | none => exact Reachable.refl _
      | some p => exact hp p.1 (.inl p.2)
    | inr j => exact hp j.1 (.inr j.2)
  exact { preconnected := fun u v => (hv u).symm.trans (hv v),nonempty := ⟨.inl none⟩ }

end KroneckerSourceAttachmentConnected
end

/- Original module: KroneckerSourceAttachmentNeighbors -/
section
set_option autoImplicit false
namespace KroneckerSourceAttachmentNeighbors
open KroneckerFiniteColoredTables KroneckerSourceAttachmentEdges KroneckerColoredSourceAttachment
attribute [local instance] Classical.propDecidable

variable {K : Type} {I J : K → Type}
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))

noncomputable def attachmentRootNeighbors :
    {j // Incidence (sourceAttachment T r c hc hr) none j} ≃ K where
  toFun j := j.1.1
  invFun k := ⟨⟨k,r k⟩,(attachment_root_incidence T r c hc hr k (r k)).mpr rfl⟩
  left_inv := by
    rintro ⟨⟨k,j⟩,hj⟩
    have he := (attachment_root_incidence T r c hc hr k j).mp hj
    subst j; rfl
  right_inv k := rfl

noncomputable def attachmentInternalNeighbors (k : K) (i : I k) :
    {j // Incidence (T k) i j} ≃
      {j // Incidence (sourceAttachment T r c hc hr) (some ⟨k,i⟩) j} := by
  let f : {j // Incidence (T k) i j} →
      {j // Incidence (sourceAttachment T r c hc hr) (some ⟨k,i⟩) j} :=
    fun j => ⟨⟨k,j.1⟩,(attachment_internal_incidence T r c hc hr k i j).mpr j.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro j l h
    apply Subtype.ext
    exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
  · rintro ⟨⟨l,j⟩,d,h⟩
    have he : k=l := attach_component_index T r c
      ((attachment_code_iff T r c hc hr _ _ d).mp h)
    subst l
    refine ⟨⟨j,⟨d,?_⟩⟩,rfl⟩
    exact (attachment_internal_code T r c hc hr k i j).symm.trans h

theorem attachment_root_degree [Fintype K] [∀ k,Fintype (J k)] :
    Fintype.card {j // Incidence (sourceAttachment T r c hc hr) none j}=Fintype.card K :=
  Fintype.card_congr (attachmentRootNeighbors T r c hc hr)

theorem attachment_internal_degree [Fintype K] [∀ k,Fintype (J k)] (k : K) (i : I k) :
    Fintype.card {j // Incidence (sourceAttachment T r c hc hr) (some ⟨k,i⟩) j}=
      Fintype.card {j // Incidence (T k) i j} :=
  (Fintype.card_congr (attachmentInternalNeighbors T r c hc hr k i)).symm

end KroneckerSourceAttachmentNeighbors
end
