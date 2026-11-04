import KroneckerColoredSourceAttachment

set_option autoImplicit false
namespace KroneckerSourceAttachmentColors
open KroneckerFiniteColoredTables KroneckerSourceAttachmentEdges KroneckerColoredSourceAttachment

variable {K : Type} {I J : K → Type}
variable (T : ∀ k,ColoredTable (I k) (J k)) (r : ∀ k,J k) (c : K → Fin 3)
variable (hc : Function.Injective c) (hr : ∀ k i,(T k).code i (r k)≠some (c k))

theorem attachment_root_colors (e : Fin 3) :
    (∃ j,(sourceAttachment T r c hc hr).code none j=some e) ↔ ∃ k,c k=e := by
  constructor
  · rintro ⟨⟨k,j⟩,h⟩
    exact ⟨k,((attach_root_edge T r c k j e).mp
      ((attachment_code_iff T r c hc hr _ _ e).mp h)).2⟩
  · rintro ⟨k,rfl⟩
    exact ⟨⟨k,r k⟩,(attachment_code_iff T r c hc hr _ _ _).mpr (AttachEdge.root k)⟩

theorem attachment_component_colors (k : K) (i : I k) (e : Fin 3) :
    (∃ j,(sourceAttachment T r c hc hr).code (some ⟨k,i⟩) j=some e) ↔
      ∃ j,(T k).code i j=some e := by
  constructor
  · rintro ⟨⟨l,j⟩,h⟩
    have he : k=l := attach_component_index T r c
      ((attachment_code_iff T r c hc hr _ _ e).mp h)
    subst l
    exact ⟨j,(attachment_internal_code T r c hc hr k i j).symm.trans h⟩
  · rintro ⟨j,h⟩
    exact ⟨⟨k,j⟩,(attachment_internal_code T r c hc hr k i j).trans h⟩

end KroneckerSourceAttachmentColors
