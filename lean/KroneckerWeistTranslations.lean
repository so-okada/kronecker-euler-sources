import KroneckerWeistCoverEmbedding

/- Original module: KroneckerWeistBaseComponent -/
section
/-! The image of the reduced-color-word cover is exactly the connected component
of (source,1) in Weist's possibly disconnected free-word cover. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistBaseComponent
open KroneckerWeistSignedWords KroneckerWeistCoverEmbedding
open KroneckerReducedColorWords KroneckerColorWordAction KroneckerWordParity
open KroneckerUniversalWordBaseProjection

def InBase (v : cover.V) : Prop := ∃ w : Word, vertex w = v

def Adj (u v : cover.V) : Prop := ∃ e : cover.A,
  (u=cover.source e ∧ v=cover.target e) ∨ (u=cover.target e ∧ v=cover.source e)

abbrev Reach (u v : cover.V) := Relation.ReflTransGen Adj u v

theorem endpoints_in_base (e : cover.A) : InBase (cover.source e) ↔ InBase (cover.target e) := by
  constructor
  · rintro ⟨w,hw⟩
    have hp : parity w=0 := congrArg (fun v : cover.V => v.1.val) hw
    have hg : encode w=e.2 := congrArg Prod.snd hw
    refine ⟨toggle e.1 w,?_⟩
    apply Prod.ext
    · apply Fin.ext
      change parity (toggle e.1 w)=1
      rw [toggle_parity,hp]
    · change encode (toggle e.1 w)=e.2*FreeGroup.of e.1
      rw [source_step _ _ hp,hg]
  · rintro ⟨w,hw⟩
    have hp : parity w=1 := congrArg (fun v : cover.V => v.1.val) hw
    have hg : encode w=e.2*FreeGroup.of e.1 := congrArg Prod.snd hw
    refine ⟨toggle e.1 w,?_⟩
    apply Prod.ext
    · apply Fin.ext
      change parity (toggle e.1 w)=0
      rw [toggle_parity,hp]
    · change encode (toggle e.1 w)=e.2
      rw [sink_step _ _ hp,hg]
      simp [mul_assoc]

theorem adj_closed {u v : cover.V} (h : Adj u v) (hu : InBase u) : InBase v := by
  obtain ⟨e,h | h⟩ := h
  · rcases h with ⟨rfl,rfl⟩
    exact (endpoints_in_base e).mp hu
  · rcases h with ⟨rfl,rfl⟩
    exact (endpoints_in_base e).mpr hu

theorem toggle_adj (c : Color) (w : Word) : Adj (vertex w) (vertex (toggle c w)) := by
  by_cases hp : parity w=0
  · let e : KroneckerFiniteSupportDeckRepresentationTransport.coloredCoverQuiver.A := (c,⟨w,hp⟩)
    exact ⟨embedding.arrow e,Or.inl ⟨(embedding.source e).symm,(embedding.target e).symm⟩⟩
  · have hp' : parity (toggle c w)=0 := by
      rw [toggle_parity]
      have : parity w<2 := Nat.mod_lt _ (by decide)
      omega
    let e : KroneckerFiniteSupportDeckRepresentationTransport.coloredCoverQuiver.A := (c,⟨toggle c w,hp'⟩)
    refine ⟨embedding.arrow e,Or.inr ⟨?_,(embedding.source e).symm⟩⟩
    simpa only [e,embedding,KroneckerFiniteSupportDeckRepresentationTransport.coloredCoverQuiver,
      toggle_involution] using (embedding.target e).symm

theorem normal_reachable (l : List Color) : Reach (vertex root) (vertex (normal l)) := by
  induction l with
  | nil => exact .refl
  | cons c l ih => exact ih.tail (toggle_adj c (normal l))

theorem image_reachable (w : Word) : Reach (vertex root) (vertex w) := by
  simpa only [normal_reduced] using normal_reachable w.val

theorem in_base_iff_reachable (v : cover.V) : InBase v ↔ Reach (vertex root) v := by
  constructor
  · rintro ⟨w,rfl⟩
    exact image_reachable w
  · intro h
    induction h with
    | refl => exact ⟨root,rfl⟩
    | tail h e ih => exact adj_closed e ih

end KroneckerWeistBaseComponent
end
end

/- Original module: KroneckerWeistTranslations -/
section
/-! Free-word translations of Weist's entire cover are genuine quiver
isomorphisms. Any component containing a source vertex translates to the
project's based component, retaining projection and arrow colors. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistTranslations
open KroneckerWeistSignedWords KroneckerWeistCoverEmbedding KroneckerWeistBaseComponent
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerReducedColorWords

def shift (g : GroupWord) (v : cover.V) : cover.V := (v.1,g*v.2)

def translation (g : GroupWord) : TypedQuiverIso cover cover where
  vertexEquiv :=
    { toFun := shift g
      invFun := shift g⁻¹
      left_inv := by rintro ⟨v,w⟩; simp [shift] <;> rfl
      right_inv := by rintro ⟨v,w⟩; simp [shift] <;> rfl }
  arrowEquiv :=
    { toFun := fun e => (e.1,g*e.2)
      invFun := fun e => (e.1,g⁻¹*e.2)
      left_inv := by rintro ⟨a,w⟩; simp [] <;> rfl
      right_inv := by rintro ⟨a,w⟩; simp [] <;> rfl }
  map_source _ := rfl
  map_target e := by
    change (1, (g * e.2) * FreeGroup.of e.1) = (1, g * (e.2 * FreeGroup.of e.1))
    rw [mul_assoc]

theorem shift_adj (g : GroupWord) {u v : cover.V} (h : Adj u v) :
    Adj (shift g u) (shift g v) := by
  obtain ⟨e,h | h⟩ := h
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨(translation g).arrowEquiv e,Or.inl
      ⟨((translation g).map_source e).symm,((translation g).map_target e).symm⟩⟩
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨(translation g).arrowEquiv e,Or.inr
      ⟨((translation g).map_target e).symm,((translation g).map_source e).symm⟩⟩

theorem shift_reach (g : GroupWord) {u v : cover.V} (h : Reach u v) :
    Reach (shift g u) (shift g v) :=
  h.lift (shift g) (fun _ _ e => shift_adj g e)

theorem source_component_normalization (g : GroupWord) (v : cover.V)
    (h : Reach (0,g) v) : InBase (shift g⁻¹ v) := by
  apply (in_base_iff_reachable _).mpr
  have H := shift_reach g⁻¹ h
  simpa [shift,vertex,KroneckerUniversalWordBaseProjection.baseVertex,
    KroneckerWordParity.parity,encode,encodeList,root] using H



end KroneckerWeistTranslations
end
end
