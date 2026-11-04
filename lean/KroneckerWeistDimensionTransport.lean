import KroneckerWeistTranslations

/- Original module: KroneckerWeistDeckDictionary -/
section
/-! On the connected color cover, the project's deck maps are exactly the
restrictions of Weist's free-word translations whenever the latter meet the
component. No global permutation of arrow colors is introduced. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistDeckDictionary
open KroneckerWeistSignedWords KroneckerWeistCoverEmbedding KroneckerWeistTranslations
open KroneckerReducedColorWords KroneckerColorWordAction KroneckerWordParity
open KroneckerCoverDeckTranslations KroneckerUniversalWordBaseProjection

private theorem deck_encode_normal (d : Deck) (l : List Color) :
    encode (d (normal l)) = encode (d root) * encodeList l := by
  induction l with
  | nil => simp [normal,act,encodeList]
  | cons c l ih =>
    change encode (d (toggle c (normal l))) = _
    rw [d.commutes,encode_toggle,ih]
    have hs : signed c (d (normal l)).val.length = signed c l.length := by
      change (if parity (d (normal l))=0 then _ else _) = _
      rw [d.preserves_parity,normal_parity]
      rfl
    rw [hs,encodeList,mul_assoc]

theorem deck_encode (d : Deck) (w : Word) :
    encode (d w) = encode (d root) * encode w := by
  simpa only [normal_reduced,encode] using deck_encode_normal d w.val

theorem deck_shift (d : Deck) (w : Word) :
    vertex (d w) = shift (encode (d root)) (vertex w) := by
  apply Prod.ext
  · apply Fin.ext
    exact d.preserves_parity w
  · exact deck_encode d w

/-- A translation taking even one vertex of the base component to another
restricts to a unique color/bipartition-preserving deck map on that component. -/
theorem shift_match_deck (g : GroupWord) (u v : Word)
    (h : shift g (vertex u)=vertex v) :
    ∃ d : Deck, d u=v ∧ ∀ w, shift g (vertex w)=vertex (d w) := by
  have hp : parity u=parity v := congrArg (fun z : KroneckerWeistCoverEmbedding.cover.V => z.1.val) h
  obtain ⟨d,hd⟩ := deck_transitive_same_parity hp
  have he : g=encode (d root) := by
    apply mul_right_cancel (b:=encode u)
    have hs : g*encode u=encode v := congrArg Prod.snd h
    rw [hs,←deck_encode,hd]
  refine ⟨d,hd,fun w => ?_⟩
  rw [he]
  exact (deck_shift d w).symm

end KroneckerWeistDeckDictionary
end
end

/- Original module: KroneckerWeistDimensionTransport -/
section
/-! Finitely supported dimensions and their pushforward to Weist's cover.
The deck/free-word correspondence commutes with actual dimension transport. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistDimensionTransport
open KroneckerWeistSignedWords KroneckerWeistCoverEmbedding KroneckerWeistTranslations
open KroneckerWeistDeckDictionary KroneckerReducedColorWords KroneckerCoverDeckTranslations
open KroneckerDeckDimensionClasses
attribute [local instance] Classical.decEq Classical.propDecidable

def push (D : Word →₀ ℕ) : cover.V →₀ ℕ := D.mapDomain vertex

theorem push_injective : Function.Injective push := Finsupp.mapDomain_injective vertex_injective

theorem push_at (D : Word →₀ ℕ) (w : Word) : push D (vertex w)=D w :=
  Finsupp.mapDomain_apply_of_injective vertex_injective D w

theorem push_nonzero_range (D : Word →₀ ℕ) (v : cover.V) (h : push D v≠0) :
    ∃ w, vertex w=v := by
  by_contra H
  exact h (Finsupp.mapDomain_of_notMem_range D v H)

theorem shift_injective (g : GroupWord) : Function.Injective (shift g) :=
  (translation g).vertexEquiv.injective

theorem deck_transport (d : Deck) (D : Word →₀ ℕ) :
    (push D).mapDomain (shift (encode (d root))) = push (D.mapDomain d) := by
  unfold push
  rw [←Finsupp.mapDomain_comp,←Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro w _
  exact (deck_shift d w).symm

theorem dimension_related_iff_pushforward (D E : Word →₀ ℕ) :
    dimensionSetoid.r D E ↔ ∃ d : Deck, D.mapDomain d=E := by
  constructor
  · rintro ⟨d,h⟩
    refine ⟨d,?_⟩
    ext w
    obtain ⟨v,rfl⟩ := d.equiv.surjective w
    rw [Finsupp.mapDomain_apply_of_injective d.equiv.injective]
    exact (h v).symm
  · rintro ⟨d,rfl⟩
    exact ⟨d,fun w => Finsupp.mapDomain_apply_of_injective d.equiv.injective D w⟩

end KroneckerWeistDimensionTransport
end
end
