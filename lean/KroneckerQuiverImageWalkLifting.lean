import KroneckerDirectSumEmbeddingLocalLifts

/-! Locally surjective typed-quiver maps lift every finite signed walk from a
specified root. For embeddings this gives an exact equivalence of walk types
and proves that the image is a union of whole walk-connected components. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerQuiverImageWalkLifting
open KroneckerAbelianCover LabeledWalk KroneckerTypedQuiverMaps
open KroneckerDirectSumEmbeddingLocalLifts
variable {P Q : TypedQuiver}

theorem exists_walk_lift (f : QuiverMap P Q) (hf : LocallySurjective f)
    {u v : Q.V} (p : LabeledWalk Q.source Q.target u v) (x : P.V) (hx : f.vertex x = u) :
    ∃ y : P.V, f.vertex y = v ∧ ∃ q : LabeledWalk P.source P.target x y,
      labels (f.walk q) = labels p := by
  induction p generalizing x with
  | nil u => exact ⟨x,hx,.nil x,rfl⟩
  | forward a p ih =>
    obtain ⟨b,hs,hb⟩ := hf.1 x a hx.symm
    have ht : f.vertex (P.target b) = Q.target a := (f.target b).symm.trans (congrArg Q.target hb)
    obtain ⟨y,hy,q,hq⟩ := ih (P.target b) ht
    refine ⟨y,hy,castEndpoints hs rfl (.forward b q),?_⟩
    simp only [QuiverMap.walk,transport_labels,labels_castEndpoints,labels,List.map_cons] at hq ⊢
    rw [hb,hq]
  | backward a p ih =>
    obtain ⟨b,ht,hb⟩ := hf.2 x a hx.symm
    have hs : f.vertex (P.source b) = Q.source a := (f.source b).symm.trans (congrArg Q.source hb)
    obtain ⟨y,hy,q,hq⟩ := ih (P.source b) hs
    refine ⟨y,hy,castEndpoints ht rfl (.backward b q),?_⟩
    simp only [QuiverMap.walk,transport_labels,labels_castEndpoints,labels,List.map_cons] at hq ⊢
    rw [hb,hq]

theorem image_closed_under_walk (f : QuiverMap P Q) (hf : LocallySurjective f)
    {u v : Q.V} (p : LabeledWalk Q.source Q.target u v) (hu : u ∈ Set.range f.vertex) :
    v ∈ Set.range f.vertex := by
  obtain ⟨x,hx⟩ := hu
  obtain ⟨y,hy,_⟩ := exists_walk_lift f hf p x hx
  exact ⟨y,hy⟩

def walkEquiv (f : QuiverMap P Q) (hf : LocallySurjective f)
    (hv : Function.Injective f.vertex) (ha : Function.Injective f.arrow) (x y : P.V) :
    LabeledWalk P.source P.target x y ≃ LabeledWalk Q.source Q.target (f.vertex x) (f.vertex y) :=
  Equiv.ofBijective f.walk ⟨f.walk_injective ha x y,by
    intro p
    obtain ⟨z,hz,q,hq⟩ := exists_walk_lift f hf p x rfl
    have he : z = y := hv hz
    subst z
    exact ⟨q,labels_injective hq⟩⟩

theorem connected_iff (f : QuiverMap P Q) (hf : LocallySurjective f)
    (hv : Function.Injective f.vertex) (ha : Function.Injective f.arrow) (x y : P.V) :
    Nonempty (LabeledWalk P.source P.target x y) ↔
      Nonempty (LabeledWalk Q.source Q.target (f.vertex x) (f.vertex y)) :=
  (walkEquiv f hf hv ha x y).nonempty_congr

end KroneckerQuiverImageWalkLifting
