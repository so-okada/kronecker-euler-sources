import KroneckerAccumulatedDeckWalkTransport

/-! Actual maps of typed quivers act functorially and faithfully on labeled
walks when their arrow maps are injective. Reduced girth bounds pull back along
such maps, without assuming that the vertex map is surjective. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerTypedQuiverMaps
open KroneckerAbelianCover LabeledWalk

structure QuiverMap (Q R : TypedQuiver) where
  vertex : Q.V → R.V
  arrow : Q.A → R.A
  source : ∀ a, R.source (arrow a) = vertex (Q.source a)
  target : ∀ a, R.target (arrow a) = vertex (Q.target a)

namespace QuiverMap
variable {Q R T : TypedQuiver}
def identity (Q : TypedQuiver) : QuiverMap Q Q := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
def comp (f : QuiverMap Q R) (g : QuiverMap R T) : QuiverMap Q T where
  vertex := g.vertex ∘ f.vertex
  arrow := g.arrow ∘ f.arrow
  source a := (g.source (f.arrow a)).trans (congrArg g.vertex (f.source a))
  target a := (g.target (f.arrow a)).trans (congrArg g.vertex (f.target a))
def walk (f : QuiverMap Q R) {u v : Q.V} (p : LabeledWalk Q.source Q.target u v) :
    LabeledWalk R.source R.target (f.vertex u) (f.vertex v) :=
  transport f.vertex f.arrow f.source f.target p


theorem walk_injective (f : QuiverMap Q R) (ha : Function.Injective f.arrow) (u v : Q.V) :
    Function.Injective (f.walk (u:=u) (v:=v)) := by
  intro p q h
  apply labels_injective
  have hh := congrArg labels h
  simp only [walk,transport_labels] at hh
  apply (List.map_inj_right (f:=fun x : Q.A × Bool => (f.arrow x.1,x.2)) ?_).mp hh
  intro x y he
  exact Prod.ext (ha (congrArg (fun z : R.A × Bool => z.1) he))
    (congrArg (fun z : R.A × Bool => z.2) he)

theorem pull_girth (f : QuiverMap Q R) (ha : Function.Injective f.arrow) (g : ℕ)
    (h : ReducedGirthBound R.source R.target g) : ReducedGirthBound Q.source Q.target g := by
  intro u p hr hp
  have hl : (labels (f.walk p)).length = (labels p).length := by
    rw [walk,transport_labels,List.length_map]
  have hq := (transport_reduced_iff f.vertex f.arrow ha f.source f.target p).2 hr
  have hh := h (f.vertex u) (f.walk p) hq (by rwa [hl])
  rwa [hl] at hh
end QuiverMap

end KroneckerTypedQuiverMaps
