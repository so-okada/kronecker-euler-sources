import KroneckerAccumulatedDeckRootTransitivity
import KroneckerLabeledWalkTransport

/-! Accumulated deck maps transport genuine walks and preserve their complete
original signed words. Equal starting points and base words then identify the
actual lifted endpoints, including after an arbitrary number of cover stages. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerAccumulatedDeckWalkTransport
open KroneckerAbelianCover KroneckerAbelianCover.TypedQuiver LabeledWalk
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerAccumulatedCoverDeckActions
open KroneckerAccumulatedDeckBaseLabels KroneckerIteratedQuiverBaseProjection
attribute [local instance] Classical.decEq Classical.propDecidable

def walk (Q : TypedQuiver) (n : ℕ) (f : Deck Q n) {u v : (Q.iterate n).V}
    (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v) :
    LabeledWalk (Q.iterate n).source (Q.iterate n).target (f.val.vertexEquiv u) (f.val.vertexEquiv v) :=
  transport f.val.vertexEquiv f.val.arrowEquiv f.val.map_source f.val.map_target p

theorem walk_base_labels (Q : TypedQuiver) (n : ℕ) (f : Deck Q n) {u v : (Q.iterate n).V}
    (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v) :
    labels (baseWalk Q n (walk Q n f p)) = labels (baseWalk Q n p) := by
  rw [base_labels,walk,transport_labels,base_labels,List.map_map]
  congr 1
  funext x
  exact Prod.ext (arrow_base_invariant Q n f.val f.property x.1) rfl

theorem walk_reduced_iff (Q : TypedQuiver) (n : ℕ) (f : Deck Q n) {u v : (Q.iterate n).V}
    (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v) :
    Reduced (walk Q n f p) ↔ Reduced p :=
  transport_reduced_iff _ _ f.val.arrowEquiv.injective _ _ _

theorem endpoint_of_base_word (Q : TypedQuiver) (n : ℕ) (f : Deck Q n)
    {u v u' v' : (Q.iterate n).V}
    (p : LabeledWalk (Q.iterate n).source (Q.iterate n).target u v)
    (q : LabeledWalk (Q.iterate n).source (Q.iterate n).target u' v')
    (hu : f.val.vertexEquiv u = u') (hpq : labels (baseWalk Q n p) = labels (baseWalk Q n q)) :
    f.val.vertexEquiv v = v' := by
  have hb : labels (baseWalk Q n (walk Q n f p)) = labels (baseWalk Q n q) :=
    (walk_base_labels Q n f p).trans hpq
  exact (labels_heq (walk Q n f p) q hu
    (baseWalk_labels_injective Q n _ _ hu hb)).1

end KroneckerAccumulatedDeckWalkTransport
