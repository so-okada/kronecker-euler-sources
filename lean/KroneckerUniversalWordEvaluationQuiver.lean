import KroneckerColorMoveWordEvaluation

/-! Evaluation of universal colored words from a chosen source vertex is an
actual quiver map into any complete properly colored bipartite quiver. Its
arrow map uses unique outgoing color fibers, preserves colors, and has the
correct source and target rather than only a graph-level endpoint action. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerUniversalWordEvaluationQuiver
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerBipartiteCompleteColorFibers KroneckerBipartiteColorMoves
open KroneckerColorMoveWordEvaluation KroneckerWordParity KroneckerTypedQuiverMaps
open KroneckerFiniteSupportDeckRepresentationTransport
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (H : Complete C) (u : Q.V) (hu : C.side u = 0)

include hu in
theorem evaluation_side (w : Word) : C.side (eval C H u w) = parity w := by
  rw [eval_side,hu,add_zero]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))

def evaluationMap : QuiverMap coloredCoverQuiver Q where
  vertex := eval C H u
  arrow a := sourceArrow C H (eval C H u a.2.val) ((evaluation_side C H u hu a.2.val).trans a.2.property) a.1
  source a := (sourceArrow_spec C H (eval C H u a.2.val) ((evaluation_side C H u hu a.2.val).trans a.2.property) a.1).1
  target a := by
    change Q.target (sourceArrow C H (eval C H u a.2.val) _ a.1) = eval C H u (toggle a.1 a.2.val)
    rw [eval_toggle]
    have h := move_source C H (sourceArrow C H (eval C H u a.2.val)
      ((evaluation_side C H u hu a.2.val).trans a.2.property) a.1)
    rw [(sourceArrow_spec C H (eval C H u a.2.val) ((evaluation_side C H u hu a.2.val).trans a.2.property) a.1).1,(sourceArrow_spec C H (eval C H u a.2.val) ((evaluation_side C H u hu a.2.val).trans a.2.property) a.1).2] at h
    exact h.symm

theorem evaluation_color (a : coloredCoverQuiver.A) : C.color ((evaluationMap C H u hu).arrow a) = a.1 :=
  (sourceArrow_spec C H (eval C H u a.2.val) ((evaluation_side C H u hu a.2.val).trans a.2.property) a.1).2


end KroneckerUniversalWordEvaluationQuiver
