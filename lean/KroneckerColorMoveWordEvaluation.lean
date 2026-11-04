import KroneckerBipartiteCompleteColorFibers

/- Original module: KroneckerBipartiteColorMoves -/
section
/-! Complete proper color fibers define involutive color moves on actual
quiver vertices. The move follows an outgoing arrow at a source and the inverse
of an incoming arrow at a sink. Its endpoint and parity formulas are proved
from unique actual arrows, providing a concrete action for word evaluation. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBipartiteColorMoves
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerBipartiteCompleteColorFibers
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (H : Complete C)

def move (c : Color) (v : Q.V) : Q.V :=
  if h : C.side v = 0 then Q.target (sourceArrow C H v h c)
  else Q.source (targetArrow C H v (by have hh := C.side_lt v; omega) c)

theorem move_source (a : Q.A) : move C H (C.color a) (Q.source a) = Q.target a := by
  unfold move
  rw [dite_eq_left (C.source_side a),sourceArrow_eq C H _ _ _ a rfl rfl]

theorem move_target (a : Q.A) : move C H (C.color a) (Q.target a) = Q.source a := by
  unfold move
  rw [dite_eq_right (by rw [C.target_side]; omega),targetArrow_eq C H _ _ _ a rfl rfl]

theorem move_side (c : Color) (v : Q.V) : C.side (move C H c v) = (C.side v + 1) % 2 := by
  unfold move
  split_ifs with hs
  · rw [C.target_side,hs]
  · have ht : C.side v = 1 := by have hh := C.side_lt v; omega
    rw [C.source_side,ht]

theorem move_involutive (c : Color) : Function.Involutive (move C H c) := by
  intro v
  by_cases hs : C.side v = 0
  · let a := sourceArrow C H v hs c
    have ha := sourceArrow_spec C H v hs c
    have h1 : move C H c v = Q.target a := by
      unfold move
      rw [dite_eq_left hs]
    have h2 := move_target C H a
    rw [ha.2] at h2
    exact (congrArg (move C H c) h1).trans (h2.trans ha.1)
  · have ht : C.side v = 1 := by have hh := C.side_lt v; omega
    let a := targetArrow C H v ht c
    have ha := targetArrow_spec C H v ht c
    have h1 : move C H c v = Q.source a := by
      unfold move
      rw [dite_eq_right hs]
    have h2 := move_source C H a
    rw [ha.2] at h2
    exact (congrArg (move C H c) h1).trans (h2.trans ha.1)

def moveEquiv (c : Color) : Q.V ≃ Q.V where
  toFun := move C H c
  invFun := move C H c
  left_inv := move_involutive C H c
  right_inv := move_involutive C H c

end KroneckerBipartiteColorMoves
end
end

/- Original module: KroneckerColorMoveWordEvaluation -/
section
/-! Reduced color words evaluate by actual involutive color moves in any
complete properly colored bipartite quiver. Evaluation intertwines color
toggle exactly, respects concatenated actions, and computes source/sink parity.
No injectivity of this global finite-depth evaluation is presumed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerColorMoveWordEvaluation
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerReducedColorWords
open KroneckerBipartiteCompleteColorFibers KroneckerBipartiteColorMoves KroneckerWordParity
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver} (C : Coloring Q) (H : Complete C)

def evalList : List Color → Q.V → Q.V
  | [],u => u
  | c::l,u => move C H c (evalList l u)

def eval (u : Q.V) (w : Word) : Q.V := evalList C H w.val u

theorem eval_append (l k : List Color) (u : Q.V) :
    evalList C H (l++k) u = evalList C H l (evalList C H k u) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.cons_append,evalList,ih]

theorem eval_toggle (u : Q.V) (c : Color) (w : Word) : eval C H u (toggle c w) = move C H c (eval C H u w) := by
  rcases w with ⟨l,hl⟩
  cases l with
  | nil => rfl
  | cons d l =>
    by_cases hc : c = d
    · subst d
      change evalList C H (if c = c then l else c::c::l) u = move C H c (move C H c (evalList C H l u))
      rw [ite_eq_left rfl,move_involutive]
    · change evalList C H (if c = d then l else c::d::l) u = move C H c (move C H d (evalList C H l u))
      rw [ite_eq_right hc]
      rfl

theorem evalList_side (l : List Color) (u : Q.V) :
    C.side (evalList C H l u) = (l.length + C.side u) % 2 := by
  induction l with
  | nil => simpa only [evalList,List.length_nil,zero_add] using (Nat.mod_eq_of_lt (C.side_lt u)).symm
  | cons c l ih =>
    rw [evalList,move_side,ih]
    simp only [List.length_cons]
    omega

theorem eval_side (u : Q.V) (w : Word) : C.side (eval C H u w) = (parity w + C.side u) % 2 := by
  rw [eval,evalList_side]
  unfold parity
  omega

theorem eval_root (u : Q.V) : eval C H u root = u := rfl

end KroneckerColorMoveWordEvaluation
end
end
