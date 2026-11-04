import KroneckerIteratedBallFinite

set_option autoImplicit false
namespace KroneckerAbelianCover
namespace TypedQuiver
open LabeledWalk

noncomputable def baseArrow (Q : TypedQuiver) : (n : ℕ) → (Q.iterate n).A → Q.A
  | 0,a => a
  | n+1,a => baseArrow Q n a.1

/-- Unique outgoing arrow lifting holds after ALL actual cover iterations. -/
theorem baseArrow_source_injective (Q : TypedQuiver) (n : ℕ)
    (a b : (Q.iterate n).A) (ha : baseArrow Q n a = baseArrow Q n b)
    (hs : (Q.iterate n).source a = (Q.iterate n).source b) : a = b := by
  classical
  induction n with
  | zero => exact ha
  | succ n ih =>
    apply Prod.ext
    · exact ih a.1 b.1 ha (congrArg Prod.fst hs)
    · exact congrArg (fun w : (Q.iterate (n+1)).V => w.2) hs

/-- Unique incoming arrow lifting similarly survives every iteration. -/
theorem baseArrow_target_injective (Q : TypedQuiver) (n : ℕ)
    (a b : (Q.iterate n).A) (ha : baseArrow Q n a = baseArrow Q n b)
    (ht : (Q.iterate n).target a = (Q.iterate n).target b) : a = b := by
  classical
  induction n with
  | zero => exact ha
  | succ n ih =>
    have he : a.1 = b.1 := ih a.1 b.1 ha (congrArg Prod.fst ht)
    apply Prod.ext he
    have hc := congrArg Prod.snd ht
    change a.2 + unit a.1 = b.2 + unit b.1 at hc
    rw [he] at hc
    exact add_right_cancel hc

/-- ALL actual outgoing arrows whose source is in the rooted radius ball. -/
def SourceBallArrow (Q : TypedQuiver) (n r : ℕ) (u : (Q.iterate n).V) :=
  {a : (Q.iterate n).A // ∃p : LabeledWalk (Q.iterate n).source (Q.iterate n).target
    u ((Q.iterate n).source a), Reduced p ∧ (labels p).length ≤ r}

noncomputable def sourceBallArrowCode (Q : TypedQuiver) (n r : ℕ) (u : (Q.iterate n).V)
    (a : SourceBallArrow Q n r u) :
    Q.A × VertexBall (s:=(Q.iterate n).source) (t:=(Q.iterate n).target) u r :=
  (baseArrow Q n a.val,⟨(Q.iterate n).source a.val,a.property⟩)

theorem sourceBallArrowCode_injective (Q : TypedQuiver) (n r : ℕ) (u : (Q.iterate n).V) :
    Function.Injective (sourceBallArrowCode Q n r u) := by
  intro a b h
  apply Subtype.ext
  apply baseArrow_source_injective Q n a.val b.val
  · exact congrArg Prod.fst h
  · exact congrArg (fun z => z.2.val) h

theorem sourceBallArrow_finite (Q : TypedQuiver) [Finite Q.A] (n r : ℕ) (u : (Q.iterate n).V) :
    Finite (SourceBallArrow Q n r u) := by
  haveI := iterate_vertexBall_finite Q n r u
  exact Finite.of_injective (sourceBallArrowCode Q n r u) (sourceBallArrowCode_injective Q n r u)


end TypedQuiver
end KroneckerAbelianCover
