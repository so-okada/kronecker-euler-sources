import KroneckerTypedReducedForest

/-! A proper bipartite coloring records original source/sink types and the
actual color of every directed arrow. Signed colors and a starting vertex
determine the full signed arrow; opposite directions are excluded by the
bipartition. This is the data needed to compare typed covers with color words. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerProperBipartiteQuiver
open KroneckerAbelianCover LabeledWalk KroneckerReducedColorWords
attribute [local instance] Classical.decEq Classical.propDecidable

structure Coloring (Q : TypedQuiver) where
  side : Q.V → ℕ
  side_lt : ∀ v, side v < 2
  color : Q.A → Color
  source_side : ∀ a, side (Q.source a) = 0
  target_side : ∀ a, side (Q.target a) = 1
  source_injective : ∀ a b, color a = color b → Q.source a = Q.source b → a = b
  target_injective : ∀ a b, color a = color b → Q.target a = Q.target b → a = b

variable {Q : TypedQuiver}

theorem endpoints_ne (C : Coloring Q) (a : Q.A) : Q.source a ≠ Q.target a := by
  intro h
  have hh := congrArg C.side h
  rw [C.source_side,C.target_side] at hh
  omega

theorem signed_color_start_injective (C : Coloring Q) (x y : Q.A × Bool)
    (hc : C.color x.1 = C.color y.1) (hs : stepStart Q.source Q.target x = stepStart Q.source Q.target y) : x = y := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases b <;> cases d
  · exact Prod.ext (C.target_injective a c hc hs) rfl
  · have hh := congrArg C.side hs
    change C.side (Q.target a) = C.side (Q.source c) at hh
    rw [C.target_side,C.source_side] at hh
    omega
  · have hh := congrArg C.side hs
    change C.side (Q.source a) = C.side (Q.target c) at hh
    rw [C.source_side,C.target_side] at hh
    omega
  · exact Prod.ext (C.source_injective a c hc hs) rfl

theorem signed_step_side (C : Coloring Q) (x : Q.A × Bool) :
    C.side (stepEnd Q.source Q.target x) = (C.side (stepStart Q.source Q.target x) + 1) % 2 := by
  rcases x with ⟨a,b⟩
  cases b <;> simp [stepStart,stepEnd,C.source_side,C.target_side]

end KroneckerProperBipartiteQuiver


/-! The concrete original three-arrow Kronecker quiver has vertices0 and1,
three actual color labels, and every arrow oriented from0 to1. Its proper
bipartite coloring is constructed, not supplied as a cover interface. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerThreeArrowBaseQuiver
open KroneckerAbelianCover KroneckerReducedColorWords KroneckerProperBipartiteQuiver
attribute [local instance] Classical.decEq Classical.propDecidable

def baseQuiver : TypedQuiver where
  V := Fin 2
  A := Color
  source _ := 0
  target _ := 1

instance vertexFintype : Fintype baseQuiver.V := inferInstanceAs (Fintype (Fin 2))
instance arrowFintype : Fintype baseQuiver.A := inferInstanceAs (Fintype Color)

def coloring : Coloring baseQuiver where
  side v := v.val
  side_lt v := v.isLt
  color a := a
  source_side _ := rfl
  target_side _ := rfl
  source_injective _ _ h _ := h
  target_injective _ _ h _ := h

theorem vertex_card : Fintype.card baseQuiver.V = 2 := Fintype.card_fin 2

theorem arrow_card : Fintype.card baseQuiver.A = 3 := Fintype.card_fin 3


end KroneckerThreeArrowBaseQuiver
