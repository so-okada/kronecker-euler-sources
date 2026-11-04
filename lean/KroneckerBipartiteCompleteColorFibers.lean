import KroneckerProperBipartiteQuiver

/-! Completeness of a proper bipartite coloring provides one actual outgoing
arrow of each color at each source vertex and one incoming arrow of each color
at each sink vertex. The chosen arrows are unique by the checked proper-color
fiber laws, so later word evaluation has no hidden edge-selection ambiguity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerBipartiteCompleteColorFibers
open KroneckerAbelianCover KroneckerProperBipartiteQuiver KroneckerReducedColorWords
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Q : TypedQuiver}

structure Complete (C : Coloring Q) : Prop where
  source : ∀ (v : Q.V), C.side v = 0 → ∀ c : Color, ∃ a : Q.A, Q.source a = v ∧ C.color a = c
  target : ∀ (v : Q.V), C.side v = 1 → ∀ c : Color, ∃ a : Q.A, Q.target a = v ∧ C.color a = c

variable (C : Coloring Q) (H : Complete C)

def sourceArrow (v : Q.V) (hs : C.side v = 0) (c : Color) : Q.A := Classical.choose (H.source v hs c)
def targetArrow (v : Q.V) (ht : C.side v = 1) (c : Color) : Q.A := Classical.choose (H.target v ht c)

theorem sourceArrow_spec (v : Q.V) (hs : C.side v = 0) (c : Color) :
    Q.source (sourceArrow C H v hs c) = v ∧ C.color (sourceArrow C H v hs c) = c :=
  Classical.choose_spec (H.source v hs c)

theorem targetArrow_spec (v : Q.V) (ht : C.side v = 1) (c : Color) :
    Q.target (targetArrow C H v ht c) = v ∧ C.color (targetArrow C H v ht c) = c :=
  Classical.choose_spec (H.target v ht c)

theorem sourceArrow_eq (v : Q.V) (hs : C.side v = 0) (c : Color) (a : Q.A)
    (ha : Q.source a = v) (hc : C.color a = c) : sourceArrow C H v hs c = a :=
  C.source_injective _ a ((sourceArrow_spec C H v hs c).2.trans hc.symm)
    ((sourceArrow_spec C H v hs c).1.trans ha.symm)

theorem targetArrow_eq (v : Q.V) (ht : C.side v = 1) (c : Color) (a : Q.A)
    (ha : Q.target a = v) (hc : C.color a = c) : targetArrow C H v ht c = a :=
  C.target_injective _ a ((targetArrow_spec C H v ht c).2.trans hc.symm)
    ((targetArrow_spec C H v ht c).1.trans ha.symm)

end KroneckerBipartiteCompleteColorFibers
