import KroneckerManuscriptNotation

/-! Proper coloring on actual incident arrow sets, and its typed-quiver bridge. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace KroneckerManuscriptQuiverDefinitions.ColoredQuiver

def Proper {C : Type} (Q : ColoredQuiver C) : Prop :=
  ∀ v, Set.InjOn Q.QCol (Q.1.IncEdgeQuiv v)

theorem proper_iff_endpoint_injective {C : Type} (Q : ColoredQuiver C)
    (B : Q.1.Bipartition) :
    Q.Proper ↔
      (∀ a b, Q.QCol a = Q.QCol b → Q.1.source a = Q.1.source b → a=b) ∧
      (∀ a b, Q.QCol a = Q.QCol b → Q.1.target a = Q.1.target b → a=b) := by
  constructor
  · intro h
    exact ⟨fun a b hc hs => h (Q.1.source a) (Or.inl rfl) (Or.inl hs.symm) hc,
      fun a b hc ht => h (Q.1.target a) (Or.inr rfl) (Or.inr ht.symm) hc⟩
  · rintro ⟨hs,ht⟩ v a ha b hb hc
    have cross (a b : Q.1.Edge) : Q.1.source a ≠ Q.1.target b := by
      intro h
      exact Set.disjoint_left.mp B.disjoint (B.source_mem a) (h.symm ▸ B.target_mem b)
    rcases ha with ha|ha <;> rcases hb with hb|hb
    · exact hs a b hc (ha.trans hb.symm)
    · exact (cross a b (ha.trans hb.symm)).elim
    · exact (cross b a (hb.trans ha.symm)).elim
    · exact ht a b hc (ha.trans hb.symm)

theorem ofProperColoring_proper {Q : KroneckerAbelianCover.TypedQuiver}
    (C : KroneckerProperBipartiteQuiver.Coloring Q) : (ofProperColoring C).Proper :=
  (proper_iff_endpoint_injective _ (properBipartition C)).mpr
    ⟨C.source_injective,C.target_injective⟩

def toProperColoring (Q : ColoredQuiver KroneckerReducedColorWords.Color)
    (B : Q.1.Bipartition) (h : Q.Proper) : KroneckerProperBipartiteQuiver.Coloring Q.1.toTyped where
  side v := if v ∈ B.sources then 0 else 1
  side_lt v := by split <;> decide
  color := Q.QCol
  source_side a := by simp [Quiver.toTyped,B.source_mem a]
  target_side a := by
    have hn : Q.1.target a ∉ B.sources := fun hi =>
      Set.disjoint_left.mp B.disjoint hi (B.target_mem a)
    simp [Quiver.toTyped,hn]
  source_injective := (proper_iff_endpoint_injective Q B).mp h |>.1
  target_injective := (proper_iff_endpoint_injective Q B).mp h |>.2

theorem toProperColoring_color (Q : ColoredQuiver KroneckerReducedColorWords.Color)
    (B : Q.1.Bipartition) (h : Q.Proper) (a : Q.1.Edge) :
    (toProperColoring Q B h).color a = Q.QCol a := rfl

end KroneckerManuscriptQuiverDefinitions.ColoredQuiver

set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.ColoredQuiver.Proper
set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.ColoredQuiver.proper_iff_endpoint_injective
set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.ColoredQuiver.ofProperColoring_proper
set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.ColoredQuiver.toProperColoring
set_option pp.fullNames true in
#print axioms KroneckerManuscriptQuiverDefinitions.ColoredQuiver.toProperColoring_color
