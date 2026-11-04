import KroneckerNaturalPathGradings

/-! The h-precursor, debt, nodes, restriction, and parent statements for
arbitrary natural-valued gradings. The input-dependent finite encoding has
exactly the same grades, edges, and assignment fibers. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths
open KroneckerPaperPathGradings (Horizontal Vertical edgeIndex assignmentCount nodePath)

def occurrenceWord {P : TNEPath} (g : Grading P) :
    KroneckerPredecessor.Word P.steps.length :=
  fun i => if P.steps.get i then .H (g (edgeEquiv P i)) else .V (g (edgeEquiv P i))

def IsHPrecursor {P : TNEPath} (g : Grading P)
    (p : Vertical P → Horizontal P) : Prop :=
  ∀ v : Vertical P, IsGreatest
    {i : ℕ | ∃ x : Horizontal P, i = edgeIndex x.val ∧
      edgeIndex x.val < edgeIndex v.val ∧
      assignmentCount p (edgeIndex v.val) x < g x.val}
    (edgeIndex (p v).val)

theorem hPrecursor_unique {P : TNEPath} (g : Grading P)
    (p q : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (hq : IsHPrecursor g q) : p = q :=
  KroneckerPaperPathGradings.hPrecursor_unique (bounded g) p q hp hq

theorem hPrecursor_exists_iff {P : TNEPath} (g : Grading P) :
    (∃ p, IsHPrecursor g p) ↔ ∀ k ≤ P.steps.length,
      KroneckerPredecessor.verticalCount (occurrenceWord g) k ≤
        KroneckerPredecessor.horizontalGrade (occurrenceWord g) k :=
  KroneckerPaperPathGradings.hPrecursor_exists_iff (bounded g)

def Debt {P : TNEPath} (g : Grading P) (p : Vertical P → Horizontal P)
    (x : Horizontal P) (k : ℕ) : ℤ := (g x.val : ℤ) - assignmentCount p k x

theorem debt_nonnegative {P : TNEPath} (g : Grading P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (x : Horizontal P) (k : ℕ) (hk : k ≤ P.steps.length) : 0 ≤ Debt g p x k := by
  have h := KroneckerPaperPathGradings.hPrecursor_debt_formula (bounded g) p hp x k hk
  change _ = Debt g p x k at h
  rw [← h]
  exact Int.natCast_nonneg _

def IsNode {P : TNEPath} (g : Grading P) (p : Vertical P → Horizontal P)
    (x : Horizontal P) (v : Vertical P) : Prop :=
  p v = x ∧ assignmentCount p P.steps.length x = g x.val ∧
    ∀ w : Vertical P, p w = x → edgeIndex w.val ≤ edgeIndex v.val

abbrev Node {P : TNEPath} (g : Grading P) (p : Vertical P → Horizontal P) :=
  KroneckerPaperPathGradings.Node (bounded g) p

def NodeBalance {P : TNEPath} (g : Grading P) (p : Vertical P → Horizontal P) : Prop :=
  KroneckerPaperPathGradings.NodeBalance (bounded g) p

abbrev nodeGrading {P : TNEPath} (g : Grading P) (x : Horizontal P) (v : Vertical P) :
    Grading (nodePath x v) :=
  restrictGrading g (edgeIndex x.val) (edgeIndex v.val+1) ((edgeEquiv P).symm v.val).isLt

def Parent {P : TNEPath} {g : Grading P} {p : Vertical P → Horizontal P}
    (X Y : Node g p) : Prop := KroneckerPaperPathGradings.Parent X Y

theorem node_isSubpath {P : TNEPath} {g : Grading P}
    {p : Vertical P → Horizontal P} (hp : IsHPrecursor g p) (X : Node g p) :
    IsSubpath (nodePath X.first X.last) P :=
  KroneckerPaperPathGradings.Node.isSubpath (g := bounded g) hp X

theorem node_subpath_laminar {P : TNEPath} {g : Grading P}
    {p : Vertical P → Horizontal P} (hp : IsHPrecursor g p) (X Y : Node g p) :
    Disjoint (KroneckerPaperPathGradings.nodeEdges X) (KroneckerPaperPathGradings.nodeEdges Y) ∨
    KroneckerPaperPathGradings.nodeEdges X ⊆ KroneckerPaperPathGradings.nodeEdges Y ∨
    KroneckerPaperPathGradings.nodeEdges Y ⊆ KroneckerPaperPathGradings.nodeEdges X :=
  KroneckerPaperPathGradings.nodeEdges_laminar (g := bounded g) hp X Y

theorem parent_unique {P : TNEPath} {g : Grading P}
    {p : Vertical P → Horizontal P} (hp : IsHPrecursor g p) {X Y Z : Node g p}
    (hX : Parent X Z) (hY : Parent Y Z) : X = Y :=
  KroneckerPaperPathGradings.parent_unique (g := bounded g) hp hX hY

theorem nodeGrading_connected {P : TNEPath} (g : Grading P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (hb : NodeBalance g p) (X : Node g p) :
    ConnectedGrading (nodeGrading g X.first X.last) :=
  KroneckerPaperPathGradings.nodeGrading_connected (bounded g) p hp hb X

theorem nodeGrading_surp_nonnegative {P : TNEPath} (g : Grading P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (hb : NodeBalance g p) (X : Node g p) :
    0 ≤ Surp (nodePath X.first X.last) (nodeGrading g X.first X.last) :=
  connected_surp_nonnegative (nodeGrading_connected g p hp hb X)

theorem node_surp_balance {P : TNEPath} (g : Grading P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p) (X : Node g p) :
    eBal g X.last.val -
      bBal g ⟨edgeIndex X.first.val, Nat.lt_succ_of_lt ((edgeEquiv P).symm X.first.val).isLt⟩ =
    Surp (nodePath X.first X.last) (nodeGrading g X.first X.last)+1 :=
  KroneckerPaperPathGradings.node_surp_balance (bounded g) p hp X

end KroneckerNaturalPathGradings
