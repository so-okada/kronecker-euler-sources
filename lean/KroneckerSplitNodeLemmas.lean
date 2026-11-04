import KroneckerNaturalNodes

/-! Contracts for `lem:node-structure`, `lem:node-balances` and
`lem:node-restriction`, in manuscript order.
The word model numbers edge occurrences from zero. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerSplitNodeLemmas

open KroneckerPredecessor

theorem interior_node {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v y : Fin n} (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hy : IsHorizontal U y) (hxy : x.val < y.val) (hyv : y.val ≤ v.val)
    (hg : 0 < (U y).grade) :
    ∃ z, IsNode U p y z ∧ z.val < v.val :=
  h.interior_node hp hy hxy hyv hg

theorem node_balances {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    {x v : Fin n} (h : IsNode U p x v) (hp : ValidThrough U p n)
    (hb : OwnedBalance U p) :
    (∀ i : ℕ, x.val + 1 ≤ i → i ≤ v.val + 1 → baseline U x ≤ balance U i) ∧
    (∀ y : Fin n, IsHorizontal U y → x.val < y.val → y.val ≤ v.val →
      baseline U x < baseline U y) :=
  ⟨fun _ hi hj => h.balance_lower_bound hp hb hi hj,
    fun _ hy hxy hyv => h.interior_baseline_lt hp hb hy hxy hyv⟩

open KroneckerPaperPaths
open KroneckerPaperPathGradings (Horizontal Vertical edgeIndex nodePath)
open KroneckerNaturalPathGradings

theorem node_restriction {P : TNEPath} (g : Grading P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (hb : NodeBalance g p) (X : KroneckerNaturalPathGradings.Node g p) :
    ConnectedGrading (nodeGrading g X.first X.last) ∧
    0 ≤ Surp (nodePath X.first X.last) (nodeGrading g X.first X.last) ∧
    eBal g X.last.val -
      bBal g ⟨edgeIndex X.first.val, Nat.lt_succ_of_lt ((edgeEquiv P).symm X.first.val).isLt⟩ =
      Surp (nodePath X.first X.last) (nodeGrading g X.first X.last) + 1 :=
  ⟨nodeGrading_connected g p hp hb X,
    nodeGrading_surp_nonnegative g p hp hb X, node_surp_balance g p hp X⟩

end KroneckerSplitNodeLemmas

#print axioms KroneckerSplitNodeLemmas.interior_node
#print axioms KroneckerSplitNodeLemmas.node_balances
#print axioms KroneckerSplitNodeLemmas.node_restriction
