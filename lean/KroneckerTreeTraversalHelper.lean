import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A traversal with no immediate reversal in a tree has distinct vertices.
The recursive condition records v_i ≠ v_{i+2}; for a simple graph this is
exactly inequality of consecutive unoriented edges. -/
namespace KroneckerTreeTraversalHelper
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def NoReversal : {u v : V} → G.Walk u v → Prop
  | _, _, .nil => True
  | u, _, .cons _ p =>
      (∀ {w : V} (h : G.Adj _ w) (q : G.Walk w _), p = .cons h q → w ≠ u) ∧
      NoReversal p

theorem noReversal_isPath (hT : G.IsTree) {u v : V}
    (p : G.Walk u v) (hp : NoReversal p) : p.IsPath := by
  classical
  induction p with
  | nil => exact Walk.IsPath.nil
  | @cons u v w h p ih =>
    have hpath := ih hp.2
    apply hpath.cons
    intro hu
    have ht : p.takeUntil u hu = .cons h.symm .nil :=
      (hT.existsUnique_path v u).unique (hpath.takeUntil hu)
        (Walk.IsPath.nil.cons (by simpa using h.ne.symm))
    cases p with
    | nil => simpa using h.ne (by simpa using hu)
    | @cons v x w h' q =>
      have hux : u ∈ q.support := by
        simpa only [Walk.support_cons, List.mem_cons, h.ne, false_or] using hu
      rw [Walk.takeUntil_cons hux h.ne.symm] at ht
      have hx : x = u := by
        have he := congrArg (fun r => r.getVert 1) ht
        simpa using he
      exact hp.1 h' q rfl hx

theorem noReversal_vertices_nodup (hT : G.IsTree) {u v : V}
    (p : G.Walk u v) (hp : NoReversal p) : p.support.Nodup :=
  (noReversal_isPath hT p hp).support_nodup

#print axioms KroneckerTreeTraversalHelper.noReversal_isPath
#print axioms KroneckerTreeTraversalHelper.noReversal_vertices_nodup
end KroneckerTreeTraversalHelper
