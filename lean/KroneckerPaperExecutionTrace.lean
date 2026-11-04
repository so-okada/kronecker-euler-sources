import KroneckerComponentRoots

/-!
# From accepted execution to the literal indexed trace

The list of a finite word in character order is identified with the existing
recursive `segment`.  The reverse execution-to-trace implication then follows
from the proved component dictionary: root positivity, positive proper
horizontal-capacity prefixes, the zero terminal capacity, and the guard at
each vertical occurrence are consequences of `NodeRun`, not extra premises.
-/
set_option autoImplicit false
namespace KroneckerPaperExecutionTrace
open KroneckerStack KroneckerCompatibility KroneckerShadow
open KroneckerComponent KroneckerComponentRoots

theorem orderedList_eq_segment (E : ℕ → Edge) (s len : ℕ) :
    (List.range' s len).map E = segment E s len := by
  induction len generalizing s with
  | zero => rfl
  | succ len ih => simp only [List.range'_succ, List.map_cons, KroneckerComponent.segment, ih]

/-- Acceptance supplies the complete horizontal-shadow component conditions. -/
theorem nodeRun_rootComponent {E : ℕ → Edge} {n c : ℕ}
    (hn : NodeRun ((List.range' 0 n).map E) c) : RootComponent E n := by
  rw [orderedList_eq_segment] at hn
  exact node_root_component hn

/-- Every unguarded trace of an accepted word satisfies the actual execution
inequalities, without an additional compatibility assumption. -/
theorem nodeRun_guarded_of_trace {E : ℕ → Edge} {n c : ℕ}
    {f : ℕ → List Entry} (hn : NodeRun ((List.range' 0 n).map E) c)
    (ht : RawTrace E n f) : Guarded E n f := by
  have hr := nodeRun_rootComponent hn
  rw [orderedList_eq_segment] at hn
  exact (compatibility_iff_guarded hr ht).mp (node_compatible hr hn)

/-- Accepted execution constructs a complete indexed trace with all guards. -/
theorem nodeRun_guardedTrace {E : ℕ → Edge} {n c : ℕ}
    (hn : NodeRun ((List.range' 0 n).map E) c) :
    ∃ f, RawTrace E n f ∧ Guarded E n f := by
  obtain ⟨f, ht⟩ := root_trace_exists (nodeRun_rootComponent hn)
  exact ⟨f, ht, nodeRun_guarded_of_trace hn ht⟩

/-- The existing grade-bounded acceptance predicate also supplies the trace;
its finite palette bound is not used to derive the trace properties. -/
theorem operational_guardedTrace {E : ℕ → Edge} {n m c : ℕ}
    (hc : KroneckerStack.Connected m ((List.range' 0 n).map E) c) :
    RootComponent E n ∧ ∃ f, RawTrace E n f ∧ Guarded E n f := by
  have hn := (connected_iff.mp hc).1
  exact ⟨nodeRun_rootComponent hn, nodeRun_guardedTrace hn⟩

#print axioms KroneckerPaperExecutionTrace.nodeRun_rootComponent
#print axioms KroneckerPaperExecutionTrace.nodeRun_guardedTrace
#print axioms KroneckerPaperExecutionTrace.operational_guardedTrace
end KroneckerPaperExecutionTrace
