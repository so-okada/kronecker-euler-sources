import KroneckerGeometricCounts

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace KroneckerSmallFrameClassification
open KroneckerStack

def threeCases (a b c d e f : ℕ) : Prop :=
  (a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 2) ∨
  (a = 3 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 2) ∨
  (a = 3 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 1 ∧ f = 1)

theorem finite_classification : ∀ a b c : Fin 4, ∀ d e f : Fin 3,
    Connected 3 [.H a.val, .V d.val, .H b.val, .V e.val, .H c.val, .V f.val] 0 ↔
      threeCases a.val b.val c.val d.val e.val f.val := by
  unfold Connected threeCases
  intro a b c d e f
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f <;> decide

theorem node_classification (a b c d e f : ℕ) :
    NodeRun [.H a, .V d, .H b, .V e, .H c, .V f] 0 ↔ threeCases a b c d e f := by
  constructor
  · intro h
    have hh := node_debt_balance h
    have hv := node_credit h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Edge.debtChange, Edge.credit, credit, Nat.cast_zero, zero_add, add_zero] at hh hv
    have hb : a ≤ 3 ∧ b ≤ 3 ∧ c ≤ 3 ∧ d ≤ 2 ∧ e ≤ 2 ∧ f ≤ 2 := by
      omega
    have hc : Connected 3 [.H a, .V d, .H b, .V e, .H c, .V f] 0 := by
      apply node_connected h
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Edge.grade] <;> omega
    exact (finite_classification ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩
      ⟨d, by omega⟩ ⟨e, by omega⟩ ⟨f, by omega⟩).mp hc
  · intro h
    rcases h with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ |
      ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    · exact ⟨1,_,rfl,by decide⟩
    · exact ⟨2,_,rfl,by decide⟩
    · exact ⟨2,_,rfl,by decide⟩

end KroneckerSmallFrameClassification
