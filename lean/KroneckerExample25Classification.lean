import KroneckerGeometricCounts

/-! The six unbounded grading cases in Example 2.19 for R₂ R₂ R₁. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option maxSynthPendingDepth 1024
set_option synthInstance.maxSize 4096
namespace KroneckerExample25
open KroneckerStack
attribute [local instance] Fintype.decidableForallFintype

def sixCases (a b c d e f g h : ℕ) : Prop :=
  (a = 3 ∧ d = 0 ∧ e = 0 ∧ b = 2 ∧ f = 0 ∧ g = 0 ∧ c = 0 ∧ h = 2) ∨
  (a = 4 ∧ d = 0 ∧ e = 0 ∧ b = 1 ∧ f = 0 ∧ g = 0 ∧ c = 0 ∧ h = 2) ∨
  (a = 4 ∧ d = 0 ∧ e = 0 ∧ b = 1 ∧ f = 0 ∧ g = 1 ∧ c = 0 ∧ h = 1) ∨
  (a = 5 ∧ d = 0 ∧ e = 0 ∧ b = 0 ∧ f = 0 ∧ g = 0 ∧ c = 0 ∧ h = 2) ∨
  (a = 5 ∧ d = 0 ∧ e = 0 ∧ b = 0 ∧ f = 1 ∧ g = 0 ∧ c = 0 ∧ h = 1) ∨
  (a = 5 ∧ d = 0 ∧ e = 0 ∧ b = 0 ∧ f = 0 ∧ g = 1 ∧ c = 0 ∧ h = 1)

private theorem initial_zeros (a b c d e f g h : ℕ)
    (hn : NodeRun [.H a, .V d, .V e, .H b, .V f, .V g, .H c, .V h] 0) :
    d = 0 ∧ e = 0 := by
  obtain ⟨r,rest,hw,he⟩ := hn
  simp only [List.cons.injEq, Edge.H.injEq] at hw
  rcases hw with ⟨rfl,rfl⟩
  have hd : d = 0 := by
    by_contra hd
    have hb : ¬(1 : ℤ) ≤ 1-(d : ℤ) := by omega
    simp [execute, step, hb] at he
  subst d
  have hv : e = 0 := by
    by_contra hv
    have hb : ¬(1 : ℤ) ≤ 1-(e : ℤ) := by omega
    by_cases hr : r = 0
    · subst r
      simp [execute, step] at he
    · simp [execute, step, hr, hb] at he
  exact ⟨rfl,hv⟩

theorem finite_classification : ∀ a b c : Fin 6, ∀ f g h : Fin 3,
    Connected 5 [.H a.val, .V 0, .V 0, .H b.val, .V f.val,
      .V g.val, .H c.val, .V h.val] 0 ↔
        sixCases a.val b.val c.val 0 0 f.val g.val h.val := by
  unfold Connected sixCases
  decide +kernel

theorem node_classification (a b c d e f g h : ℕ) :
    NodeRun [.H a, .V d, .V e, .H b, .V f, .V g, .H c, .V h] 0 ↔
      sixCases a b c d e f g h := by
  constructor
  · intro hn
    obtain ⟨rfl,rfl⟩ := initial_zeros a b c d e f g h hn
    have hh := node_debt_balance hn
    have hv := node_credit hn
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Edge.debtChange, Edge.credit, credit, Nat.cast_zero, zero_add, add_zero] at hh hv
    have hb : a ≤ 5 ∧ b ≤ 5 ∧ c ≤ 5 ∧ f ≤ 2 ∧ g ≤ 2 ∧ h ≤ 2 := by
      omega
    have hc : Connected 5 [.H a, .V 0, .V 0, .H b, .V f, .V g, .H c, .V h] 0 := by
      apply node_connected hn
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Edge.grade] <;> omega
    exact (finite_classification ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩
      ⟨f, by omega⟩ ⟨g, by omega⟩ ⟨h, by omega⟩).mp hc
  · intro hn
    rcases hn with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · exact ⟨2,_,rfl,by decide⟩
    · exact ⟨3,_,rfl,by decide⟩
    · exact ⟨3,_,rfl,by decide⟩
    · exact ⟨4,_,rfl,by decide⟩
    · exact ⟨4,_,rfl,by decide⟩
    · exact ⟨4,_,rfl,by decide⟩

end KroneckerExample25
