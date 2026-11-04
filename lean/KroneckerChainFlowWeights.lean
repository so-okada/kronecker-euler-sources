import KroneckerChainIncidence

set_option autoImplicit false
namespace KroneckerChainFlowWeights
open KroneckerChainIncidence KroneckerIncidenceDivergence KroneckerFlowEdgeExtension
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def weight {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) (i : Connector n) : Block n → ℝ
  | .inl j => (if j=i.castSucc then l i else 0)+(if j=i.succ then r i else 0)
  | .inr j => if j=i then x+1-l i-r i else 0

noncomputable def chainFlow {n : ℕ} (x : ℝ) (l r : ℕ → ℝ)
    (e : Edge (@incidence n)) : ℝ := weight x l r e.1.1 e.1.2

theorem weight_off_edge {n : ℕ} (x : ℝ) (l r : ℕ → ℝ)
    (i : Connector n) (j : Block n) (h : ¬incidence i j) : weight x l r i j=0 := by
  cases j <;> simp_all [incidence,weight]

theorem flow_extension {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) (i : Connector n) (j : Block n) :
    extendFlow (chainFlow x l r) i j=weight x l r i j := by
  by_cases h : incidence i j
  · simp [extendFlow,chainFlow,h]
  · simp [extendFlow,h,weight_off_edge x l r i j h]

theorem row_balance {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) (i : Connector n) :
    (∑ j,extendFlow (chainFlow x l r) i j)=x+1 := by
  simp only [flow_extension,Fintype.sum_sum_type,weight,Finset.sum_add_distrib]
  simp

theorem port_weights {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) (i : Connector n) :
    weight x l r i (portBlock i 0)=l i ∧
    weight x l r i (portBlock i 1)=x+1-l i-r i ∧
    weight x l r i (portBlock i 2)=r i := by
  have hn : i.castSucc≠i.succ := by intro h; have hh := congrArg Fin.val h; simp at hh
  simp [portBlock,weight,hn,Ne.symm hn]

theorem flow_positive_iff {n : ℕ} (x : ℝ) (l r : ℕ → ℝ) :
    (∀ e : Edge (@incidence n),0<chainFlow x l r e) ↔
      ∀ i : Connector n,0<l i ∧ 0<x+1-l i-r i ∧ 0<r i := by
  constructor
  · intro h i
    have h0 := h ⟨(i,portBlock i 0),port_incident i 0⟩
    have h1 := h ⟨(i,portBlock i 1),port_incident i 1⟩
    have h2 := h ⟨(i,portBlock i 2),port_incident i 2⟩
    exact ⟨(port_weights x l r i).1 ▸ h0,
      (port_weights x l r i).2.1 ▸ h1,(port_weights x l r i).2.2 ▸ h2⟩
  · intro h e
    obtain ⟨p,hp⟩ := (incident_iff_port e.1.1 e.1.2).mp e.2
    change 0<weight x l r e.1.1 e.1.2
    rw [←hp]
    fin_cases p
    · change 0<weight x l r e.1.1 (portBlock e.1.1 0)
      rw [(port_weights x l r e.1.1).1]; exact (h e.1.1).1
    · change 0<weight x l r e.1.1 (portBlock e.1.1 1)
      rw [(port_weights x l r e.1.1).2.1]; exact (h e.1.1).2.1
    · change 0<weight x l r e.1.1 (portBlock e.1.1 2)
      rw [(port_weights x l r e.1.1).2.2]; exact (h e.1.1).2.2

end KroneckerChainFlowWeights
