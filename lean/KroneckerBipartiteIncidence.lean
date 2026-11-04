import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/- Original module: KroneckerForestDegreeCount -/
section
set_option autoImplicit false
namespace KroneckerForestDegreeCount
open SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem component_degree {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : G.ConnectedComponent) (v : c) : c.toSimpleGraph.degree v=G.degree v := by
  classical
  apply G.degree_induce_of_neighborSet_subset
  intro w hw
  exact c.mem_supp_of_adj_mem_supp v.2 hw

theorem sum_component_vertices {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] :
    (∑ c : G.ConnectedComponent,Fintype.card c)=Fintype.card V := by
  classical
  change (∑ c : G.ConnectedComponent, Fintype.card {v : V // G.connectedComponentMk v = c}) =
    Fintype.card V
  simpa using Fintype.sum_fiberwise G.connectedComponentMk (fun _ : V => (1 : ℕ))

/-- The forest identity is proved from the actual connected components. -/
theorem forest_degree_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] (h : G.IsAcyclic) :
    (∑ v,G.degree v)+2*Fintype.card G.ConnectedComponent=2*Fintype.card V := by
  classical
  have hc : ∀ c : G.ConnectedComponent,
      (∑ v : c,G.degree v)+2=2*Fintype.card c := by
    intro c
    have ht := (h.isTree_connectedComponent c).card_edgeFinset
    have hd := c.toSimpleGraph.sum_degrees_eq_twice_card_edges
    simp only [component_degree] at hd
    omega
  have hs := congrArg (fun f : G.ConnectedComponent → ℕ => ∑ c,f c) (funext hc)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    ←Finset.mul_sum,sum_component_vertices] at hs
  have hf : (∑ c : G.ConnectedComponent,∑ v : c,G.degree v)=∑ v,G.degree v := by
    exact Fintype.sum_fiberwise G.connectedComponentMk (fun v => G.degree v)
  rw [hf] at hs
  omega

theorem forest_degree_bound {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] (h : G.IsAcyclic) :
    (∑ v,G.degree v)+2≤2*Fintype.card V := by
  haveI : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  have hp := Fintype.card_pos (α:=G.ConnectedComponent)
  have hc := forest_degree_count G h
  omega

end KroneckerForestDegreeCount
end

/- Original module: KroneckerBipartiteIncidence -/
section
set_option autoImplicit false
namespace KroneckerBipartiteIncidence
open SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def incidenceGraph {I J : Type*} (R : I → J → Prop) : SimpleGraph (I ⊕ J) where
  Adj
  | .inl i,.inr j => R i j
  | .inr j,.inl i => R i j
  | _,_ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

def leftNeighbors {I J : Type*} (R : I → J → Prop) (i : I) :
    (incidenceGraph R).neighborSet (.inl i) ≃ {j // R i j} where
  toFun v := by
    rcases v with ⟨v,h⟩
    cases v with
    | inl k => exact False.elim h
    | inr j => exact ⟨j,h⟩
  invFun j := ⟨.inr j,j.2⟩
  left_inv := by rintro ⟨v,h⟩; cases v with
    | inl k => exact False.elim h
    | inr j => rfl
  right_inv := by intro j; rfl

def rightNeighbors {I J : Type*} (R : I → J → Prop) (j : J) :
    (incidenceGraph R).neighborSet (.inr j) ≃ {i // R i j} where
  toFun v := by
    rcases v with ⟨v,h⟩
    cases v with
    | inl i => exact ⟨i,h⟩
    | inr k => exact False.elim h
  invFun i := ⟨.inl i,i.2⟩
  left_inv := by rintro ⟨v,h⟩; cases v with
    | inl i => rfl
    | inr k => exact False.elim h
  right_inv := by intro i; rfl

theorem left_degree {I J : Type*} [Fintype I] [Fintype J] (R : I → J → Prop) (i : I) :
    (incidenceGraph R).degree (.inl i)=Fintype.card {j // R i j} :=
  by simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr (leftNeighbors R i)

theorem right_degree {I J : Type*} [Fintype I] [Fintype J] (R : I → J → Prop) (j : J) :
    (incidenceGraph R).degree (.inr j)=Fintype.card {i // R i j} :=
  by simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr (rightNeighbors R j)

theorem incidence_double_count {I J : Type*} [Fintype I] [Fintype J] (R : I → J → Prop) :
    (∑ i,Fintype.card {j // R i j})=∑ j,Fintype.card {i // R i j} := by
  simp only [Fintype.card_subtype,Finset.card_filter]
  exact Finset.sum_comm

theorem incidence_degree_sum {I J : Type*} [Fintype I] [Fintype J] (R : I → J → Prop) :
    (∑ v,(incidenceGraph R).degree v)=2*∑ i,Fintype.card {j // R i j} := by
  rw [Fintype.sum_sum_type]
  simp only [left_degree,right_degree]
  rw [←incidence_double_count]
  omega

end KroneckerBipartiteIncidence
end
