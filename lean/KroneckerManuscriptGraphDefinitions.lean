import KroneckerBipartiteIncidence
import Mathlib.Combinatorics.SimpleGraph.Bipartite

set_option autoImplicit false
namespace KroneckerManuscriptGraphs

def Bipartition {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ A ∪ B = Set.univ ∧
    ∀ v w, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A)

theorem incidence_bipartition {I J : Type*} (R : I → J → Prop) :
    Bipartition (KroneckerBipartiteIncidence.incidenceGraph R)
      (Set.range Sum.inl) (Set.range Sum.inr) := by
  refine ⟨Set.disjoint_left.mpr ?_, ?_, ?_⟩
  · rintro v ⟨i, rfl⟩ ⟨j, h⟩
    cases h
  · ext v
    cases v <;> simp
  · intro v w h
    cases v <;> cases w <;>
      simp_all [KroneckerBipartiteIncidence.incidenceGraph]

theorem bipartition_iff_bipartite {V : Type*} (G : SimpleGraph V) :
    (∃ A B, Bipartition G A B) ↔ G.IsBipartite := by
  classical
  constructor
  · rintro ⟨A, B, hd, _, he⟩
    exact SimpleGraph.IsBipartiteWith.isBipartite ⟨hd, fun _ _ h => he _ _ h⟩
  · rintro ⟨c, hc⟩
    refine ⟨{v | c v = 0}, {v | c v = 1}, ?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr (by intro v h0 h1; simp_all)
    · ext v
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have h := (c v).isLt
      omega
    · intro v w h
      have hh := hc h
      simp only [Set.mem_ofPred_eq]
      generalize hv : c v = a at *
      generalize hw : c w = b at *
      fin_cases a <;> fin_cases b <;> simp_all

def Leaf {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : Prop := G.degree v = 1

theorem left_leaf_iff {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (i : I) :
    letI := Classical.propDecidable
    Leaf (KroneckerBipartiteIncidence.incidenceGraph R) (Sum.inl i) ↔
      Fintype.card {j // R i j} = 1 := by
  classical
  exact congrArg (fun n : ℕ => n = 1)
    (KroneckerBipartiteIncidence.left_degree R i) |>.to_iff

theorem right_leaf_iff {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (j : J) :
    letI := Classical.propDecidable
    Leaf (KroneckerBipartiteIncidence.incidenceGraph R) (Sum.inr j) ↔
      Fintype.card {i // R i j} = 1 := by
  classical
  exact congrArg (fun n : ℕ => n = 1)
    (KroneckerBipartiteIncidence.right_degree R j) |>.to_iff

end KroneckerManuscriptGraphs
