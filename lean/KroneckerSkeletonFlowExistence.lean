import KroneckerTreeFlowUniqueness
import Mathlib.Data.Fintype.BigOperators
import KroneckerSaturatedTreeDimensions

/- Original module: KroneckerFlowEdgeExtension -/
section
set_option autoImplicit false
namespace KroneckerFlowEdgeExtension
open KroneckerIncidenceDivergence
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def extendFlow {I J : Type*} {R : I → J → Prop}
    (f : Edge R → ℝ) (i : I) (j : J) : ℝ := if h : R i j then f ⟨(i,j),h⟩ else 0

theorem extend_on_edge {I J : Type*} {R : I → J → Prop}
    (f : Edge R → ℝ) (i : I) (j : J) (h : R i j) :
    extendFlow f i j=f ⟨(i,j),h⟩ := by simp [extendFlow,h]

theorem extend_off_edge {I J : Type*} {R : I → J → Prop}
    (f : Edge R → ℝ) (i : I) (j : J) (h : ¬R i j) : extendFlow f i j=0 := by
  simp [extendFlow,h]

theorem edge_extension_injective {I J : Type*} {R : I → J → Prop} :
    Function.Injective (@extendFlow I J R) := by
  intro f g h
  funext e
  have he := congrFun (congrFun h e.1.1) e.1.2
  simpa [extendFlow,e.2] using he

theorem weighted_extension_sum {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (f : Edge R → ℝ) (g : I → J → ℝ) :
    (∑ i,∑ j,g i j*extendFlow f i j)=∑ e,g e.1.1 e.1.2*f e := by
  rw [←Fintype.sum_prod_type (fun p : I × J => g p.1 p.2*extendFlow f p.1 p.2)]
  let z : I × J → ℝ := fun p => g p.1 p.2*extendFlow f p.1 p.2
  have hs : (∑ p,z p)=∑ p∈Finset.univ.filter (fun p : I × J => R p.1 p.2),z p := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p _ hp
    have hn : ¬R p.1 p.2 := by simpa using hp
    simp [z,extendFlow,hn]
  rw [hs,Finset.sum_subtype _ (p:=fun p : I × J => R p.1 p.2) (F:=inferInstance) (by simp)]
  apply Finset.sum_congr rfl
  intro e _
  simp [z,extendFlow,e.2]

theorem extended_row {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (f : Edge R → ℝ) (i : I) :
    (∑ j,extendFlow f i j)=divergence R f (.inl i) := by
  classical
  rw [divergence_left]
  simpa [ite_mul] using weighted_extension_sum f (fun k _ => if k=i then 1 else 0)

theorem extended_column {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (f : Edge R → ℝ) (j : J) :
    (∑ i,extendFlow f i j)= -divergence R f (.inr j) := by
  classical
  rw [divergence_right,neg_neg]
  simpa [ite_mul] using weighted_extension_sum f (fun _ k => if k=j then 1 else 0)

end KroneckerFlowEdgeExtension
end

/- Original module: KroneckerSkeletonFlowExistence -/
section
set_option autoImplicit false
namespace KroneckerSkeletonFlowExistence
open SimpleGraph KroneckerBipartiteIncidence KroneckerBalancedVertexSpace
open KroneckerIncidenceDivergence KroneckerTreeFlowUniqueness
open KroneckerFlowEdgeExtension KroneckerSaturatedTreeDimensions
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def demand {I J : Type*} (x : ℝ) (a : J → ℕ) : I ⊕ J → ℝ
  | .inl _ => x+1
  | .inr j => (a j : ℝ)-x

def FlowEquations {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (x : ℝ) (a : J → ℕ) (f : Edge R → ℝ) : Prop :=
  (∀ i,∑ j,extendFlow f i j=x+1) ∧ (∀ j,∑ i,extendFlow f i j=x-a j)

theorem flow_equations_iff_divergence {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (x : ℝ) (a : J → ℕ) (f : Edge R → ℝ) :
    FlowEquations x a f ↔ divergence R f=demand (I:=I) x a := by
  constructor
  · rintro ⟨hl,hr⟩
    funext v
    cases v with
    | inl i => simpa [demand,extended_row] using hl i
    | inr j =>
      have h := hr j
      rw [extended_column] at h
      dsimp [demand]
      linarith
  · intro h
    constructor
    · intro i
      rw [extended_row,h]
      rfl
    · intro j
      rw [extended_column,h]
      simp [demand]

theorem skeleton_demand_balanced {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (x : ℝ) (a : J → ℕ)
    (ha : (∑ j,(a j : ℝ))+(Fintype.card I : ℝ)=x*((Fintype.card I : ℝ)+1)) :
    demand (I:=I) x a∈Balanced (I ⊕ J) := by
  have hc : (Fintype.card J : ℝ)=2*(Fintype.card I : ℝ)+1 := by
    exact_mod_cast saturated_tree_sink_count R hT h3
  change ∑ v,demand x a v=0
  simp only [Fintype.sum_sum_type,demand,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  rw [hc]
  nlinarith

/-- The manuscript's tree flow is constructed from its total-dimension identity. -/
theorem unique_skeleton_flow {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (x : ℝ) (a : J → ℕ)
    (ha : (∑ j,(a j : ℝ))+(Fintype.card I : ℝ)=x*((Fintype.card I : ℝ)+1)) :
    ∃! f : Edge R → ℝ,FlowEquations x a f := by
  obtain ⟨f,hf,hu⟩ := unique_tree_flow R hT (demand x a)
    (skeleton_demand_balanced R hT h3 x a ha)
  exact ⟨f,(flow_equations_iff_divergence x a f).mpr hf,
    fun g hg => hu g ((flow_equations_iff_divergence x a g).mp hg)⟩

end KroneckerSkeletonFlowExistence
end
