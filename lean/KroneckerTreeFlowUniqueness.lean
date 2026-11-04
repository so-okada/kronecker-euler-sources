import KroneckerReflectionKernel
import KroneckerBipartiteIncidence

/- Original module: KroneckerBalancedVertexSpace -/
section
set_option autoImplicit false
namespace KroneckerBalancedVertexSpace
open Module
open scoped BigOperators

noncomputable def totalMap (V : Type*) [Fintype V] : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ v,x v
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

noncomputable abbrev Balanced (V : Type*) [Fintype V] := LinearMap.ker (totalMap V)

theorem totalMap_surjective (V : Type*) [Fintype V] [Nonempty V] :
    Function.Surjective (totalMap V) := by
  classical
  intro c
  exact ⟨Pi.single (Classical.arbitrary V) c,by simp [totalMap]⟩

theorem balanced_dimension (V : Type*) [Fintype V] [Nonempty V] :
    finrank ℝ (Balanced V)+1=Fintype.card V := by
  have h := (totalMap V).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (totalMap_surjective V)] at h
  simpa [Balanced,add_comm] using h

noncomputable def pointDifference {V : Type*} (u v : V) : V → ℝ := by
  classical
  exact Pi.single u 1-Pi.single v 1

theorem point_difference_balanced {V : Type*} [Fintype V] (u v : V) :
    pointDifference u v∈Balanced V := by
  classical
  change ∑ w,pointDifference u v w=0
  simp [pointDifference,Finset.sum_sub_distrib]

theorem point_difference_trans {V : Type*} (u v w : V) :
    pointDifference u v+pointDifference v w=pointDifference u w := by
  unfold pointDifference
  abel

/-- A balanced demand is an explicit sum of differences from any chosen root. -/
theorem balanced_decomposition {V : Type*} [Fintype V] (x : V → ℝ) (r : V)
    (hx : x∈Balanced V) : ∑ v,x v • pointDifference v r=x := by
  classical
  have ht : ∑ v,x v=0 := hx
  have hd : ∑ v,x v • (Pi.single v (1 : ℝ) : V → ℝ)=x := by
    ext w
    simp [Pi.single_apply]
  simp only [pointDifference,smul_sub,Finset.sum_sub_distrib]
  rw [hd,←Finset.sum_smul,ht,zero_smul,sub_zero]

end KroneckerBalancedVertexSpace
end

/- Original module: KroneckerIncidenceDivergence -/
section
set_option autoImplicit false
namespace KroneckerIncidenceDivergence
open KroneckerBalancedVertexSpace
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Edge {I J : Type*} (R : I → J → Prop) := {p : I × J // R p.1 p.2}

noncomputable def column {I J : Type*} {R : I → J → Prop} (e : Edge R) : I ⊕ J → ℝ :=
  pointDifference (.inl e.1.1) (.inr e.1.2)

noncomputable def divergence {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) : (Edge R → ℝ) →ₗ[ℝ] (I ⊕ J → ℝ) where
  toFun f := ∑ e,f e • column e
  map_add' := by intros; simp [add_smul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [mul_smul,Finset.smul_sum]

theorem divergence_balanced {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (f : Edge R → ℝ) : divergence R f∈Balanced (I ⊕ J) := by
  apply Submodule.sum_mem
  intro e _
  exact Submodule.smul_mem _ _ (point_difference_balanced _ _)

theorem column_in_range {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (e : Edge R) : column e∈LinearMap.range (divergence R) := by
  classical
  exact ⟨Pi.single e 1,by simp [divergence]⟩

theorem divergence_left {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (f : Edge R → ℝ) (i : I) :
    divergence R f (.inl i)=∑ e,if e.1.1=i then f e else 0 := by
  classical
  simp [divergence,column,pointDifference,Pi.single_apply,eq_comm]

theorem divergence_right {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (f : Edge R → ℝ) (j : J) :
    divergence R f (.inr j)=-(∑ e,if e.1.2=j then f e else 0) := by
  classical
  simp [divergence,column,pointDifference,Pi.single_apply,Finset.sum_neg_distrib,eq_comm]

end KroneckerIncidenceDivergence
end

/- Original module: KroneckerConnectedIncidenceRange -/
section
set_option autoImplicit false
namespace KroneckerConnectedIncidenceRange
open SimpleGraph KroneckerBipartiteIncidence KroneckerBalancedVertexSpace
open KroneckerIncidenceDivergence
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem adjacent_difference_in_range {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} {u v : I ⊕ J} (h : (incidenceGraph R).Adj u v) :
    pointDifference u v∈LinearMap.range (divergence R) := by
  cases u with
  | inl i => cases v with
    | inl k => exact False.elim h
    | inr j => exact column_in_range (⟨(i,j),h⟩ : Edge R)
  | inr j => cases v with
    | inr k => exact False.elim h
    | inl i =>
      simpa [column,pointDifference,neg_sub] using
        (LinearMap.range (divergence R)).neg_mem (column_in_range (⟨(i,j),h⟩ : Edge R))

theorem walk_difference_in_range {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} {u v : I ⊕ J} (p : (incidenceGraph R).Walk u v) :
    pointDifference u v∈LinearMap.range (divergence R) := by
  induction p with
  | nil => simp [pointDifference]
  | @cons u v w h p ih =>
    rw [←point_difference_trans u v w]
    exact Submodule.add_mem _ (adjacent_difference_in_range h) ih

/-- Connectedness alone identifies the range; acyclicity is not presumed. -/
theorem connected_incidence_range {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hc : (incidenceGraph R).Connected) :
    LinearMap.range (divergence R)=Balanced (I ⊕ J) := by
  apply le_antisymm
  · rintro x ⟨f,rfl⟩
    exact divergence_balanced R f
  · intro x hx
    let r : I ⊕ J := Classical.choice hc.nonempty
    rw [←balanced_decomposition x r hx]
    apply Submodule.sum_mem
    intro v _
    obtain ⟨p⟩ := hc v r
    exact Submodule.smul_mem _ _ (walk_difference_in_range p)

end KroneckerConnectedIncidenceRange
end

/- Original module: KroneckerTreeFlowUniqueness -/
section
set_option autoImplicit false
namespace KroneckerTreeFlowUniqueness
open SimpleGraph Module KroneckerBipartiteIncidence KroneckerBalancedVertexSpace
open KroneckerIncidenceDivergence KroneckerConnectedIncidenceRange
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem incidence_edge_count {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) : Fintype.card (Edge R)=∑ i,Fintype.card {j // R i j} := by
  classical
  simp only [Edge,Fintype.card_subtype,Finset.card_filter,Fintype.sum_prod_type]

theorem tree_edge_count {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree) :
    Fintype.card (Edge R)+1=Fintype.card (I ⊕ J) := by
  classical
  have he := hT.card_edgeFinset
  have hd := (incidenceGraph R).sum_degrees_eq_twice_card_edges
  rw [incidence_degree_sum,←incidence_edge_count] at hd
  omega

theorem tree_divergence_injective {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree) :
    Function.Injective (divergence R) := by
  let : Nonempty (I ⊕ J) := hT.connected.nonempty
  have he := tree_edge_count R hT
  have hd := balanced_dimension (I ⊕ J)
  have hr := (divergence R).finrank_range_add_finrank_ker
  rw [connected_incidence_range R hT.connected] at hr
  have hv : finrank ℝ (Edge R → ℝ)=Fintype.card (Edge R) := by simp
  rw [hv] at hr
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  omega

/-- Every balanced real demand on a finite bipartite tree has exactly one flow. -/
theorem unique_tree_flow {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (d : I ⊕ J → ℝ) (hd : d∈Balanced (I ⊕ J)) :
    ∃! f : Edge R → ℝ,divergence R f=d := by
  have hr : d∈LinearMap.range (divergence R) := by
    rw [connected_incidence_range R hT.connected]
    exact hd
  obtain ⟨f,hf⟩ := hr
  exact ⟨f,hf,fun g hg => tree_divergence_injective R hT (hg.trans hf.symm)⟩

end KroneckerTreeFlowUniqueness
end
