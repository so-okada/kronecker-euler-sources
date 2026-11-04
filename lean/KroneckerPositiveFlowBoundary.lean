import KroneckerReflectedSourceGeneration

/- Original module: KroneckerFlowBoundaryIdentity -/
section
set_option autoImplicit false
namespace KroneckerFlowBoundaryIdentity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def boundaryFlux {I J : Type*} [Fintype I]
    (f : I → J → ℝ) (C : Finset I) (B : Finset J) := ∑ j∈B,∑ i∈Finset.univ\C,f i j

theorem boundary_demand_difference {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J → ℝ) (C : Finset I) (B : Finset J)
    (hclosed : ∀ i∈C,∀ j∉B,f i j=0) :
    (∑ j∈B,∑ i,f i j)-(∑ i∈C,∑ j,f i j)=boundaryFlux f C B := by
  have hrows : (∑ i∈C,∑ j,f i j)=∑ j∈B,∑ i∈C,f i j := by
    rw [Finset.sum_comm]
    apply Eq.symm
    apply Finset.sum_subset (Finset.subset_univ B)
    intro j _ hj
    exact Finset.sum_eq_zero (fun i hi => hclosed i hi j hj)
  rw [hrows,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := Finset.sum_sdiff (f:=fun i => f i j) (Finset.subset_univ C)
  linarith

theorem boundary_flux_nonnegative {I J : Type*} [Fintype I]
    (f : I → J → ℝ) (C : Finset I) (B : Finset J) (hf : ∀ i j,0≤f i j) :
    0≤boundaryFlux f C B := by
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => hf i j))

theorem boundary_flux_positive {I J : Type*} [Fintype I]
    (f : I → J → ℝ) (C : Finset I) (B : Finset J) (hf : ∀ i j,0≤f i j)
    (i : I) (j : J) (hi : i∉C) (hj : j∈B) (hij : 0<f i j) : 0<boundaryFlux f C B := by
  have hm : i∈Finset.univ\C := by simp [hi]
  have hl : f i j≤∑ k∈Finset.univ\C,f k j := Finset.single_le_sum (fun k _ => hf k j) hm
  have hr : (∑ k∈Finset.univ\C,f k j)≤boundaryFlux f C B :=
    Finset.single_le_sum (fun b _ => Finset.sum_nonneg (fun k _ => hf k b)) hj
  exact lt_of_lt_of_le hij (hl.trans hr)

end KroneckerFlowBoundaryIdentity
end

/- Original module: KroneckerPositiveFlowBoundary -/
section
set_option autoImplicit false
namespace KroneckerPositiveFlowBoundary
open SimpleGraph KroneckerBipartiteIncidence KroneckerReflectedSourceGeneration
open KroneckerFlowBoundaryIdentity
attribute [local instance] Classical.propDecidable

theorem occupied_boundary_exists {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hc : (incidenceGraph R).Connected) (C : Finset I) (B : Finset J)
    (hB : B.Nonempty) (hclosed : ∀ i∈C,∀ j,R i j → j∈B)
    (hproper : ¬(C=Finset.univ ∧ B=Finset.univ)) :
    ∃ i,i∉C ∧ ∃ j,j∈B ∧ R i j := by
  by_contra hcut
  push Not at hcut
  let P : I ⊕ J → Prop := fun v => match v with
    | .inl i => i∈C
    | .inr j => j∈B
  have hp : ∀ u v,(incidenceGraph R).Adj u v → P u → P v := by
    intro u v huv hu
    cases u with
    | inl i => cases v with
      | inl k => exact False.elim huv
      | inr j => exact hclosed i hu j huv
    | inr j => cases v with
      | inr k => exact False.elim huv
      | inl i =>
        by_contra hi
        exact hcut i hi j hu huv
  obtain ⟨j,hj⟩ := hB
  have hall : ∀ v,P v := fun v => reachable_closed P hp hj (hc (.inr j) v)
  apply hproper
  constructor
  · exact Finset.eq_univ_of_forall (fun i => hall (.inl i))
  · exact Finset.eq_univ_of_forall (fun j => hall (.inr j))

theorem positive_boundary_flux {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (hc : (incidenceGraph R).Connected)
    (f : I → J → ℝ) (hf : ∀ i j,0≤f i j) (hpos : ∀ i j,R i j → 0<f i j)
    (C : Finset I) (B : Finset J) (hB : B.Nonempty)
    (hclosed : ∀ i∈C,∀ j,R i j → j∈B) (hproper : ¬(C=Finset.univ ∧ B=Finset.univ)) :
    0<boundaryFlux f C B := by
  obtain ⟨i,hi,j,hj,hij⟩ := occupied_boundary_exists R hc C B hB hclosed hproper
  exact boundary_flux_positive f C B hf i j hi hj (hpos i j hij)

end KroneckerPositiveFlowBoundary
end
