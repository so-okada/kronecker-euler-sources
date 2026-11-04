import KroneckerSaturatedTreeDimensions

section

/- Original module: KroneckerSelectedIncidenceForest -/
section
set_option autoImplicit false
namespace KroneckerSelectedIncidenceForest
open SimpleGraph KroneckerBipartiteIncidence KroneckerForestDegreeCount
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def neighbors {I J : Type*} [Fintype J] (R : I → J → Prop) (s : Finset I) : Finset J :=
  Finset.univ.filter (fun j => ∃ i∈s,R i j)

def selectedRelation {I J : Type*} [Fintype J] (R : I → J → Prop) (s : Finset I)
    (i : s) (j : neighbors R s) : Prop := R i j

theorem selected_left_card {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (s : Finset I) (i : s) :
    Fintype.card {j // selectedRelation R s i j}=Fintype.card {j // R i j} := by
  apply Fintype.card_congr
  exact {
    toFun := fun j => ⟨j.1.1,j.2⟩
    invFun := fun j => ⟨⟨j.1,by simp [neighbors]; exact ⟨i,i.2,j.2⟩⟩,j.2⟩
    left_inv := by intro j; rfl
    right_inv := by intro j; rfl }

theorem selected_acyclic {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (s : Finset I) (h : (incidenceGraph R).IsAcyclic) :
    (incidenceGraph (selectedRelation R s)).IsAcyclic := by
  let f : incidenceGraph (selectedRelation R s) →g incidenceGraph R := {
    toFun := Sum.map Subtype.val Subtype.val
    map_rel' := by intro a b h; cases a <;> cases b <;> exact h }
  apply h.comap f
  exact Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩

/-- The incident forest of a nonempty source subset has at least 2v+1 neighboring sinks. -/
theorem selected_neighbor_bound {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (h : (incidenceGraph R).IsAcyclic)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (s : Finset I) (hs : s.Nonempty) :
    2*s.card+1≤(neighbors R s).card := by
  classical
  let G := incidenceGraph (selectedRelation R s)
  haveI : Nonempty ↥s := hs.to_subtype
  let : Finite G.ConnectedComponent := Quot.finite _
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hb := forest_degree_bound G (selected_acyclic R s h)
  rw [incidence_degree_sum] at hb
  simp only [selected_left_card,h3,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    Fintype.card_sum,Fintype.card_coe] at hb
  omega

end KroneckerSelectedIncidenceForest
end

/- Original module: KroneckerReflectionCapacity -/
section
set_option autoImplicit false
namespace KroneckerReflectionCapacity
open SimpleGraph KroneckerBipartiteIncidence KroneckerSelectedIncidenceForest
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def selectedDegree {I J : Type*} (R : I → J → Prop)
    (s : Finset I) (j : J) := (s.filter (fun i => R i j)).card

theorem selected_degree_positive {I J : Type*} [Fintype J] (R : I → J → Prop)
    (s : Finset I) (j : J) : 0<selectedDegree R s j ↔ j∈neighbors R s := by
  simp [selectedDegree,Finset.card_pos,Finset.filter_nonempty_iff,neighbors]

theorem selected_degree_total {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (h3 : ∀ i,Fintype.card {j // R i j}=3) (s : Finset I) :
    (∑ j,selectedDegree R s j)=3*s.card := by
  simp only [selectedDegree,Finset.card_filter]
  rw [Finset.sum_comm]
  have hc : ∀ i, (∑ j : J,if R i j then 1 else 0)=3 := by
    intro i
    simpa only [Fintype.card_subtype,Finset.card_filter] using h3 i
  simp only [hc,Finset.sum_const,smul_eq_mul]
  omega

theorem capacity_identity {I J : Type*} [Fintype J] (R : I → J → Prop) (s : Finset I) :
    (∑ j,(selectedDegree R s j-1))+(neighbors R s).card=∑ j,selectedDegree R s j := by
  have hp : ∀ j,(selectedDegree R s j-1)+(if j∈neighbors R s then 1 else 0)=selectedDegree R s j := by
    intro j
    have h := selected_degree_positive R s j
    by_cases hj : j∈neighbors R s
    · rw [ite_eq_left hj]
      have hq := h.mpr hj
      omega
    · rw [ite_eq_right hj]
      have hq : selectedDegree R s j=0 := by have := mt h.mp hj; omega
      rw [hq]
  have hs := congrArg (fun f : J → ℕ => ∑ j,f j) (funext hp)
  simpa [Finset.sum_add_distrib] using hs

/-- Total reflected source capacity is strictly below the selected sink count. -/
theorem reflected_capacity_bound {I J : Type*} [Fintype I] [Fintype J]
    (R : I → J → Prop) (h : (incidenceGraph R).IsAcyclic)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (s : Finset I) (hs : s.Nonempty) :
    (∑ j,(selectedDegree R s j-1))<s.card := by
  have hN := selected_neighbor_bound R h h3 s hs
  have hc := capacity_identity R s
  rw [selected_degree_total R h3] at hc
  omega

end KroneckerReflectionCapacity
end

/- Original module: KroneckerReflectedSubrepresentations -/
section
set_option autoImplicit false
namespace KroneckerReflectedSubrepresentations
open Module KroneckerReflectionKernel KroneckerReflectionCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure ReflectedSubrep {I J : Type*} [Fintype I] (R : I → J → Prop) where
  source : ∀ j,Submodule ℂ (Kernel {i // R i j})
  sink : I → Submodule ℂ ℂ
  invariant : ∀ j i (h : R i j) x,x∈source j → projection ⟨i,h⟩ x∈sink i

noncomputable def selected {I J : Type*} [Fintype I] {R : I → J → Prop}
    (S : ReflectedSubrep R) := Finset.univ.filter (fun i => S.sink i≠⊥)

theorem complex_submodule_dimension (B : Submodule ℂ ℂ) :
    finrank ℂ B=if B=⊥ then 0 else 1 := by
  by_cases h : B=⊥
  · simp [h]
  · have hp := Submodule.one_le_finrank_iff.mpr h
    have hb : finrank ℂ B≤1 := by simpa using B.finrank_le
    simp only [ite_eq_right h]
    omega

theorem selected_sink_dimension {I J : Type*} [Fintype I] {R : I → J → Prop}
    (S : ReflectedSubrep R) : (∑ i,finrank ℂ (S.sink i))=(selected S).card := by
  simp only [complex_submodule_dimension,selected,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

noncomputable def selectedCoordinates {I J : Type*} [Fintype I]
    (R : I → J → Prop) (s : Finset I) (j : J) : Finset {i // R i j} :=
  Finset.univ.filter (fun i => i.1∈s)

theorem selected_coordinates_card {I J : Type*} [Fintype I]
    (R : I → J → Prop) (s : Finset I) (j : J) :
    (selectedCoordinates R s j).card=selectedDegree R s j := by
  unfold selectedDegree
  apply Finset.card_bij (fun i _ => i.1)
  · intro i hi
    simp only [selectedCoordinates,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    exact Finset.mem_filter.mpr ⟨hi,i.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro i hi
    refine ⟨⟨i,(Finset.mem_filter.mp hi).2⟩,?_,rfl⟩
    simpa [selectedCoordinates] using (Finset.mem_filter.mp hi).1

theorem subrep_coordinate_support {I J : Type*} [Fintype I] {R : I → J → Prop}
    (S : ReflectedSubrep R) (j : J) (x : S.source j) (i : {i // R i j})
    (hi : i∉selectedCoordinates R (selected S) j) : (x.1 : {i // R i j} → ℂ) i=0 := by
  have hbot : S.sink i.1=⊥ := by simpa [selectedCoordinates,selected] using hi
  have hx := S.invariant j i.1 i.2 x.1 x.2
  rw [hbot] at hx
  exact hx

theorem subrep_source_capacity {I J : Type*} [Fintype I] {R : I → J → Prop}
    (S : ReflectedSubrep R) (j : J) :
    finrank ℂ (S.source j)≤selectedDegree R (selected S) j-1 := by
  have h := KroneckerSupportedReflectionKernel.supported_subspace_dimension
    (selectedCoordinates R (selected S) j) (S.source j) (subrep_coordinate_support S j)
  simpa [selected_coordinates_card] using h

end KroneckerReflectedSubrepresentations
end

/- Original module: KroneckerReflectedBlockStability -/
section
set_option autoImplicit false
namespace KroneckerReflectedBlockStability
open SimpleGraph Module KroneckerBipartiteIncidence KroneckerSaturatedTreeDimensions
open KroneckerReflectedSubrepresentations KroneckerReflectionCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem empty_selected_source_zero {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (S : ReflectedSubrep R) (hs : selected S=∅) :
    (∑ j,finrank ℂ (S.source j))=0 := by
  apply Finset.sum_eq_zero
  intro j _
  have h := subrep_source_capacity S j
  simpa [hs,selectedDegree] using h

/-- The strict integral defect is proved for arbitrary vertexwise subspaces. -/
theorem reflected_subrepresentation_defect {I J : Type*} [Fintype I] [Fintype J]
    {R : I → J → Prop} (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) (S : ReflectedSubrep R)
    (hn : 0<(∑ j,finrank ℂ (S.source j))+(∑ i,finrank ℂ (S.sink i))) :
    (∑ j,finrank ℂ (S.source j))<∑ i,finrank ℂ (S.sink i) := by
  rw [selected_sink_dimension] at hn ⊢
  have hs : (selected S).Nonempty := by
    by_contra h
    have he : selected S=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hz := empty_selected_source_zero S he
    simp [he,hz] at hn
  have hc := reflected_capacity_bound R hT.isAcyclic h3 (selected S) hs
  exact lt_of_le_of_lt (Finset.sum_le_sum (fun j _ => subrep_source_capacity S j)) hc


end KroneckerReflectedBlockStability
end
end

section

set_option autoImplicit false
namespace KroneckerReflectedSourceGeneration
open SimpleGraph Module KroneckerBipartiteIncidence KroneckerReflectionKernel
attribute [local instance] Classical.propDecidable

theorem reachable_closed {V : Type*} {G : SimpleGraph V} (P : V → Prop)
    (h : ∀ u v,G.Adj u v → P u → P v) {u v : V} (hu : P u) (hr : G.Reachable u v) : P v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hu
  | @cons a b c hab p ih => exact ih (h a b hab hu)

theorem nonleaf_neighbor {I J : Type*} [Fintype I] [Fintype J] [Nontrivial I]
    (R : I → J → Prop) (hc : (incidenceGraph R).Connected) (i : I) :
    ∃ j,R i j ∧ 2≤Fintype.card {k // R k j} := by
  by_contra h
  push Not at h
  let P : I ⊕ J → Prop := fun v => match v with
    | .inl k => k=i
    | .inr j => R i j
  have hp : ∀ u v,(incidenceGraph R).Adj u v → P u → P v := by
    intro u v huv hu
    cases u with
    | inl k =>
      cases v with
      | inl l => exact False.elim huv
      | inr j => change k=i at hu; subst k; exact huv
    | inr j =>
      cases v with
      | inr l => exact False.elim huv
      | inl k =>
        have hcard : Fintype.card {k // R k j}≤1 := by have := h j hu; omega
        haveI : Subsingleton {k // R k j} := Fintype.card_le_one_iff_subsingleton.mp hcard
        exact congrArg Subtype.val (Subsingleton.elim (⟨k,huv⟩ : {k // R k j}) ⟨i,hu⟩)
  obtain ⟨k,hki⟩ := exists_ne i
  exact hki (reachable_closed P hp rfl (hc (.inl i) (.inl k)))

/-- At every reflected sink, one actual kernel projection is surjective. -/
theorem full_sources_generate_sink {I J : Type*} [Fintype I] [Fintype J] [Nontrivial I]
    (R : I → J → Prop) (hc : (incidenceGraph R).Connected) (i : I) :
    ∃ j,(∃ h : R i j,Function.Surjective (projection (⟨i,h⟩ : {k // R k j}))) := by
  obtain ⟨j,hij,hcard⟩ := nonleaf_neighbor R hc i
  haveI : Nontrivial {k // R k j} := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨k,hk⟩ := exists_ne (⟨i,hij⟩ : {k // R k j})
  exact ⟨j,hij,reflection_projection_surjective ⟨i,hij⟩ k (Ne.symm hk)⟩

end KroneckerReflectedSourceGeneration
end

