import KroneckerGluedSupportTree

set_option autoImplicit false
namespace KroneckerCoverTitsForm
open SimpleGraph Module KroneckerLinearCoverBlocks KroneckerRetainedBlockSupport
open KroneckerGluedLinearRepresentation KroneckerGluedSupportGraph KroneckerGluedSupportTree
open KroneckerIncidenceDivergence KroneckerTreeFlowUniqueness KroneckerBipartiteIncidence
open KroneckerRetainedReflectionKernels KroneckerReflectedLinearBlock
open KroneckerReflectionKernel KroneckerSaturatedTreeDimensions
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The Tits form of the nonzero-arrow support; each sink has dimension one. -/
noncomputable def titsForm (B : LinearCoverBlock) : ℤ := (Fintype.card B.Sink : ℤ)+
  ∑ s,((finrank ℂ (B.Space s) : ℤ)^2-
    (Fintype.card {t // linearSupport B s t} : ℤ)*finrank ℂ (B.Space s))

theorem glued_support_neighbor_card {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (s : I ⊕ (Σ j,(B j).Source)) :
    Fintype.card {t // linearSupport (gluedBlock B R attach) s t}=
      Fintype.card {t // GlueEdge B R attach s t} :=
  Fintype.card_congr (Equiv.subtypeEquivRight (fun t => glued_arrow_support_iff B R attach s t))

set_option backward.isDefEq.respectTransparency false in
/-- Internal edge contributions and attachment edge contributions are counted
separately in the actual glued representation's Tits form. -/
theorem glued_tits_form {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink) :
    titsForm (gluedBlock B R attach)=
      (∑ j,titsForm (B j))+(Fintype.card I : ℤ)-(Fintype.card (Edge R) : ℤ) := by
  classical
  change (Fintype.card (Σ j,(B j).Sink) : ℤ)+
    (∑ s : I ⊕ (Σ j,(B j).Source),((finrank ℂ (gluedSpace B s) : ℤ)^2-
      (Fintype.card {t // linearSupport (gluedBlock B R attach) s t} : ℤ)*
        finrank ℂ (gluedSpace B s)))=_
  rw [Fintype.sum_sum_type]
  simp only [glued_support_neighbor_card B R attach,connector_neighbor_count,Fintype.sum_sigma,
    internal_neighbor_count,gluedSpace]
  simp [titsForm,incidence_edge_count,Fintype.card_sigma,Nat.cast_sum,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring

theorem retained_tits_form {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (R : I → J → Prop) (hT : (incidenceGraph R).IsTree)
    (h3 : ∀ i,Fintype.card {j // R i j}=3) : titsForm (retainedBlock R)=1 := by
  have he : ∀ j : (retainedBlock R).Source,
      (Fintype.card {i // linearSupport (retainedBlock R) j i} : ℤ)=
        (finrank ℂ ((retainedBlock R).Space j) : ℤ)+1 := by
    intro j
    haveI : Nonempty {i // R i j.1} := Fintype.card_pos_iff.mp (by have := j.2; omega)
    have hc := Fintype.card_congr (Equiv.subtypeEquivRight (fun i => retained_support_iff R j i))
    have hc' : Fintype.card {i // linearSupport (retainedBlock R) j i}=
        Fintype.card {i : I // R i j.1} := by
      simpa only [←Nat.card_eq_fintype_card] using hc
    rw [hc']
    exact_mod_cast (reflection_kernel_dimension {i // R i j.1}).symm
  have hsum : (sourceDimension (retainedBlock R) : ℤ)+1=Fintype.card I := by
    rw [retained_total_dimension]
    exact_mod_cast reflected_source_dimension R hT h3
  have hterm : ∀ j : (retainedBlock R).Source,
      (finrank ℂ ((retainedBlock R).Space j) : ℤ)^2-
        (Fintype.card {i // linearSupport (retainedBlock R) j i} : ℤ)*
          finrank ℂ ((retainedBlock R).Space j)= -(finrank ℂ ((retainedBlock R).Space j) : ℤ) := by
    intro j
    rw [he]
    ring
  unfold titsForm
  simp only [hterm,Finset.sum_neg_distrib]
  change (Fintype.card I : ℤ)-(∑ j : (retainedBlock R).Source,(finrank ℂ ((retainedBlock R).Space j) : ℤ))=1
  have hs : (sourceDimension (retainedBlock R) : ℤ)=
      ∑ j : (retainedBlock R).Source,(finrank ℂ ((retainedBlock R).Space j) : ℤ) := by
    simp [sourceDimension]
  omega

theorem glued_tits_form_one {I J : Type} [Fintype I] [Fintype J]
    (B : J → LinearCoverBlock) (R : I → J → Prop) (attach : ∀ i j,R i j → (B j).Sink)
    (hT : (incidenceGraph R).IsTree) (h3 : ∀ i,Fintype.card {j // R i j}=3)
    (hB : ∀ j,titsForm (B j)=1) : titsForm (gluedBlock B R attach)=1 := by
  have hJ : (Fintype.card J : ℤ)=2*(Fintype.card I : ℤ)+1 := by
    exact_mod_cast saturated_tree_sink_count R hT h3
  have he : (Fintype.card (Edge R) : ℤ)=3*(Fintype.card I : ℤ) := by
    rw [incidence_edge_count]
    simp [h3,mul_comm]
  rw [glued_tits_form]
  simp only [hB,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [hJ,he]
  ring

end KroneckerCoverTitsForm
