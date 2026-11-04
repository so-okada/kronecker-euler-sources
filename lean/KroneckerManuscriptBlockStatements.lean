import KroneckerSaturatedBlockData
import KroneckerStablePositiveSupportConnected
import KroneckerCanonicalStableOrbit
import KroneckerManuscriptFixedCoverCount

set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace KroneckerManuscriptBlockStatements
open Module KroneckerLinearCoverBlocks KroneckerGluedSubrepEquivalence
open KroneckerSaturatedBlockData KroneckerRetainedBlockSupport KroneckerCoverTitsForm
open KroneckerRetainedReflectionKernels KroneckerSparseBlockQuiver
open KroneckerOrdinarySingularEuler KroneckerStableChainCoverData
open KroneckerFiniteStableChainFamily

theorem stable_of_defect (B : LinearCoverBlock) (hB : PositiveDefect B)
    (hd : Fintype.card B.Sink = sourceDimension B + 1) : BlockKingStable B := by
  intro S hn hp
  have huv := hB S hn
  have hv : sinkSize S ≤ Fintype.card B.Sink := by
    unfold sinkSize
    calc
      (∑ t,finrank ℂ (S.sink t)) ≤ ∑ _t : B.Sink, 1 :=
        Finset.sum_le_sum (fun t _ => by simpa using (S.sink t).finrank_le)
      _ = _ := by simp
  rw [hd] at hv hp ⊢
  by_cases he : sinkSize S = sourceDimension B + 1
  · have hu : sourceSize S < sourceDimension B := by omega
    nlinarith
  · have hv' : sinkSize S ≤ sourceDimension B := by omega
    nlinarith

theorem reflected_block_statement (T : SaturatedBlockData) :
    sourceDimension (supportedBlock T) = T.sources - 1 ∧
    Fintype.card (supportedBlock T).Sink = T.sources ∧
    titsForm (supportedBlock T) = 1 ∧ BlockKingStable (supportedBlock T) ∧
    (∀ j : (supportedBlock T).Source,
      (finrank ℂ ((supportedBlock T).Space j) = 1 ∧
        (supportGraph (supportedBlock T)).degree (.inl j) = 2) ∨
      (finrank ℂ ((supportedBlock T).Space j) = 2 ∧
        (supportGraph (supportedBlock T)).degree (.inl j) = 3)) ∧
    (∀ i : (supportedBlock T).Sink,
      ∃ j : (supportedBlock T).Source, Function.Surjective ((supportedBlock T).arrow j i)) := by
  have hd := supported_block_dimensions T
  refine ⟨hd.1,hd.2,supported_block_tits T,?_,?_,?_⟩
  · apply stable_of_defect _ (supported_block_defect T)
    rw [hd.1,hd.2]
    have := T.sources_ge_two
    omega
  · exact retained_dimension_degree_pairs T.coloring
  · intro i
    let : Nontrivial (Fin T.sources) := Fintype.one_lt_card_iff_nontrivial.mp
      (by simp only [Fintype.card_fin]; have := T.sources_ge_two; omega)
    obtain ⟨j,hj,hcard⟩ := KroneckerReflectedSourceGeneration.nonleaf_neighbor
      T.incidence T.tree.connected i
    exact ⟨⟨j,hcard⟩,retained_projection_surjective T.incidence ⟨j,hcard⟩ i hj⟩

def supportModuli (B : LinearCoverBlock) : TopCat.{0} :=
  KroneckerCanonicalStableOrbit.space (source B) (target B)
    (fun v => finrank ℂ (vertexSpace B v)) (kingWeight B)

theorem supportModuli_nonempty (B : LinearCoverBlock) (hB : BlockKingStable B) :
    Nonempty (supportModuli B) := by
  apply (KroneckerCanonicalStableOrbit.space_nonempty_iff _ _ _ _).mpr
  exact ⟨coordinateRepresentation B,(coordinateRepresentation_stable_iff B).mpr hB⟩

theorem supportModuli_subsingleton (B : LinearCoverBlock) (hq : titsForm B = 1) :
    Subsingleton (supportModuli B) :=
  KroneckerStableOrbitEuler.stableOrbit_subsingleton _ _ _ _
    (positive_tits_dimension_inequality B (by rw [hq]; norm_num))

theorem supportModuli_euler_one (B : LinearCoverBlock) (hB : BlockKingStable B)
    (hq : titsForm B = 1) : ∃ h : Admissible (supportModuli B),
      ordinaryEuler (supportModuli B) h = 1 := by
  let := supportModuli_nonempty B hB
  let := supportModuli_subsingleton B hq
  exact ⟨singleton_admissible _,ordinaryEuler_singleton _⟩

theorem constructed_support_one_point {n a : ℕ} (X : StableInput n a) :
    Nonempty (supportModuli (chainBlock X.val).block) ∧
    Subsingleton (supportModuli (chainBlock X.val).block) ∧
    ∃ h : Admissible (supportModuli (chainBlock X.val).block),
      ordinaryEuler (supportModuli (chainBlock X.val).block) h = 1 := by
  have h := stable_input_realization X.val X.property
  exact ⟨supportModuli_nonempty _ h.1,supportModuli_subsingleton _ h.2.2.1,
    supportModuli_euler_one _ h.1 h.2.2.1⟩

end KroneckerManuscriptBlockStatements

#print axioms KroneckerManuscriptBlockStatements.reflected_block_statement
#print axioms KroneckerManuscriptBlockStatements.constructed_support_one_point
