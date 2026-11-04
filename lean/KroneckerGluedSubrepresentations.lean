import KroneckerLinearCoverBlocks

set_option autoImplicit false
namespace KroneckerGluedSubrepresentations
open Module KroneckerLinearCoverBlocks
open KroneckerReflectedSubrepresentations
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The attachment arrows are identity maps from a connector copy of C to the
chosen one-dimensional block sink. Block restrictions include every arrow. -/
structure GluedSubrep {I J : Type} (B : J → LinearCoverBlock) (R : I → J → Prop)
    (attach : ∀ i j,R i j → (B j).Sink) where
  block : ∀ j,BlockSubrep (B j)
  connector : I → Submodule ℂ ℂ
  attachment : ∀ i j (h : R i j) x,x∈connector i → x∈(block j).sink (attach i j h)

noncomputable def chosenConnectors {I J : Type} [Fintype I]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) : Finset I :=
  Finset.univ.filter (fun i => S.connector i≠⊥)

noncomputable def occupiedBlocks {I J : Type} [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) : Finset J :=
  Finset.univ.filter (fun j => 0<sourceSize (S.block j)+sinkSize (S.block j))

theorem connector_dimension_sum {I J : Type} [Fintype I]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) : (∑ i,finrank ℂ (S.connector i))=(chosenConnectors S).card := by
  simp only [complex_submodule_dimension,chosenConnectors,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem empty_block_dimensions {I J : Type} [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) (j : J) (hj : j∉occupiedBlocks S) :
    sourceSize (S.block j)=0 ∧ sinkSize (S.block j)=0 := by
  have h : ¬0<sourceSize (S.block j)+sinkSize (S.block j) := by
    simpa [occupiedBlocks] using hj
  omega

theorem attachment_forces_occupied {I J : Type} [Fintype I] [Fintype J]
    {B : J → LinearCoverBlock} {R : I → J → Prop} {attach : ∀ i j,R i j → (B j).Sink}
    (S : GluedSubrep B R attach) {i : I} {j : J} (hi : i∈chosenConnectors S)
    (h : R i j) : j∈occupiedBlocks S := by
  have hn : S.connector i≠⊥ := by simpa [chosenConnectors] using hi
  have hc : 1≤finrank ℂ (S.connector i) := Submodule.one_le_finrank_iff.mpr hn
  have hle : S.connector i≤(S.block j).sink (attach i j h) := S.attachment i j h
  have hd := Submodule.finrank_mono hle
  have hs : finrank ℂ ((S.block j).sink (attach i j h))≤sinkSize (S.block j) :=
    Finset.single_le_sum (f:=fun t => finrank ℂ ((S.block j).sink t))
      (fun t _ => Nat.zero_le _) (Finset.mem_univ _)
  simp only [occupiedBlocks,Finset.mem_filter,Finset.mem_univ,true_and]
  omega

end KroneckerGluedSubrepresentations
