import KroneckerBipartiteKingRestriction

/- DEVELOPMENT SOURCE: certification status is recorded separately. -/
set_option autoImplicit false
namespace KroneckerBipartiteSubrepresentationRestriction
open Module KroneckerPositiveSupportRestriction
open scoped BigOperators

abbrev Families {I J : Type} (R : Representation I J) :=
  (∀ i, Submodule ℂ (R.SourceSpace i)) × (∀ j, Submodule ℂ (R.SinkSpace j))

def Compatible {I J : Type} {R : Representation I J} (U : Families R) : Prop :=
  ∀ i j x, x ∈ U.1 i → R.arrow i j x ∈ U.2 j

def subrepFamilies {I J : Type} (R : Representation I J) :
    Subrep R ≃ {U : Families R // Compatible U} where
  toFun U := ⟨⟨U.source,U.sink⟩,U.invariant⟩
  invFun U := ⟨U.val.1,U.val.2,U.property⟩
  left_inv U := rfl
  right_inv U := rfl

/-- Pullback on all source and sink submodule families, including arbitrary
infinite index sets and arbitrary vertex label bijections. -/
noncomputable def isoFamilies {I J I' J' : Type} {R : Representation I J}
    {S : Representation I' J'} (e : Iso S R) : Families R ≃ Families S :=
  ((Equiv.piCongrLeft' (fun i => Submodule ℂ (R.SourceSpace i)) e.sourceIndex.symm).trans
    (Equiv.piCongrRight (fun i => (Submodule.orderIsoMapComap (e.source i)).symm.toEquiv))).prodCongr
  ((Equiv.piCongrLeft' (fun j => Submodule ℂ (R.SinkSpace j)) e.sinkIndex.symm).trans
    (Equiv.piCongrRight (fun j => (Submodule.orderIsoMapComap (e.sink j)).symm.toEquiv)))

theorem iso_compatible_iff {I J I' J' : Type} {R : Representation I J}
    {S : Representation I' J'} (e : Iso S R) (U : Families R) :
    Compatible U ↔ Compatible (isoFamilies e U) := by
  constructor
  · intro h i j x hx
    change e.sink j (S.arrow i j x) ∈ U.2 (e.sinkIndex j)
    rw [e.commutes]
    exact h (e.sourceIndex i) (e.sinkIndex j) (e.source i x) hx
  · intro h i j x hx
    obtain ⟨i,rfl⟩ := e.sourceIndex.surjective i
    obtain ⟨j,rfl⟩ := e.sinkIndex.surjective j
    have hy : e.source i ((e.source i).symm x) ∈ U.1 (e.sourceIndex i) := by
      simpa only [LinearEquiv.apply_symm_apply] using hx
    have hh := h i j ((e.source i).symm x) hy
    change e.sink j (S.arrow i j ((e.source i).symm x)) ∈ U.2 (e.sinkIndex j) at hh
    rw [e.commutes,LinearEquiv.apply_symm_apply] at hh
    exact hh

/-- A genuine representation isomorphism identifies ALL subrepresentations. -/
noncomputable def isoSubrepEquiv {I J I' J' : Type} {R : Representation I J}
    {S : Representation I' J'} (e : Iso S R) : Subrep R ≃ Subrep S :=
  (subrepFamilies R).trans
    (((isoFamilies e).subtypeEquiv (iso_compatible_iff e)).trans (subrepFamilies S).symm)

theorem finrank_comap_equiv {V W : Type} [AddCommGroup V] [AddCommGroup W]
    [Module ℂ V] [Module ℂ W] (e : V ≃ₗ[ℂ] W) (P : Submodule ℂ W) :
    finrank ℂ (P.comap e.toLinearMap) = finrank ℂ P := by
  have h := e.finrank_map_eq (P.comap e.toLinearMap)
  rw [Submodule.map_comap_eq_of_surjective (f := e.toLinearMap) e.surjective] at h
  exact h.symm

theorem iso_source_subspace_dimension {I J I' J' : Type} {R : Representation I J}
    {S : Representation I' J'} (e : Iso S R) (U : Subrep R) (i : I') :
    finrank ℂ ((isoSubrepEquiv e U).source i) = finrank ℂ (U.source (e.sourceIndex i)) :=
  finrank_comap_equiv (e.source i) (U.source (e.sourceIndex i))

theorem iso_sink_subspace_dimension {I J I' J' : Type} {R : Representation I J}
    {S : Representation I' J'} (e : Iso S R) (U : Subrep R) (j : J') :
    finrank ℂ ((isoSubrepEquiv e U).sink j) = finrank ℂ (U.sink (e.sinkIndex j)) :=
  finrank_comap_equiv (e.sink j) (U.sink (e.sinkIndex j))

theorem iso_source_size {I J I' J' : Type} [Fintype I] [Fintype I']
    {R : Representation I J} {S : Representation I' J'} (e : Iso S R) (U : Subrep R) :
    sourceSize (isoSubrepEquiv e U) = sourceSize U := by
  simp only [sourceSize,iso_source_subspace_dimension]
  exact Equiv.sum_comp e.sourceIndex (fun i => finrank ℂ (U.source i))

theorem iso_sink_size {I J I' J' : Type} [Fintype J] [Fintype J']
    {R : Representation I J} {S : Representation I' J'} (e : Iso S R) (U : Subrep R) :
    sinkSize (isoSubrepEquiv e U) = sinkSize U := by
  simp only [sinkSize,iso_sink_subspace_dimension]
  exact Equiv.sum_comp e.sinkIndex (fun j => finrank ℂ (U.sink j))

theorem iso_source_dimension {I J I' J' : Type} [Fintype I] [Fintype I']
    {R : Representation I J} {S : Representation I' J'} (e : Iso S R) :
    sourceDimension S = sourceDimension R := by
  calc
    sourceDimension S = ∑ i, finrank ℂ (R.SourceSpace (e.sourceIndex i)) :=
      Finset.sum_congr rfl (fun i _ => (e.source i).finrank_eq)
    _ = sourceDimension R := Equiv.sum_comp e.sourceIndex (fun i => finrank ℂ (R.SourceSpace i))

theorem iso_sink_dimension {I J I' J' : Type} [Fintype J] [Fintype J']
    {R : Representation I J} {S : Representation I' J'} (e : Iso S R) :
    sinkDimension S = sinkDimension R := by
  calc
    sinkDimension S = ∑ j, finrank ℂ (R.SinkSpace (e.sinkIndex j)) :=
      Finset.sum_congr rfl (fun j _ => (e.sink j).finrank_eq)
    _ = sinkDimension R := Equiv.sum_comp e.sinkIndex (fun j => finrank ℂ (R.SinkSpace j))

theorem iso_king_stability_iff {I J I' J' : Type} [Fintype I] [Fintype J]
    [Fintype I'] [Fintype J'] {R : Representation I J} {S : Representation I' J'}
    (e : Iso S R) : KingStable S ↔ KingStable R := by
  constructor
  · intro h U
    simpa only [iso_source_size,iso_sink_size,iso_source_dimension e,iso_sink_dimension e]
      using h (isoSubrepEquiv e U)
  · intro h U
    obtain ⟨W,rfl⟩ := (isoSubrepEquiv e).surjective U
    simpa only [iso_source_size,iso_sink_size,iso_source_dimension e,iso_sink_dimension e]
      using h W

end KroneckerBipartiteSubrepresentationRestriction
