import KroneckerReflectedSupportClasses

set_option autoImplicit false
namespace KroneckerDimensionedSupportClasses
open Module KroneckerReflectedSupportClasses KroneckerColoredIncidenceIso
open KroneckerRetainedBlockSupport KroneckerRetainedReflectionKernels
open KroneckerProperColoredReflection KroneckerBipartiteIncidence
attribute [local instance] Classical.propDecidable

/-- The target of forgetting markings retains the source-space dimensions.
Every sink space in `LinearCoverBlock` is the fixed one-dimensional space. -/
def dimensionedSetoid : Setoid ColoredBlock where
  r X Y := ∃ e : ColoredIso X.coloring Y.coloring,
    ∀ s,finrank ℂ (Y.block.Space (e.source s))=finrank ℂ (X.block.Space s)
  iseqv := by
    constructor
    · intro X; exact ⟨identityIso X.coloring,fun _ => rfl⟩
    · rintro X Y ⟨e,he⟩
      exact ⟨e.symm,fun s => (he (e.source.symm s)).symm.trans
        (congrArg (fun t => finrank ℂ (Y.block.Space t)) (e.source.apply_symm_apply s))⟩
    · rintro X Y Z ⟨e,he⟩ ⟨f,hf⟩
      exact ⟨e.trans f,fun s => (hf (e.source s)).trans (he s)⟩

noncomputable def forgetDimensions : Quotient dimensionedSetoid → Quotient supportSetoid :=
  Quotient.map id (by rintro X Y ⟨e,_⟩; exact ⟨e⟩)

theorem retained_iso_preserves_dimensions {I J I' J' : Type}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    {R : I → J → Prop} {R' : I' → J' → Prop}
    (C : ProperColoring R) (D : ProperColoring R')
    (e : ColoredIso (retainedColoring C) (retainedColoring D)) (s : Retained R) :
    finrank ℂ ((retainedBlock R').Space (e.source s))=
      finrank ℂ ((retainedBlock R).Space s) := by
  have hs := retained_dimension_degree_pairs C s
  have ht := retained_dimension_degree_pairs D (e.source s)
  rw [supportGraph,left_degree] at hs ht
  have hd := e.source_degree s
  omega


end KroneckerDimensionedSupportClasses
