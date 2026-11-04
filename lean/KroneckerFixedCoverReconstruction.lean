import KroneckerZeroExtensionReindex

/- Original module: KroneckerCoverExtensionDimensions -/
section
/- DEVELOPMENT SOURCE: certification status is recorded separately from this source. -/
set_option autoImplicit false
namespace KroneckerCoverExtensionDimensions
open Module KroneckerBlockZeroExtension KroneckerBlockCoverExtension
open KroneckerReflectedSupportClasses KroneckerRetainedBlockSupport
open KroneckerBlockCoverDimensions KroneckerFiniteWeightedImages KroneckerBipartiteTreeLift
open KroneckerReducedColorWords KroneckerWordParity KroneckerColoredTreeLift
open KroneckerColorWordCover KroneckerIncidenceEdgeColoring

variable (X : ColoredBlock) (hT : (supportGraph X.block).IsTree) (r : X.block.Source)

theorem source_complement_outside (w : SourceComplement X hT r) :
    w.val.val ∉ Set.range (blockEmbedding X hT r) := by
  rintro ⟨v,hv⟩
  cases v with
  | inl s => exact w.property ⟨s,Subtype.ext hv⟩
  | inr t =>
    have hp : parity (blockEmbedding X hT r (.inr t)) = 1 :=
      source_root_lift_parity X.coloring hT r (.inr t)
    rw [hv] at hp
    have hw := w.val.property
    omega

theorem sink_complement_outside (w : SinkComplement X hT r) :
    w.val.val ∉ Set.range (blockEmbedding X hT r) := by
  rintro ⟨v,hv⟩
  cases v with
  | inl s =>
    have hp : parity (blockEmbedding X hT r (.inl s)) = 0 :=
      source_root_lift_parity X.coloring hT r (.inl s)
    rw [hv] at hp
    have hw := w.val.property
    omega
  | inr t => exact w.property ⟨t,Subtype.ext hv⟩

theorem source_dimension_at_label (s : X.block.Source ⊕ SourceComplement X hT r) :
    finrank ℂ (sourceSpace X.block (SourceComplement X hT r) s) =
      coverDimensions X hT r (sourceLabel X hT r s).val := by
  cases s with
  | inl s =>
    exact (coverDimensions_at X hT r (.inl s)).symm
  | inr s =>
    change finrank ℂ ZeroSpace = weightedImage (blockEmbedding X hT r)
      (vertexWeight X.block) s.val.val
    rw [weightedImage_outside _ _ (source_complement_outside X hT r s)]
    simp [ZeroSpace]

theorem sink_dimension_at_label (t : X.block.Sink ⊕ SinkComplement X hT r) :
    finrank ℂ (sinkSpace X.block (SinkComplement X hT r) t) =
      coverDimensions X hT r (sinkLabel X hT r t).val := by
  cases t with
  | inl t =>
    change finrank ℂ ℂ = coverDimensions X hT r (blockEmbedding X hT r (.inr t))
    rw [Module.finrank_self]
    exact (coverDimensions_at X hT r (.inr t)).symm
  | inr t =>
    change finrank ℂ ZeroSpace = weightedImage (blockEmbedding X hT r)
      (vertexWeight X.block) t.val.val
    rw [weightedImage_outside _ _ (sink_complement_outside X hT r t)]
    simp [ZeroSpace]

/-- Pointwise agreement with the already-certified finitely supported dimension vector. -/
theorem fixed_source_dimension (w : CoverSource) :
    finrank ℂ (sourceSpace X.block (SourceComplement X hT r)
      ((sourceLabel X hT r).symm w)) = coverDimensions X hT r w.val := by
  simpa only [Equiv.apply_symm_apply] using
    source_dimension_at_label X hT r ((sourceLabel X hT r).symm w)

theorem fixed_sink_dimension (w : CoverSink) :
    finrank ℂ (sinkSpace X.block (SinkComplement X hT r)
      ((sinkLabel X hT r).symm w)) = coverDimensions X hT r w.val := by
  simpa only [Equiv.apply_symm_apply] using
    sink_dimension_at_label X hT r ((sinkLabel X hT r).symm w)

/-- Every retained nonzero arrow has exactly its original color in the fixed cover. -/
theorem fixed_arrow_color (s : X.block.Source) (t : X.block.Sink)
    (h : X.block.arrow s t ≠ 0) :
    coverColoring.color (nonzero_arrow_cover_adj X hT r (.inl s) (.inl t) h) =
      X.coloring.color s t h := by
  exact rootLift_color (incidenceColoring X.coloring) hT (.inl r) (u := .inl s) (v := .inr t) h

end KroneckerCoverExtensionDimensions
end

/- Original module: KroneckerPositiveSupportRestriction -/
section
/- DEVELOPMENT SOURCE: certification status is recorded separately from this source. -/
set_option autoImplicit false
namespace KroneckerPositiveSupportRestriction
open Module KroneckerBlockZeroExtension KroneckerBlockCoverExtension

/-- An arbitrary bipartite representation. The vertex sets may be infinite;
every individual vector space is finite-dimensional. -/
structure Representation (I J : Type) where
  SourceSpace : I → Type
  SinkSpace : J → Type
  [sourceGroup : ∀ i, AddCommGroup (SourceSpace i)]
  [sinkGroup : ∀ j, AddCommGroup (SinkSpace j)]
  [sourceModule : ∀ i, Module ℂ (SourceSpace i)]
  [sinkModule : ∀ j, Module ℂ (SinkSpace j)]
  [sourceFinite : ∀ i, FiniteDimensional ℂ (SourceSpace i)]
  [sinkFinite : ∀ j, FiniteDimensional ℂ (SinkSpace j)]
  arrow : ∀ i j, SourceSpace i →ₗ[ℂ] SinkSpace j

attribute [instance] Representation.sourceGroup Representation.sinkGroup
attribute [instance] Representation.sourceModule Representation.sinkModule
attribute [instance] Representation.sourceFinite Representation.sinkFinite

variable {I J : Type} (R : Representation I J)

abbrev PositiveSource := {i : I // 0 < finrank ℂ (R.SourceSpace i)}
abbrev PositiveSink := {j : J // 0 < finrank ℂ (R.SinkSpace j)}

def sourceInclusion : PositiveSource R ↪ I := ⟨Subtype.val,Subtype.val_injective⟩
def sinkInclusion : PositiveSink R ↪ J := ⟨Subtype.val,Subtype.val_injective⟩
abbrev ZeroSource := {i : I // i ∉ Set.range (sourceInclusion R)}
abbrev ZeroSink := {j : J // j ∉ Set.range (sinkInclusion R)}

noncomputable def sourceLabel : PositiveSource R ⊕ ZeroSource R ≃ I :=
  completedEquiv (sourceInclusion R)
noncomputable def sinkLabel : PositiveSink R ⊕ ZeroSink R ≃ J :=
  completedEquiv (sinkInclusion R)

theorem zero_source_finrank (i : ZeroSource R) : finrank ℂ (R.SourceSpace i.val) = 0 := by
  by_contra hn
  exact i.property ⟨⟨i.val,Nat.pos_of_ne_zero hn⟩,rfl⟩

theorem zero_sink_finrank (j : ZeroSink R) : finrank ℂ (R.SinkSpace j.val) = 0 := by
  by_contra hn
  exact j.property ⟨⟨j.val,Nat.pos_of_ne_zero hn⟩,rfl⟩

/-- Boundary arrows out of a zero-dimensional source vanish. -/
theorem arrow_zero_of_source (i : I) (j : J) (h : finrank ℂ (R.SourceSpace i) = 0) :
    R.arrow i j = 0 := by
  let : Subsingleton (R.SourceSpace i) := Module.finrank_zero_iff.mp h
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  rw [hx,map_zero,LinearMap.zero_apply]

/-- Boundary arrows into a zero-dimensional sink vanish. -/
theorem arrow_zero_of_sink (i : I) (j : J) (h : finrank ℂ (R.SinkSpace j) = 0) :
    R.arrow i j = 0 := by
  let : Subsingleton (R.SinkSpace j) := Module.finrank_zero_iff.mp h
  ext x
  exact Subsingleton.elim _ _

/-- The actual restriction uses only positive-dimensional vertices and keeps
all arrows between them, including arrows whose linear maps happen to be zero. -/
def restriction : Representation (PositiveSource R) (PositiveSink R) where
  SourceSpace i := R.SourceSpace i.val
  SinkSpace j := R.SinkSpace j.val
  arrow i j := R.arrow i.val j.val

def extensionSource : PositiveSource R ⊕ ZeroSource R → Type
  | .inl i => R.SourceSpace i.val
  | .inr _ => ZeroSpace

def extensionSink : PositiveSink R ⊕ ZeroSink R → Type
  | .inl j => R.SinkSpace j.val
  | .inr _ => ZeroSpace

instance extensionSourceGroup (i : PositiveSource R ⊕ ZeroSource R) :
    AddCommGroup (extensionSource R i) := by
  cases i with
  | inl i => exact inferInstanceAs (AddCommGroup (R.SourceSpace i.val))
  | inr _ => exact inferInstanceAs (AddCommGroup ZeroSpace)
instance extensionSourceModule (i : PositiveSource R ⊕ ZeroSource R) :
    Module ℂ (extensionSource R i) := by
  cases i with
  | inl i => exact inferInstanceAs (Module ℂ (R.SourceSpace i.val))
  | inr _ => exact inferInstanceAs (Module ℂ ZeroSpace)
instance extensionSourceFinite (i : PositiveSource R ⊕ ZeroSource R) :
    FiniteDimensional ℂ (extensionSource R i) := by
  cases i with
  | inl i => exact inferInstanceAs (FiniteDimensional ℂ (R.SourceSpace i.val))
  | inr _ => exact inferInstanceAs (FiniteDimensional ℂ ZeroSpace)
instance extensionSinkGroup (j : PositiveSink R ⊕ ZeroSink R) :
    AddCommGroup (extensionSink R j) := by
  cases j with
  | inl j => exact inferInstanceAs (AddCommGroup (R.SinkSpace j.val))
  | inr _ => exact inferInstanceAs (AddCommGroup ZeroSpace)
instance extensionSinkModule (j : PositiveSink R ⊕ ZeroSink R) :
    Module ℂ (extensionSink R j) := by
  cases j with
  | inl j => exact inferInstanceAs (Module ℂ (R.SinkSpace j.val))
  | inr _ => exact inferInstanceAs (Module ℂ ZeroSpace)
instance extensionSinkFinite (j : PositiveSink R ⊕ ZeroSink R) :
    FiniteDimensional ℂ (extensionSink R j) := by
  cases j with
  | inl j => exact inferInstanceAs (FiniteDimensional ℂ (R.SinkSpace j.val))
  | inr _ => exact inferInstanceAs (FiniteDimensional ℂ ZeroSpace)

/-- Extension by zero defined directly from the restricted arrow maps. -/
def extensionArrow : ∀ i j, extensionSource R i →ₗ[ℂ] extensionSink R j
  | .inl i, .inl j => (restriction R).arrow i j
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr _, .inr _ => 0

def extension : Representation (PositiveSource R ⊕ ZeroSource R)
    (PositiveSink R ⊕ ZeroSink R) where
  SourceSpace := extensionSource R
  SinkSpace := extensionSink R
  arrow := extensionArrow R

noncomputable def zeroEquiv (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (h : finrank ℂ V = 0) : ZeroSpace ≃ₗ[ℂ] V := by
  letI : Subsingleton V := Module.finrank_zero_iff.mp h
  exact LinearEquiv.ofSubsingleton ZeroSpace V

noncomputable def sourceIso : ∀ i, extensionSource R i ≃ₗ[ℂ] R.SourceSpace (sourceLabel R i)
  | .inl i => LinearEquiv.refl ℂ (R.SourceSpace i.val)
  | .inr i => zeroEquiv (R.SourceSpace i.val) (zero_source_finrank R i)

noncomputable def sinkIso : ∀ j, extensionSink R j ≃ₗ[ℂ] R.SinkSpace (sinkLabel R j)
  | .inl j => LinearEquiv.refl ℂ (R.SinkSpace j.val)
  | .inr j => zeroEquiv (R.SinkSpace j.val) (zero_sink_finrank R j)

set_option backward.isDefEq.respectTransparency false in
/-- Explicit vertexwise linear equivalences commute with every arrow. -/
theorem extension_iso_commutes (i : PositiveSource R ⊕ ZeroSource R)
    (j : PositiveSink R ⊕ ZeroSink R) (x : extensionSource R i) :
    sinkIso R j (extensionArrow R i j x) =
      R.arrow (sourceLabel R i) (sinkLabel R j) (sourceIso R i x) := by
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      have hz := arrow_zero_of_sink R i.val j.val (zero_sink_finrank R j)
      change sinkIso R (.inr j) 0 = R.arrow i.val j.val _
      rw [hz,LinearMap.zero_apply,map_zero]
  | inr i =>
    cases j with
    | inl j =>
      have hz := arrow_zero_of_source R i.val j.val (zero_source_finrank R i)
      change sinkIso R (.inl j) 0 = R.arrow i.val j.val _
      rw [hz,LinearMap.zero_apply,map_zero]
    | inr j =>
      have hz := arrow_zero_of_source R i.val j.val (zero_source_finrank R i)
      change sinkIso R (.inr j) 0 = R.arrow i.val j.val _
      rw [hz,LinearMap.zero_apply,map_zero]

/-- This packages a representation isomorphism allowing a bijection of labels. -/
structure Iso {I' J' : Type} (S : Representation I' J') (R : Representation I J) where
  sourceIndex : I' ≃ I
  sinkIndex : J' ≃ J
  source : ∀ i, S.SourceSpace i ≃ₗ[ℂ] R.SourceSpace (sourceIndex i)
  sink : ∀ j, S.SinkSpace j ≃ₗ[ℂ] R.SinkSpace (sinkIndex j)
  commutes : ∀ i j x, sink j (S.arrow i j x) = R.arrow (sourceIndex i) (sinkIndex j) (source i x)

noncomputable def restriction_extension_iso : Iso (extension R) R where
  sourceIndex := sourceLabel R
  sinkIndex := sinkLabel R
  source := sourceIso R
  sink := sinkIso R
  commutes := extension_iso_commutes R

/-- A finitely supported dimension vector makes the positive support finite. -/
theorem positive_sources_finite (d : I →₀ ℕ)
    (hd : ∀ i, finrank ℂ (R.SourceSpace i) = d i) : Finite (PositiveSource R) := by
  classical
  apply Finite.of_injective (fun i : PositiveSource R =>
    (⟨i.val, Finsupp.mem_support_iff.mpr (by rw [←hd]; exact Nat.ne_of_gt i.property)⟩ :
      {i // i ∈ d.support}))
  intro i j h
  exact Subtype.ext (congrArg (fun z : {i // i ∈ d.support} => z.val) h)

theorem positive_sinks_finite (d : J →₀ ℕ)
    (hd : ∀ j, finrank ℂ (R.SinkSpace j) = d j) : Finite (PositiveSink R) := by
  classical
  apply Finite.of_injective (fun j : PositiveSink R =>
    (⟨j.val, Finsupp.mem_support_iff.mpr (by rw [←hd]; exact Nat.ne_of_gt j.property)⟩ :
      {j // j ∈ d.support}))
  intro i j h
  exact Subtype.ext (congrArg (fun z : {i // i ∈ d.support} => z.val) h)

end KroneckerPositiveSupportRestriction
end

/- Original module: KroneckerFixedCoverReconstruction -/
section
/- DEVELOPMENT SOURCE: certification status is recorded separately from this source. -/
set_option autoImplicit false
namespace KroneckerFixedCoverReconstruction
open Module KroneckerPositiveSupportRestriction KroneckerBlockZeroExtension
open KroneckerBlockCoverExtension KroneckerReflectedSupportClasses KroneckerRetainedBlockSupport
open KroneckerBlockCoverDimensions KroneckerCoverExtensionDimensions KroneckerReducedColorWords
open KroneckerColorWordCover

/-- A representation of the fixed bipartite cover: nonedge maps are zero. -/
structure CoverRepresentation extends Representation CoverSource CoverSink where
  nonedge_zero : ∀ s t, ¬ cover.Adj s.val t.val → toRepresentation.arrow s t = 0

/-- Explicit adapter for the previously constructed block extension. -/
noncomputable def blockCoverRepresentation (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source) : CoverRepresentation where
  SourceSpace s := sourceSpace X.block (SourceComplement X hT r)
    ((KroneckerBlockCoverExtension.sourceLabel X hT r).symm s)
  SinkSpace t := sinkSpace X.block (SinkComplement X hT r)
    ((KroneckerBlockCoverExtension.sinkLabel X hT r).symm t)
  arrow s t := KroneckerBlockZeroExtension.arrow X.block (SourceComplement X hT r)
    (SinkComplement X hT r)
    ((KroneckerBlockCoverExtension.sourceLabel X hT r).symm s)
    ((KroneckerBlockCoverExtension.sinkLabel X hT r).symm t)
  nonedge_zero := by
    intro s t hn
    by_contra ha
    apply hn
    simpa only [Equiv.apply_symm_apply] using nonzero_arrow_cover_adj X hT r
      ((KroneckerBlockCoverExtension.sourceLabel X hT r).symm s)
      ((KroneckerBlockCoverExtension.sinkLabel X hT r).symm t) ha

theorem block_cover_source_dimension (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source) (s : CoverSource) :
    finrank ℂ ((blockCoverRepresentation X hT r).SourceSpace s) = coverDimensions X hT r s.val :=
  fixed_source_dimension X hT r s

theorem block_cover_sink_dimension (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source) (t : CoverSink) :
    finrank ℂ ((blockCoverRepresentation X hT r).SinkSpace t) = coverDimensions X hT r t.val :=
  fixed_sink_dimension X hT r t

/-- Arbitrary cover representations with this finite dimension vector have
finite positive source support; no stability assumption is required. -/
theorem cover_positive_sources_finite (R : CoverRepresentation) (d : Word →₀ ℕ)
    (hd : ∀ s, finrank ℂ (R.SourceSpace s) = d s.val) :
    Finite (PositiveSource R.toRepresentation) := by
  classical
  apply Finite.of_injective (fun s : PositiveSource R.toRepresentation =>
    (⟨s.val.val, Finsupp.mem_support_iff.mpr
      (by rw [←hd s.val]; exact Nat.ne_of_gt s.property)⟩ : {w // w ∈ d.support}))
  intro s t h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : {w // w ∈ d.support} => z.val) h))

theorem cover_positive_sinks_finite (R : CoverRepresentation) (d : Word →₀ ℕ)
    (hd : ∀ t, finrank ℂ (R.SinkSpace t) = d t.val) :
    Finite (PositiveSink R.toRepresentation) := by
  classical
  apply Finite.of_injective (fun t : PositiveSink R.toRepresentation =>
    (⟨t.val.val, Finsupp.mem_support_iff.mpr
      (by rw [←hd t.val]; exact Nat.ne_of_gt t.property)⟩ : {w // w ∈ d.support}))
  intro s t h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : {w // w ∈ d.support} => z.val) h))

/-- Every representation on the infinite cover with a finitely supported
finite-dimensional dimension vector is isomorphic to the extension by zero
of its restriction to finite positive-dimensional support. -/
theorem fixed_cover_finite_support_reconstruction (R : CoverRepresentation) (d : Word →₀ ℕ)
    (hs : ∀ s, finrank ℂ (R.SourceSpace s) = d s.val)
    (ht : ∀ t, finrank ℂ (R.SinkSpace t) = d t.val) :
    Finite (PositiveSource R.toRepresentation) ∧
    Finite (PositiveSink R.toRepresentation) ∧
    Nonempty (Iso (extension R.toRepresentation) R.toRepresentation) :=
  ⟨cover_positive_sources_finite R d hs, cover_positive_sinks_finite R d ht,
    ⟨restriction_extension_iso R.toRepresentation⟩⟩

/-- Specialization to the exact dimension vector certified for a colored block;
the representation R is arbitrary and may have different arrow maps. -/
theorem block_dimension_reconstruction (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source) (R : CoverRepresentation)
    (hs : ∀ s, finrank ℂ (R.SourceSpace s) = coverDimensions X hT r s.val)
    (ht : ∀ t, finrank ℂ (R.SinkSpace t) = coverDimensions X hT r t.val) :
    Finite (PositiveSource R.toRepresentation) ∧
    Finite (PositiveSink R.toRepresentation) ∧
    Nonempty (Iso (extension R.toRepresentation) R.toRepresentation) :=
  fixed_cover_finite_support_reconstruction R (coverDimensions X hT r) hs ht

end KroneckerFixedCoverReconstruction
end
