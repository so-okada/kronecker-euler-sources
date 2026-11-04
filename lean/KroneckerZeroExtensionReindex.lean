import KroneckerBlockCoverDimensions

/- Original module: KroneckerBlockZeroExtension -/
section
/- DEVELOPMENT SOURCE: certification status is recorded separately from this source. -/
set_option autoImplicit false
namespace KroneckerBlockZeroExtension
open Module KroneckerLinearCoverBlocks KroneckerGluedSubrepEquivalence
open scoped BigOperators

/-- A zero-dimensional vector space, used at every added vertex. -/
abbrev ZeroSpace := Fin 0 → ℂ

def sourceSpace (B : LinearCoverBlock) (S : Type) : B.Source ⊕ S → Type
  | .inl s => B.Space s
  | .inr _ => ZeroSpace

def sinkSpace (B : LinearCoverBlock) (T : Type) : B.Sink ⊕ T → Type
  | .inl _ => ℂ
  | .inr _ => ZeroSpace

instance sourceSpaceGroup (B : LinearCoverBlock) (S : Type) (s : B.Source ⊕ S) :
    AddCommGroup (sourceSpace B S s) := by
  cases s with
  | inl s => exact inferInstanceAs (AddCommGroup (B.Space s))
  | inr _ => exact inferInstanceAs (AddCommGroup ZeroSpace)
instance sourceSpaceModule (B : LinearCoverBlock) (S : Type) (s : B.Source ⊕ S) :
    Module ℂ (sourceSpace B S s) := by
  cases s with
  | inl s => exact inferInstanceAs (Module ℂ (B.Space s))
  | inr _ => exact inferInstanceAs (Module ℂ ZeroSpace)
instance sourceSpaceFinite (B : LinearCoverBlock) (S : Type) (s : B.Source ⊕ S) :
    FiniteDimensional ℂ (sourceSpace B S s) := by
  cases s with
  | inl s => exact inferInstanceAs (FiniteDimensional ℂ (B.Space s))
  | inr _ => exact inferInstanceAs (FiniteDimensional ℂ ZeroSpace)
instance sinkSpaceGroup (B : LinearCoverBlock) (T : Type) (t : B.Sink ⊕ T) :
    AddCommGroup (sinkSpace B T t) := by
  cases t with
  | inl _ => exact inferInstanceAs (AddCommGroup ℂ)
  | inr _ => exact inferInstanceAs (AddCommGroup ZeroSpace)
instance sinkSpaceModule (B : LinearCoverBlock) (T : Type) (t : B.Sink ⊕ T) :
    Module ℂ (sinkSpace B T t) := by
  cases t with
  | inl _ => exact inferInstanceAs (Module ℂ ℂ)
  | inr _ => exact inferInstanceAs (Module ℂ ZeroSpace)
instance sinkSpaceFinite (B : LinearCoverBlock) (T : Type) (t : B.Sink ⊕ T) :
    FiniteDimensional ℂ (sinkSpace B T t) := by
  cases t with
  | inl _ => exact inferInstanceAs (FiniteDimensional ℂ ℂ)
  | inr _ => exact inferInstanceAs (FiniteDimensional ℂ ZeroSpace)

/-- All arrows involving an added vertex are zero. No finiteness assumption is
placed on the added source or sink sets. -/
def arrow (B : LinearCoverBlock) (S T : Type) :
    ∀ s t, sourceSpace B S s →ₗ[ℂ] sinkSpace B T t
  | .inl s, .inl t => B.arrow s t
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr _, .inr _ => 0

/-- Arbitrary vertexwise submodules, not merely coordinate subspaces. -/
structure Subrep (B : LinearCoverBlock) (S T : Type) where
  source : ∀ s, Submodule ℂ (sourceSpace B S s)
  sink : ∀ t, Submodule ℂ (sinkSpace B T t)
  invariant : ∀ s t x, x ∈ source s → arrow B S T s t x ∈ sink t

theorem subrep_ext {B : LinearCoverBlock} {S T : Type} {U V : Subrep B S T}
    (hs : U.source = V.source) (ht : U.sink = V.sink) : U = V := by
  cases U
  cases V
  cases hs
  cases ht
  rfl

theorem zeroSpace_submodule_eq_bot (P : Submodule ℂ ZeroSpace) : P = ⊥ := by
  apply le_antisymm
  · intro x _
    exact Subsingleton.elim x 0
  · exact bot_le

def restrict {B : LinearCoverBlock} {S T : Type} (U : Subrep B S T) : BlockSubrep B where
  source := fun s => U.source (.inl s)
  sink := fun t => U.sink (.inl t)
  invariant := fun s t x hx => U.invariant (.inl s) (.inl t) x hx

def extend {B : LinearCoverBlock} {S T : Type} (U : BlockSubrep B) : Subrep B S T where
  source := fun s => match s with
    | .inl s => U.source s
    | .inr _ => ⊥
  sink := fun t => match t with
    | .inl t => U.sink t
    | .inr _ => ⊥
  invariant := by
    intro s t x hx
    cases s with
    | inl s =>
      cases t with
      | inl t => exact U.invariant s t x hx
      | inr t => exact Submodule.zero_mem _
    | inr s =>
      cases t <;> exact Submodule.zero_mem _

theorem restrict_extend {B : LinearCoverBlock} {S T : Type} (U : BlockSubrep B) :
    restrict (extend (S := S) (T := T) U) = U := by
  exact block_subrep_ext rfl rfl

theorem extend_restrict {B : LinearCoverBlock} {S T : Type} (U : Subrep B S T) :
    extend (restrict U) = U := by
  apply subrep_ext
  · funext s
    cases s with
    | inl s => rfl
    | inr s => exact (zeroSpace_submodule_eq_bot (U.source (.inr s))).symm
  · funext t
    cases t with
    | inl t => rfl
    | inr t => exact (zeroSpace_submodule_eq_bot (U.sink (.inr t))).symm

def subrepEquiv (B : LinearCoverBlock) (S T : Type) : BlockSubrep B ≃ Subrep B S T where
  toFun := extend
  invFun := restrict
  left_inv := restrict_extend
  right_inv := extend_restrict

/-- Total dimensions are finite because every added-vertex submodule is zero. -/
noncomputable def sourceSize {B : LinearCoverBlock} {S T : Type} (U : Subrep B S T) : ℕ :=
  ∑ s : B.Source, finrank ℂ (U.source (.inl s))
noncomputable def sinkSize {B : LinearCoverBlock} {S T : Type} (U : Subrep B S T) : ℕ :=
  ∑ t : B.Sink, finrank ℂ (U.sink (.inl t))



def KingStable (B : LinearCoverBlock) (S T : Type) : Prop := ∀ U : Subrep B S T,
  0 < sourceSize U + sinkSize U →
  sourceSize U + sinkSize U < sourceDimension B + Fintype.card B.Sink →
  Fintype.card B.Sink * sourceSize U < sourceDimension B * sinkSize U


end KroneckerBlockZeroExtension
end

/- Original module: KroneckerBlockCoverExtension -/
section
/- DEVELOPMENT SOURCE: certification status is recorded separately from this source. -/
set_option autoImplicit false
namespace KroneckerBlockCoverExtension
open KroneckerBlockZeroExtension KroneckerLinearCoverBlocks
open KroneckerReflectedSupportClasses KroneckerRetainedBlockSupport
open KroneckerBlockCoverDimensions KroneckerReducedColorWords KroneckerWordParity
open KroneckerBipartiteTreeLift KroneckerTreeInducedEmbedding KroneckerIncidenceEdgeColoring

/-- Complete an embedding to a bijection by adjoining precisely its complement. -/
def completedLabel {A B : Type} (e : A ↪ B) : A ⊕ {b : B // b ∉ Set.range e} → B
  | .inl a => e a
  | .inr b => b.val

theorem completedLabel_bijective {A B : Type} (e : A ↪ B) :
    Function.Bijective (completedLabel e) := by
  constructor
  · intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (e.injective h)
      | inr b => exact False.elim (b.property ⟨a,h⟩)
    | inr a =>
      cases b with
      | inl b => exact False.elim (a.property ⟨b,h.symm⟩)
      | inr b => exact congrArg Sum.inr (Subtype.ext h)
  · intro b
    by_cases h : b ∈ Set.range e
    · obtain ⟨a,rfl⟩ := h
      exact ⟨.inl a,rfl⟩
    · exact ⟨.inr ⟨b,h⟩,rfl⟩

noncomputable def completedEquiv {A B : Type} (e : A ↪ B) :
    A ⊕ {b : B // b ∉ Set.range e} ≃ B :=
  Equiv.ofBijective (completedLabel e) (completedLabel_bijective e)

abbrev CoverSource := {w : Word // parity w = 0}
abbrev CoverSink := {w : Word // parity w = 1}

noncomputable def sourceEmbedding (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source) : X.block.Source ↪ CoverSource where
  toFun := fun s => ⟨blockEmbedding X hT r (.inl s),
    source_root_lift_parity X.coloring hT r (.inl s)⟩
  inj' := by
    intro s t h
    exact Sum.inl.inj ((blockEmbedding X hT r).injective (congrArg Subtype.val h))

noncomputable def sinkEmbedding (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source) : X.block.Sink ↪ CoverSink where
  toFun := fun t => ⟨blockEmbedding X hT r (.inr t),
    source_root_lift_parity X.coloring hT r (.inr t)⟩
  inj' := by
    intro s t h
    exact Sum.inr.inj ((blockEmbedding X hT r).injective (congrArg Subtype.val h))

abbrev SourceComplement (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) := {w : CoverSource // w ∉ Set.range (sourceEmbedding X hT r)}
abbrev SinkComplement (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) := {w : CoverSink // w ∉ Set.range (sinkEmbedding X hT r)}

/-- This equivalence includes every even cover vertex, including zero vertices. -/
noncomputable def sourceLabel (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) : X.block.Source ⊕ SourceComplement X hT r ≃ CoverSource :=
  completedEquiv (sourceEmbedding X hT r)

/-- This equivalence includes every odd cover vertex, including zero vertices. -/
noncomputable def sinkLabel (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source) : X.block.Sink ⊕ SinkComplement X hT r ≃ CoverSink :=
  completedEquiv (sinkEmbedding X hT r)

/-- The zero extension has nonzero arrows only along edges of the fixed cover. -/
theorem nonzero_arrow_cover_adj (X : ColoredBlock) (hT : (supportGraph X.block).IsTree)
    (r : X.block.Source)
    (s : X.block.Source ⊕ SourceComplement X hT r)
    (t : X.block.Sink ⊕ SinkComplement X hT r)
    (h : arrow X.block (SourceComplement X hT r) (SinkComplement X hT r) s t ≠ 0) :
    KroneckerColorWordCover.cover.Adj (sourceLabel X hT r s).val (sinkLabel X hT r t).val := by
  cases s with
  | inl s =>
    cases t with
    | inl t =>
      exact (treeEmbedding (incidenceColoring X.coloring) hT (.inl r)).map_rel_iff.mpr h
    | inr t => exact False.elim (h rfl)
  | inr s =>
    cases t <;> exact False.elim (h rfl)


end KroneckerBlockCoverExtension
end

/- Original module: KroneckerZeroExtensionReindex -/
section
/- DEVELOPMENT SOURCE: certification status is recorded separately from this source. -/
set_option autoImplicit false
namespace KroneckerZeroExtensionReindex
open KroneckerBlockZeroExtension KroneckerLinearCoverBlocks
open KroneckerBlockCoverExtension KroneckerReflectedSupportClasses KroneckerRetainedBlockSupport

abbrev Families (B : LinearCoverBlock) (S T : Type) :=
  (∀ s, Submodule ℂ (sourceSpace B S s)) × (∀ t, Submodule ℂ (sinkSpace B T t))

def Compatible {B : LinearCoverBlock} {S T : Type} (U : Families B S T) : Prop :=
  ∀ s t x, x ∈ U.1 s → arrow B S T s t x ∈ U.2 t

def subrepFamilies (B : LinearCoverBlock) (S T : Type) :
    Subrep B S T ≃ {U : Families B S T // Compatible U} where
  toFun := fun U => ⟨⟨U.source,U.sink⟩,U.invariant⟩
  invFun := fun U => ⟨U.val.1,U.val.2,U.property⟩
  left_inv := by intro U; rfl
  right_inv := by intro U; rfl

abbrev ReindexedFamilies (B : LinearCoverBlock) {S T A D : Type}
    (e : B.Source ⊕ S ≃ A) (f : B.Sink ⊕ T ≃ D) :=
  (∀ a, Submodule ℂ (sourceSpace B S (e.symm a))) ×
  (∀ d, Submodule ℂ (sinkSpace B T (f.symm d)))

def ReindexedCompatible {B : LinearCoverBlock} {S T A D : Type}
    (e : B.Source ⊕ S ≃ A) (f : B.Sink ⊕ T ≃ D)
    (U : ReindexedFamilies B e f) : Prop :=
  ∀ a d x, x ∈ U.1 a → arrow B S T (e.symm a) (f.symm d) x ∈ U.2 d

def reindexFamilies (B : LinearCoverBlock) {S T A D : Type}
    (e : B.Source ⊕ S ≃ A) (f : B.Sink ⊕ T ≃ D) :
    Families B S T ≃ ReindexedFamilies B e f :=
  (Equiv.piCongrLeft' (fun s => Submodule ℂ (sourceSpace B S s)) e).prodCongr
    (Equiv.piCongrLeft' (fun t => Submodule ℂ (sinkSpace B T t)) f)

theorem compatible_reindex_iff {B : LinearCoverBlock} {S T A D : Type}
    (e : B.Source ⊕ S ≃ A) (f : B.Sink ⊕ T ≃ D) (U : Families B S T) :
    Compatible U ↔ ReindexedCompatible e f (reindexFamilies B e f U) := by
  constructor
  · intro h a d x hx
    exact h (e.symm a) (f.symm d) x hx
  · intro h s t
    have hs := h (e s) (f t)
    change (∀ x, x ∈ U.1 (e.symm (e s)) →
      arrow B S T (e.symm (e s)) (f.symm (f t)) x ∈ U.2 (f.symm (f t))) at hs
    let P (s : B.Source ⊕ S) (t : B.Sink ⊕ T) : Prop :=
      ∀ x, x ∈ U.1 s → arrow B S T s t x ∈ U.2 t
    exact (congrArg₂ P (e.symm_apply_apply s) (f.symm_apply_apply t)).mp hs

def reindexedSubrepEquiv (B : LinearCoverBlock) {S T A D : Type}
    (e : B.Source ⊕ S ≃ A) (f : B.Sink ⊕ T ≃ D) :
    Subrep B S T ≃ {U : ReindexedFamilies B e f // ReindexedCompatible e f U} :=
  (subrepFamilies B S T).trans
    ((reindexFamilies B e f).subtypeEquiv (compatible_reindex_iff e f))

/-- All vertexwise subrepresentations of the actual representation on the fixed
even/odd Word cover, not only a selected family of coordinate subspaces. -/
noncomputable def fixedCoverSubrepEquiv (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source) :
    BlockSubrep X.block ≃
      {U : ReindexedFamilies X.block (sourceLabel X hT r) (sinkLabel X hT r) //
        ReindexedCompatible (sourceLabel X hT r) (sinkLabel X hT r) U} :=
  (subrepEquiv X.block (SourceComplement X hT r) (SinkComplement X hT r)).trans
    (reindexedSubrepEquiv X.block (sourceLabel X hT r) (sinkLabel X hT r))

open Module
open scoped BigOperators

noncomputable def reindexedSourceSize {B : LinearCoverBlock} {S T A D : Type}
    (e : B.Source ⊕ S ≃ A) (f : B.Sink ⊕ T ≃ D)
    (U : ReindexedFamilies B e f) : ℕ :=
  ∑ s : B.Source, finrank ℂ (U.1 (e (.inl s)))

noncomputable def reindexedSinkSize {B : LinearCoverBlock} {S T A D : Type}
    (e : B.Source ⊕ S ≃ A) (f : B.Sink ⊕ T ≃ D)
    (U : ReindexedFamilies B e f) : ℕ :=
  ∑ t : B.Sink, finrank ℂ (U.2 (f (.inl t)))






/-- Invariance only along arrows of the actual fixed cover quiver. -/
def CoverCompatible (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source)
    (U : ReindexedFamilies X.block (sourceLabel X hT r) (sinkLabel X hT r)) : Prop :=
  ∀ (a : CoverSource) (d : CoverSink), KroneckerColorWordCover.cover.Adj a.val d.val →
    ∀ x, x ∈ U.1 a →
      arrow X.block (SourceComplement X hT r) (SinkComplement X hT r)
        ((sourceLabel X hT r).symm a) ((sinkLabel X hT r).symm d) x ∈ U.2 d

theorem cover_compatible_iff (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source)
    (U : ReindexedFamilies X.block (sourceLabel X hT r) (sinkLabel X hT r)) :
    CoverCompatible X hT r U ↔
      ReindexedCompatible (sourceLabel X hT r) (sinkLabel X hT r) U := by
  constructor
  · intro h a d x hx
    by_cases hadj : KroneckerColorWordCover.cover.Adj a.val d.val
    · exact h a d hadj x hx
    · have hz : arrow X.block (SourceComplement X hT r) (SinkComplement X hT r)
          ((sourceLabel X hT r).symm a) ((sinkLabel X hT r).symm d) = 0 := by
        by_contra hn
        apply hadj
        simpa only [Equiv.apply_symm_apply] using nonzero_arrow_cover_adj X hT r
          ((sourceLabel X hT r).symm a) ((sinkLabel X hT r).symm d) hn
      rw [hz]
      exact Submodule.zero_mem _
  · intro h a d _ x hx
    exact h a d x hx

/-- Exact all-subrepresentation dictionary for the fixed cover quiver itself. -/
noncomputable def actualCoverSubrepEquiv (X : ColoredBlock)
    (hT : (supportGraph X.block).IsTree) (r : X.block.Source) :
    BlockSubrep X.block ≃
      {U : ReindexedFamilies X.block (sourceLabel X hT r) (sinkLabel X hT r) //
        CoverCompatible X hT r U} :=
  (fixedCoverSubrepEquiv X hT r).trans
    (Equiv.subtypeEquivRight (fun U => (cover_compatible_iff X hT r U).symm))

end KroneckerZeroExtensionReindex
end
