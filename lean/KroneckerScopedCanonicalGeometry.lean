import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Topology.LocalAtTarget
import KroneckerScopedModuli

/- Original module: KroneckerFiniteChainHomology -/
section
/-! Finite rational chain models imply the precise admissibility predicate used
by ordinaryEuler. Producing a cellular model and its singular comparison is a
separate geometric/source obligation; neither is postulated for quiver moduli. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFiniteChainHomology
open CategoryTheory CategoryTheory.Limits
open KroneckerOrdinarySingularEuler
open scoped BigOperators

theorem short_homology_finite (S : ShortComplex (ModuleCat ℚ))
    [FiniteDimensional ℚ S.X₂] : FiniteDimensional ℚ S.homology := by
  let : FiniteDimensional ℚ S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional ℚ (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  let e := S.moduleCatHomologyIso.toLinearEquiv
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

theorem chain_homology_finite (C : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    [FiniteDimensional ℚ (C.X n)] : FiniteDimensional ℚ (C.homology n) := by
  let : FiniteDimensional ℚ (C.sc n).X₂ := by
    change FiniteDimensional ℚ (C.X n)
    infer_instance
  exact short_homology_finite (C.sc n)

theorem chain_homology_zero (C : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (h : Subsingleton (C.X n)) : Subsingleton (C.homology n) := by
  apply ModuleCat.isZero_iff_subsingleton.mp
  exact (C.sc n).isZero_homology_of_isZero_X₂ (ModuleCat.isZero_iff_subsingleton.mpr h)

/-- A bounded finite-dimensional rational chain complex with an actual
degreewise singular-homology comparison. No Euler value is supplied as data. -/
structure Model (X : TopCat.{0}) where
  chain : ChainComplex (ModuleCat ℚ) ℕ
  finite : ∀ n, FiniteDimensional ℚ (chain.X n)
  bound : ℕ
  zero_above : ∀ n, bound ≤ n → Subsingleton (chain.X n)
  comparison : ∀ n, Homology X n ≅ chain.homology n

variable {X : TopCat.{0}} (M : Model X)
include M

theorem Model.homology_finite (n : ℕ) : FiniteDimensional ℚ (Homology X n) := by
  let := M.finite n
  let := chain_homology_finite M.chain n
  exact FiniteDimensional.of_injective (M.comparison n).toLinearEquiv.toLinearMap
    (M.comparison n).toLinearEquiv.injective

theorem Model.homology_zero (n : ℕ) (hn : M.bound ≤ n) :
    Subsingleton (Homology X n) := by
  let := chain_homology_zero M.chain n (M.zero_above n hn)
  exact (M.comparison n).toLinearEquiv.injective.subsingleton

theorem Model.betti_zero (n : ℕ) (hn : M.bound ≤ n) : betti X n = 0 := by
  let := M.homology_zero n hn
  exact Module.finrank_zero_of_subsingleton

theorem Model.support_subset : Function.support (betti X) ⊆ Finset.range M.bound := by
  intro n hn
  apply Finset.mem_range.mpr
  by_contra h
  exact hn (M.betti_zero n (by omega))

theorem Model.admissible : Admissible X :=
  ⟨M.homology_finite, (Finset.finite_toSet _).subset M.support_subset⟩

theorem Model.betti_comparison (n : ℕ) :
    betti X n = Module.finrank ℚ (M.chain.homology n) :=
  (M.comparison n).toLinearEquiv.finrank_eq

end KroneckerFiniteChainHomology
end
end

/- Original module: KroneckerQuotientOpenCover -/
section
/-! The quotient-map condition is local on an open cover of the target.
This supplies the topological gluing step for affine GIT charts. It does not
assert that the analytic moduli charts or their quotient maps have been built. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerQuotientOpenCover
open Set TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type*} {U : ι → Opens Y} {f : X → Y}

theorem surjective_of_restrictPreimage
    (hU : IsOpenCover U)
    (h : ∀ i, Function.Surjective ((U i).1.restrictPreimage f)) :
    Function.Surjective f := by
  intro y
  obtain ⟨i, hi⟩ := hU.exists_mem y
  obtain ⟨x, hx⟩ := h i ⟨y, hi⟩
  exact ⟨x.val, congrArg Subtype.val hx⟩

theorem isQuotientMap_of_restrictPreimage
    (hf : Continuous f) (hU : IsOpenCover U)
    (h : ∀ i, IsQuotientMap ((U i).1.restrictPreimage f)) :
    IsQuotientMap f := by
  refine ⟨?_, surjective_of_restrictPreimage hU (fun i => (h i).surjective)⟩
  apply IsCoinducing.of_isOpen_preimage_iff_isOpen
  intro s
  constructor
  · intro hs
    apply hU.isOpen_iff_coe_preimage.mpr
    intro i
    apply (h i).isOpen_preimage.mp
    exact hs.preimage continuous_subtype_val
  · exact fun hs => hs.preimage hf

theorem isQuotientMap_iff_restrictPreimage
    (hf : Continuous f) (hU : IsOpenCover U) :
    IsQuotientMap f ↔ ∀ i, IsQuotientMap ((U i).1.restrictPreimage f) := by
  constructor
  · exact fun h i => h.restrictPreimage_isOpen (U i).isOpen
  · exact isQuotientMap_of_restrictPreimage hf hU

/-- Local continuity also suffices, so a chart assembly does not need an
independent global continuity assumption. -/
theorem continuous_of_restrictPreimage
    (hU : IsOpenCover U) (hpre : ∀ i, IsOpen (f ⁻¹' U i))
    (h : ∀ i, Continuous ((U i).1.restrictPreimage f)) : Continuous f := by
  apply continuous_def.mpr
  intro s hs
  have hi (i : ι) : IsOpen ((f ⁻¹' s) ∩ (f ⁻¹' U i)) := by
    have hopen := ((hs.preimage continuous_subtype_val).preimage (h i))
    have himage := (hpre i).isOpenEmbedding_subtypeVal.isOpenMap _ hopen
    convert himage using 1
    ext x
    constructor
    · rintro ⟨hxs, hxU⟩
      exact ⟨⟨x, hxU⟩, hxs, rfl⟩
    · rintro ⟨x', hxs, rfl⟩
      exact ⟨hxs, x'.property⟩
  have hset : (f ⁻¹' s) = ⋃ i, ((f ⁻¹' s) ∩ (f ⁻¹' U i)) := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hU.exists_mem (f x)
      exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, _⟩
      exact hx
  rw [hset]
  exact isOpen_iUnion hi

theorem isQuotientMap_of_open_charts
    (hU : IsOpenCover U) (hpre : ∀ i, IsOpen (f ⁻¹' U i))
    (h : ∀ i, IsQuotientMap ((U i).1.restrictPreimage f)) :
    IsQuotientMap f :=
  isQuotientMap_of_restrictPreimage
    (continuous_of_restrictPreimage hU hpre (fun i => (h i).continuous)) hU h

end KroneckerQuotientOpenCover
end
end

/- Original module: KroneckerQuotientChartTransport -/
section
/-! Transport an affine polystable quotient comparison to an open stable chart.
The affine comparison is an explicit input. The restriction, diagram transport,
and gluing deductions are internal. No GIT existence theorem is asserted here. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerQuotientChartTransport
open Set Topology TopologicalSpace

variable {X Y A B : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B]

theorem quotient_of_commuting_homeomorphs (f : X → Y) (q : A → B)
    (a : X ≃ₜ A) (b : Y ≃ₜ B) (hq : IsQuotientMap q)
    (commutes : ∀ x, b (f x) = q (a x)) : IsQuotientMap f := by
  have heq : f = b.symm ∘ q ∘ a := by
    funext x
    apply b.injective
    simpa using commutes x
  rw [heq]
  exact b.symm.isQuotientMap.comp (hq.comp a.isQuotientMap)

/-- The published affine polystable comparison, followed by restriction to an
open set of the affine quotient, gives the required stable quotient map. -/
theorem affine_open_quotient (S : Setoid A) (e : Quotient S ≃ₜ B)
    (U : Opens B) :
    IsQuotientMap (U.1.restrictPreimage (e ∘ Quotient.mk S)) := by
  have hq : IsQuotientMap (e ∘ Quotient.mk S) :=
    e.isQuotientMap.comp isQuotientMap_quotient_mk'
  exact hq.restrictPreimage_isOpen U.isOpen

/-- A checked commuting diagram is essential: an unrelated homeomorphism of
the same spaces does not identify the moduli projection. -/
theorem stable_chart_quotient (f : X → Y) (S : Setoid A)
    (e : Quotient S ≃ₜ B) (U : Opens B)
    (a : X ≃ₜ ((e ∘ Quotient.mk S) ⁻¹' (U : Set B)))
    (b : Y ≃ₜ U)
    (commutes : ∀ x, b (f x) = U.1.restrictPreimage (e ∘ Quotient.mk S) (a x)) :
    IsQuotientMap f :=
  quotient_of_commuting_homeomorphs f _ a b (affine_open_quotient S e U) commutes

/-- The fiber equivalence is transported through the same diagram. -/
theorem stable_chart_fibers (f : X → Y) (S : Setoid A)
    (e : Quotient S ≃ₜ B) (U : Opens B)
    (a : X ≃ₜ ((e ∘ Quotient.mk S) ⁻¹' (U : Set B)))
    (b : Y ≃ₜ U)
    (commutes : ∀ x, b (f x) = U.1.restrictPreimage (e ∘ Quotient.mk S) (a x))
    (x y : X) : f x = f y ↔ S.r (a x).val (a y).val := by
  rw [← b.injective.eq_iff, commutes x, commutes y]
  change (⟨e (Quotient.mk S (a x).val), _⟩ : U) =
    ⟨e (Quotient.mk S (a y).val), _⟩ ↔ _
  rw [Subtype.mk.injEq, e.injective.eq_iff, Quotient.eq]

variable {ι : Type*} {U : ι → Opens Y} {f : X → Y}

/-- Equality of global fibers can be checked on an open cover, provided the
global relation preserves the projection. This separation prevents the orbit
dictionary from being hidden in a topological quotient-map hypothesis. -/
theorem fibers_of_open_charts (hU : IsOpenCover U) (R : X → X → Prop)
    (invariant : ∀ x y, R x y → f x = f y)
    (local_fibers : ∀ i (x y : f ⁻¹' (U i : Set Y)),
      (U i).1.restrictPreimage f x = (U i).1.restrictPreimage f y → R x.val y.val)
    (x y : X) : f x = f y ↔ R x y := by
  constructor
  · intro hxy
    obtain ⟨i, hi⟩ := hU.exists_mem (f x)
    have hy : f y ∈ U i := hxy ▸ hi
    exact local_fibers i ⟨x, hi⟩ ⟨y, hy⟩ (Subtype.ext hxy)
  · exact invariant x y

end KroneckerQuotientChartTransport
end
end

/- Original module: KroneckerPublishedAtlasAssembly -/
section
/-! An explicit application boundary for the two independent parts of G01.
The chart maps have the actual stable matrix families as their source. The
global quotient and Euler comparison are derived, not fields of the atlas.
Existence of these atlases and finite chain models remains unproved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPublishedAtlasAssembly
open KroneckerPublishedModuli KroneckerStableOrbitEuler
open KroneckerQuotientOpenCover KroneckerQuotientChartTransport
open KroneckerOrdinarySingularEuler Topology TopologicalSpace

structure Atlas (D : Datum) (Y : TopCat.{0}) where
  project : StableFamily D.source D.target D.dimension D.weight → Y
  index : Type
  chart : index → Opens Y
  cover : IsOpenCover chart
  preimage_open : ∀ i, IsOpen (project ⁻¹' (chart i : Set Y))
  local_quotient : ∀ i, IsQuotientMap ((chart i).1.restrictPreimage project)
  invariant : ∀ M N, (orbitSetoid D.source D.target D.dimension D.weight).r M N →
    project M = project N
  local_fibers : ∀ i (M N : project ⁻¹' (chart i : Set Y)),
    (chart i).1.restrictPreimage project M = (chart i).1.restrictPreimage project N →
      (orbitSetoid D.source D.target D.dimension D.weight).r M.val N.val

variable {D : Datum} {Y : TopCat.{0}} (A : Atlas D Y)

theorem Atlas.quotient : IsQuotientMap A.project :=
  isQuotientMap_of_open_charts A.cover A.preimage_open A.local_quotient

theorem Atlas.continuous : Continuous A.project := A.quotient.continuous

theorem Atlas.surjective : Function.Surjective A.project := A.quotient.surjective

theorem Atlas.fibers (M N : StableFamily D.source D.target D.dimension D.weight) :
    A.project M = A.project N ↔
      (orbitSetoid D.source D.target D.dimension D.weight).r M N :=
  fibers_of_open_charts A.cover _ A.invariant A.local_fibers M N

def Atlas.presentation : Presentation D Y where
  project := A.project
  quotient := A.quotient
  fibers := A.fibers

/-- The finite model input carries chain groups and homology comparisons, not
the desired Euler number. Its existence is still a geometric obligation. -/
def geometry (Y : Datum → TopCat.{0}) (atlas : ∀ D, Atlas D (Y D))
    (model : ∀ D, KroneckerFiniteChainHomology.Model (Y D)) : Geometry where
  space := Y
  presentation D := (atlas D).presentation
  admissible D := (model D).admissible

theorem geometry_space (Y : Datum → TopCat.{0}) (atlas : ∀ D, Atlas D (Y D))
    (model : ∀ D, KroneckerFiniteChainHomology.Model (Y D)) (D : Datum) :
    (geometry Y atlas model).space D = Y D := rfl

theorem canonical_admissible (Y : Datum → TopCat.{0}) (atlas : ∀ D, Atlas D (Y D))
    (model : ∀ D, KroneckerFiniteChainHomology.Model (Y D)) (D : Datum) :
    Admissible (canonical D) := (geometry Y atlas model).canonicalAdmissible D

theorem actual_euler_comparison (Y : Datum → TopCat.{0}) (atlas : ∀ D, Atlas D (Y D))
    (model : ∀ D, KroneckerFiniteChainHomology.Model (Y D)) (D : Datum) :
    ordinaryEuler (canonical D) (canonical_admissible Y atlas model D) =
      ordinaryEuler (Y D) (model D).admissible :=
  (geometry Y atlas model).euler_comparison D

end KroneckerPublishedAtlasAssembly
end
end

/- Original module: KroneckerScopedRealization -/
section
/-! Pointwise realization data and the exact scoped construction problem.
No realization witness is asserted to exist. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedRealization
open KroneckerPublishedModuli KroneckerApplicationScope KroneckerOrdinarySingularEuler
attribute [local instance] Classical.propDecidable

structure Realization (D : Datum) where
  space : TopCat.{0}
  presentation : Presentation D space
  admissible : Admissible space

def ofAtlas (D : Datum) (Y : TopCat.{0})
    (atlas : KroneckerPublishedAtlasAssembly.Atlas D Y)
    (model : KroneckerFiniteChainHomology.Model Y) : Realization D :=
  ⟨Y,atlas.presentation,model.admissible⟩

def ofGeometry (G : KroneckerScopedModuli.Geometry) (D : Datum) [Covered D] : Realization D :=
  ⟨G.space D,G.presentation D,G.admissible D⟩

def Realization.comparison {D : Datum} (R : Realization D) : canonical D ≃ₜ R.space :=
  (KroneckerQuotientHomeomorphism.descend _ _ (Homeomorph.refl _)
    (fun M N => (R.presentation.fibers M N).symm)).trans
    (Topology.IsQuotientMap.homeomorph
      (f:=⟨R.presentation.project,R.presentation.quotient.continuous⟩) R.presentation.quotient)

def Realization.canonicalAdmissible {D : Datum} (R : Realization D) : Admissible (canonical D) :=
  KroneckerHomologyHomeomorphism.admissible_transfer R.comparison R.admissible

def Realization.euler {D : Datum} (R : Realization D) : ℤ := ordinaryEuler R.space R.admissible

theorem Realization.euler_comparison {D : Datum} (R : Realization D) :
    ordinaryEuler (canonical D) R.canonicalAdmissible=R.euler :=
  KroneckerHomologyHomeomorphism.euler_eq R.comparison _ _

def Realization.transport {D E : Datum} (h : D=E) (R : Realization D) : Realization E := h ▸ R

def Realization.compare {D : Datum} (R S : Realization D) : R.space ≃ₜ S.space :=
  R.comparison.symm.trans S.comparison

theorem Realization.euler_independent {D : Datum} (R S : Realization D) : R.euler=S.euler :=
  KroneckerHomologyHomeomorphism.euler_eq (R.compare S) R.admissible S.admissible

def select (R : ∀ i : Index,Realization i.datum) (D : Datum) [h : Covered D] : Realization D :=
  (R h.witness.choose).transport h.witness.choose_spec

/-- Unused data retain their actual canonical quotient as their space. No
presentation or homology assertion is supplied or used outside Covered. -/
def geometry (R : ∀ i : Index,Realization i.datum) : KroneckerScopedModuli.Geometry where
  space D := if h : Covered D then (@select R D h).space else canonical D
  presentation D h := by
    letI : Covered D := h
    classical
    rw [dite_eq_left (inferInstance : Covered D)]
    exact (select R D).presentation
  admissible D h := by
    let : Covered D := h
    classical
    rw [dite_eq_left (inferInstance : Covered D)]
    exact (select R D).admissible

theorem selected_space (R : ∀ i : Index,Realization i.datum) (D : Datum) [Covered D] :
    (geometry R).space D=(select R D).space := by
  classical
  simp only [geometry,dite_eq_left (inferInstance : Covered D)]

theorem scope_realization_iff :
    Nonempty KroneckerScopedModuli.Geometry ↔ Nonempty (∀ i : Index,Realization i.datum) := by
  constructor
  · rintro ⟨G⟩
    exact ⟨fun i => ofGeometry G i.datum⟩
  · rintro ⟨R⟩
    exact ⟨geometry R⟩

end KroneckerScopedRealization
end
end

/- Original module: KroneckerScopedCanonicalGeometry -/
section
/-! The scoped geometry gate is exactly finite ordinary homology of the actual
canonical quotients. Their quotient presentations are constructed here. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedCanonicalGeometry
open KroneckerPublishedModuli KroneckerApplicationScope KroneckerOrdinarySingularEuler
open KroneckerScopedRealization

def canonicalPresentation (D : Datum) : Presentation D (canonical D) where
  project := KroneckerCanonicalStableOrbit.project D.source D.target D.dimension D.weight
  quotient := isQuotientMap_quotient_mk'
  fibers := fun _ _ => Quotient.eq

def CanonicalFinite : Prop := ∀ (D : Datum) [Covered D],Admissible (canonical D)

def canonicalRealization (H : CanonicalFinite) (D : Datum) [Covered D] : Realization D :=
  ⟨canonical D,canonicalPresentation D,H D⟩

def canonicalGeometry (H : CanonicalFinite) : KroneckerScopedModuli.Geometry where
  space := canonical
  presentation D _ := canonicalPresentation D
  admissible D _ := H D

theorem canonical_geometry_space (H : CanonicalFinite) (D : Datum) :
    (canonicalGeometry H).space D=canonical D := rfl

theorem canonical_geometry_euler (H : CanonicalFinite) (D : Datum) [Covered D] :
    (canonicalGeometry H).euler D=ordinaryEuler (canonical D) (H D) := rfl

theorem geometry_implies_canonical_finite (G : KroneckerScopedModuli.Geometry) : CanonicalFinite :=
  fun D _ => G.canonicalAdmissible D

theorem geometry_iff_canonical_finite :
    Nonempty KroneckerScopedModuli.Geometry ↔ CanonicalFinite :=
  ⟨fun ⟨G⟩ => geometry_implies_canonical_finite G,fun H => ⟨canonicalGeometry H⟩⟩

theorem canonical_finite_iff_indices :
    CanonicalFinite ↔ ∀ i : Index,Admissible (canonical i.datum) := by
  constructor
  · intro H i
    exact H i.datum
  · intro H D h
    obtain ⟨i,hi⟩ := h.witness
    rw [← hi]
    exact H i

theorem canonical_finite_iff_families : CanonicalFinite ↔
    (∀ m a b,Admissible (canonical (KroneckerAllMPublishedDatum.datum m a b))) ∧
    (∀ a b,Admissible (canonical (KroneckerWeistApplicationGates.base a b))) ∧
    (∀ a b (d : (wordCover (KroneckerWeistApplicationGates.base a b)).V →₀ ℕ),
      Compatible (KroneckerWeistApplicationGates.base a b) d →
      Admissible (canonical (coverDatum (KroneckerWeistApplicationGates.base a b) d))) := by
  rw [canonical_finite_iff_indices]
  constructor
  · intro H
    exact ⟨fun m a b => H (.kronecker m a b),fun a b => H (.localizationBase a b),
      fun a b d h => H (.localizationCover a b d h)⟩
  · rintro ⟨hb,hl,hc⟩ i
    cases i with
    | kronecker m a b => exact hb m a b
    | localizationBase a b => exact hl a b
    | localizationCover a b d h => exact hc a b d h

end KroneckerScopedCanonicalGeometry
end
end
