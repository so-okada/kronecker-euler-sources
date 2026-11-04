import KroneckerCanonicalSupportOrbit
import KroneckerHomologyHomeomorphism
import Mathlib.GroupTheory.FreeGroup.Basic
import KroneckerQuotientHomeomorphism

/-! General source boundary, independent of the manuscript and of m=3.

`Geometry` is an EXTERNAL analytic geometric-quotient/finite-homology input.
It is not asserted to be proved here, nor silently included in Weist's two
corollaries. The quotient-to-model homeomorphism below IS proved in Lean.
`Weist` states Cor. 3.16 on ALL compatible translation classes (a finsum),
and the nonempty consequence of Cor. 3.11. No finite manuscript index,
count, lower bound, or specialized SourceInput occurs in these inputs.
-/
noncomputable section
set_option autoImplicit false
namespace KroneckerPublishedModuli
open KroneckerAbelianCover KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportStability KroneckerOrdinarySingularEuler
open KroneckerStableOrbitEuler KroneckerRingQuiverFamilies
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

structure Datum where
  V : Type
  A : Type
  vertices : Fintype V
  arrows : Fintype A
  source : A → V
  target : A → V
  dimension : V → ℕ
  weight : V → ℤ

attribute [instance] Datum.vertices Datum.arrows

def canonical (D : Datum) : TopCat.{0} :=
  KroneckerCanonicalStableOrbit.space D.source D.target D.dimension D.weight

def Balanced (D : Datum) : Prop := ∑ v, D.weight v * (D.dimension v : ℤ) = 0
def Nonzero (D : Datum) : Prop := D.dimension ≠ 0
/-- A strict vertex ranking certifies absence of oriented cycles. -/
def Acyclic (D : Datum) : Prop := ∃ rank : D.V → ℕ, ∀ e, rank (D.source e) < rank (D.target e)
/-- Connectedness of the underlying unoriented quiver, as in Section 3.4. -/
def Connected (D : Datum) : Prop := ∀ u v : D.V,
  Relation.ReflTransGen (fun u v => ∃ e : D.A,
    (D.source e=u ∧ D.target e=v) ∨ (D.target e=u ∧ D.source e=v)) u v
/-- Balanced weight zero is the slope of the full dimension vector. -/
def Indivisible (D : Datum) : Prop :=
  ∀ e : D.V → ℕ, e ≤ D.dimension → (∑ v, D.weight v * (e v : ℤ)) = 0 →
    e = 0 ∨ e = D.dimension

def sourceSlope (weight : ℤ) (size : ℕ) : ℝ := (weight : ℝ)/size

theorem sourceSlope_neg_iff (w : ℤ) (n : ℕ) (hn : 0<n) :
    sourceSlope w n < 0 ↔ w<0 := by
  unfold sourceSlope
  rw [div_lt_iff₀ (by exact_mod_cast hn : (0 : ℝ)<n),zero_mul]
  exact_mod_cast Iff.rfl (a := w<0)

/-- With the balanced character used as Theta, the full slope is zero.
This is the source's slope test on EVERY actual proper nonzero subrepresentation. -/
theorem stable_iff_source_slope (D : Datum)
    (R : KroneckerFiniteQuiverHom.Representation D.source D.target D.dimension) :
    KroneckerFiniteQuiverHom.Stable D.weight R ↔ Balanced D ∧
      ∀ U : KroneckerFiniteQuiverHom.Subrep R,
        0<KroneckerFiniteQuiverHom.size U →
        KroneckerFiniteQuiverHom.size U<∑ v,D.dimension v →
        sourceSlope (KroneckerFiniteQuiverHom.weight D.weight U) (KroneckerFiniteQuiverHom.size U) <
          sourceSlope (∑ v,D.weight v*(D.dimension v : ℤ)) (∑ v,D.dimension v) := by
  constructor
  · rintro ⟨hb,h⟩
    refine ⟨hb,fun U hn hp => ?_⟩
    rw [hb,show sourceSlope 0 (∑ v,D.dimension v)=0 by simp [sourceSlope]]
    exact (sourceSlope_neg_iff _ _ hn).mpr (h U hn hp)
  · rintro ⟨hb,h⟩
    refine ⟨hb,fun U hn hp => ?_⟩
    have hu := h U hn hp
    change (∑ v,D.weight v*(D.dimension v : ℤ))=0 at hb
    rw [hb,show sourceSlope 0 (∑ v,D.dimension v)=0 by simp [sourceSlope]] at hu
    exact (sourceSlope_neg_iff _ _ hn).mp hu

structure Presentation (D : Datum) (Y : TopCat.{0}) where
  project : StableFamily D.source D.target D.dimension D.weight → Y
  quotient : Topology.IsQuotientMap project
  fibers : ∀ M N, project M = project N ↔
    (orbitSetoid D.source D.target D.dimension D.weight).r M N

/-- This generic analytic realization, including finite homology, stays explicit.
It is stronger than King's algebraic quotient statement alone. -/
structure Geometry where
  space : Datum → TopCat.{0}
  presentation : ∀ D, Presentation D (space D)
  admissible : ∀ D, Admissible (space D)

def Geometry.comparison (G : Geometry) (D : Datum) : canonical D ≃ₜ G.space D :=
  (KroneckerQuotientHomeomorphism.descend _ _ (Homeomorph.refl _)
    (fun M N => ((G.presentation D).fibers M N).symm)).trans
    (Topology.IsQuotientMap.homeomorph
      (f := ⟨(G.presentation D).project,(G.presentation D).quotient.continuous⟩)
      (G.presentation D).quotient)

def Geometry.canonicalAdmissible (G : Geometry) (D : Datum) : Admissible (canonical D) :=
  KroneckerHomologyHomeomorphism.admissible_transfer (G.comparison D) (G.admissible D)

def Geometry.euler (G : Geometry) (D : Datum) : ℤ := ordinaryEuler (G.space D) (G.admissible D)

theorem Geometry.euler_comparison (G : Geometry) (D : Datum) :
    ordinaryEuler (canonical D) (G.canonicalAdmissible D) = G.euler D :=
  KroneckerHomologyHomeomorphism.euler_eq (G.comparison D) _ _

/-- Weist p.392: vertices (v,w), arrow (a,w) from (s(a),w) to (t(a),w*a).
The entire possibly disconnected word cover is retained. -/
@[reducible] def wordCover (D : Datum) : TypedQuiver where
  V := D.V × FreeGroup D.A
  A := D.A × FreeGroup D.A
  source e := (D.source e.1,e.2)
  target e := (D.target e.1,e.2 * FreeGroup.of e.1)

def shift (D : Datum) (g : FreeGroup D.A) (v : (wordCover D).V) := (v.1,g*v.2)
def shifted (D : Datum) (g : FreeGroup D.A) (d : (wordCover D).V →₀ ℕ) :=
  d.mapDomain (shift D g)

theorem shifted_one (D : Datum) (d : (wordCover D).V →₀ ℕ) : shifted D 1 d = d := by
  unfold shifted
  have h : shift D 1 = id := by funext v; simp [shift]
  rw [h,Finsupp.mapDomain_id]

theorem shifted_mul (D : Datum) (g h : FreeGroup D.A) (d : (wordCover D).V →₀ ℕ) :
    shifted D (g*h) d = shifted D g (shifted D h d) := by
  unfold shifted
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro v _
  simp [shift,mul_assoc]

def translationSetoid (D : Datum) : Setoid ((wordCover D).V →₀ ℕ) where
  r d e := ∃ g, shifted D g d = e
  iseqv := by
    constructor
    · intro d; exact ⟨1,shifted_one D d⟩
    · rintro d e ⟨g,hg⟩
      refine ⟨g⁻¹,?_⟩
      rw [←hg,←shifted_mul,inv_mul_cancel,shifted_one]
    · rintro d e f ⟨g,hg⟩ ⟨h,hh⟩
      refine ⟨h*g,?_⟩
      rw [shifted_mul,hg,hh]

abbrev Class (D : Datum) := Quotient (translationSetoid D)

def arrowCode (D : Datum) (d : (wordCover D).V →₀ ℕ)
    (e : (supportQuiver (wordCover D) d).A) : D.A × SupportVertex d :=
  (e.val.1,⟨(wordCover D).source e.val,e.property.1⟩)

theorem arrowCode_injective (D : Datum) (d : (wordCover D).V →₀ ℕ) :
    Function.Injective (arrowCode D d) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z => z.1) h
  · exact congrArg (fun z => z.2.val.2) h

def coverDatum (D : Datum) (d : (wordCover D).V →₀ ℕ) : Datum where
  V := SupportVertex d
  A := (supportQuiver (wordCover D) d).A
  vertices := inferInstance
  arrows := Fintype.ofInjective (arrowCode D d) (arrowCode_injective D d)
  source := (supportQuiver (wordCover D) d).source
  target := (supportQuiver (wordCover D) d).target
  dimension := supportDimension d
  weight := fun v => D.weight v.val.1

def Compatible (D : Datum) (d : (wordCover D).V →₀ ℕ) : Prop :=
  ∀ v, d.mapDomain Prod.fst v = D.dimension v

def localizationTerm (G : Geometry) (D : Datum) (d : (wordCover D).V →₀ ℕ) : ℤ :=
  if Compatible D d then G.euler (coverDatum D d) else 0

/-- Exact general external statements, using ordinary rational Euler on the
smooth complex stable moduli. Cor.3.16 is retained as the full class sum;
omission of empty summands and its finite form are proved in the application. -/
structure Weist (G : Geometry) : Prop where
  localization : ∀ (D : Datum), Acyclic D → Connected D → Nonzero D → Balanced D →
    ∀ (rep : Class D → (wordCover D).V →₀ ℕ),
      (∀ q, Quotient.mk (translationSetoid D) (rep q) = q) →
      G.euler D = ∑ᶠ q, localizationTerm G D (rep q)
  positive : ∀ (D : Datum), Acyclic D → Nonzero D → Balanced D → Indivisible D →
    Nonempty (G.space D) → 1 ≤ G.euler D

end KroneckerPublishedModuli
