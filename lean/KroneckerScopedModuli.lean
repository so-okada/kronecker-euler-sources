import KroneckerAllMPublishedDatum
import KroneckerWeistApplicationGates

/- Original module: KroneckerApplicationScope -/
section
/-! Exactly the base and compatible-cover data used by the selected application.
No closure under further covers is imposed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerApplicationScope
open KroneckerPublishedModuli KroneckerAllMPublishedDatum KroneckerWeistApplicationGates

inductive Index : Type
  | kronecker (m a b : ℕ)
  | localizationBase (a b : ℕ)
  | localizationCover (a b : ℕ) (d : (wordCover (base a b)).V →₀ ℕ)
      (compatible : Compatible (base a b) d)

def Index.datum : Index → Datum
  | .kronecker m a b => KroneckerAllMPublishedDatum.datum m a b
  | .localizationBase a b => base a b
  | .localizationCover a b d _ => coverDatum (base a b) d

/-- Membership is witnessed by a concrete application index, not an arbitrary predicate. -/
class Covered (D : Datum) : Prop where
  witness : ∃ i : Index,i.datum=D

instance kroneckerCovered (m a b : ℕ) : Covered (datum m a b) :=
  ⟨⟨.kronecker m a b,rfl⟩⟩

instance localizationBaseCovered (a b : ℕ) : Covered (base a b) :=
  ⟨⟨.localizationBase a b,rfl⟩⟩

def coverCovered (a b : ℕ) (d : (wordCover (base a b)).V →₀ ℕ)
    (h : Compatible (base a b) d) : Covered (coverDatum (base a b) d) :=
  ⟨⟨.localizationCover a b d h,rfl⟩⟩

instance indexCovered (i : Index) : Covered i.datum := ⟨⟨i,rfl⟩⟩

instance activeCoverCovered (a b : ℕ)
    (q : KroneckerWeistStableIndexEquivalence.SourceIndex a b) :
    Covered (coverDatum (base a b) (KroneckerWeistIndexedSpaces.representative a b q).1) :=
  coverCovered a b _ ((compatible_dictionary a b _).mpr
    (KroneckerWeistIndexedSpaces.representative_spec a b q).2.1)

theorem covered_cases (D : Datum) [h : Covered D] :
    (∃ m a b,D=datum m a b) ∨ (∃ a b,D=base a b) ∨
      ∃ (a b : ℕ) (d : (wordCover (base a b)).V →₀ ℕ),
        Compatible (base a b) d ∧ D=coverDatum (base a b) d := by
  obtain ⟨i,hi⟩ := h.witness
  cases i with
  | kronecker m a b => exact Or.inl ⟨m,a,b,hi.symm⟩
  | localizationBase a b => exact Or.inr (Or.inl ⟨a,b,hi.symm⟩)
  | localizationCover a b d hc => exact Or.inr (Or.inr ⟨a,b,d,hc,hi.symm⟩)

theorem covered_acyclic (D : Datum) [Covered D] : Acyclic D := by
  rcases covered_cases D with ⟨m,a,b,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,d,hc,rfl⟩
  · exact KroneckerAllMPublishedDatum.acyclic m a b
  · exact base_acyclic a b
  · exact KroneckerWeistApplicationGates.cover_acyclic a b d

end KroneckerApplicationScope
end
end

/- Original module: KroneckerScopedModuli -/
section
/-! Analytic presentations and finite ordinary homology are required only on
the application scope. The space field has no claims outside that scope. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedModuli
export KroneckerPublishedModuli (Datum Presentation canonical Balanced Nonzero Acyclic
  Connected Indivisible sourceSlope stable_iff_source_slope wordCover shift shifted
  shifted_one shifted_mul translationSetoid Class arrowCode arrowCode_injective coverDatum Compatible)
open KroneckerApplicationScope KroneckerOrdinarySingularEuler KroneckerWeistApplicationGates
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure Geometry where
  space : Datum → TopCat.{0}
  presentation : ∀ (D : Datum) [Covered D], Presentation D (space D)
  admissible : ∀ (D : Datum) [Covered D], Admissible (space D)

def Geometry.comparison (G : Geometry) (D : Datum) [Covered D] : canonical D ≃ₜ G.space D :=
  (KroneckerQuotientHomeomorphism.descend _ _ (Homeomorph.refl _)
    (fun M N => ((G.presentation D).fibers M N).symm)).trans
    (Topology.IsQuotientMap.homeomorph
      (f:=⟨(G.presentation D).project,(G.presentation D).quotient.continuous⟩)
      (G.presentation D).quotient)

def Geometry.canonicalAdmissible (G : Geometry) (D : Datum) [Covered D] : Admissible (canonical D) :=
  KroneckerHomologyHomeomorphism.admissible_transfer (G.comparison D) (G.admissible D)

def Geometry.euler (G : Geometry) (D : Datum) [Covered D] : ℤ :=
  ordinaryEuler (G.space D) (G.admissible D)

theorem Geometry.euler_comparison (G : Geometry) (D : Datum) [Covered D] :
    ordinaryEuler (canonical D) (G.canonicalAdmissible D)=G.euler D :=
  KroneckerHomologyHomeomorphism.euler_eq (G.comparison D) _ _

def localizationTerm (G : Geometry) (a b : ℕ) (d : (wordCover (base a b)).V →₀ ℕ) : ℤ :=
  if h : Compatible (base a b) d then
    letI := coverCovered a b d h
    G.euler (coverDatum (base a b) d)
  else 0

structure Weist (G : Geometry) : Prop where
  localization : ∀ a b : ℕ,Acyclic (base a b) → Connected (base a b) →
    Nonzero (base a b) → Balanced (base a b) →
    ∀ (rep : Class (base a b) → (wordCover (base a b)).V →₀ ℕ),
      (∀ q,Quotient.mk (translationSetoid (base a b)) (rep q)=q) →
      G.euler (base a b)=∑ᶠ q,localizationTerm G a b (rep q)
  positive : ∀ (D : Datum) [Covered D], Acyclic D → Nonzero D → Balanced D → Indivisible D →
    Nonempty (G.space D) → 1≤G.euler D

end KroneckerScopedModuli
end
end
