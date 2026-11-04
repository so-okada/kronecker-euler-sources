import KroneckerEmbeddedRepresentationEquivalence

/-! The embedded-component representation equivalence identifies all
subrepresentations, not just selected coordinate subspaces. On positive
vertices it is the actual pullback family of submodules. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEmbeddedSubrepresentationEquivalence
open KroneckerAbelianCover KroneckerFiniteQuiverHom KroneckerTypedQuiverMaps
open KroneckerEmbeddedFiniteDimensions KroneckerFiniteSupportInducedQuiver
open KroneckerFiniteSupportDeckRepresentationTransport KroneckerDirectSumEmbeddingLocalLifts
open KroneckerEmbeddedSupportQuiverIso KroneckerEmbeddedRepresentationEquivalence
open KroneckerFiniteSupportSubrepresentations KroneckerQuiverPullbackSubrepresentations
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

def castSubrep {V A : Type} {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (h : R = S) : Subrep R ≃ Subrep S :=
  Equiv.cast (congrArg Subrep h)

theorem castSubrep_space {V A : Type} {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (h : R = S) (U : Subrep R) (v : V) :
    (castSubrep h U).space v = U.space v := by subst S; rfl

def subrepEquiv (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) :
    Subrep R ≃ Subrep (KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd R) :=
  (KroneckerFiniteSupportSubrepresentations.subrepEquiv Q d R).trans
    ((pullSubrepEquiv (supportIso f hv ha hf d hd) (supportFinsupp d) (restrictToSupport Q d R)).trans
      ((castSubrep (restricted_representation f hv ha hf d hd R).symm).trans
        (KroneckerFiniteSupportSubrepresentations.subrepEquiv P (descend f.vertex hv d)
          (KroneckerEmbeddedRepresentationEquivalence.representationEquiv f hv ha hf d hd R)).symm))

set_option backward.isDefEq.respectTransparency false in
theorem subrep_space_on_support (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) (hf : LocallySurjective f)
    (d : Q.V →₀ ℕ) (hd : InImage f.vertex d)
    (R : Representation Q.source Q.target (fun v => d v)) (U : Subrep R)
    (v : P.V) (h : v ∈ (descend f.vertex hv d).support) :
    (subrepEquiv f hv ha hf d hd R U).space v = U.space (f.vertex v) := by
  change (if h' : v ∈ (descend f.vertex hv d).support then
    (castSubrep (restricted_representation f hv ha hf d hd R).symm
      (pullSubrep (supportIso f hv ha hf d hd) (supportFinsupp d) (restrictToSupport Q d R)
        (restrictSubrep Q d R U))).space ⟨v,h'⟩ else (⊥ : Submodule ℂ (Space (descend f.vertex hv d v)))) = _
  rw [dite_eq_left h,castSubrep_space]
  rfl

end KroneckerEmbeddedSubrepresentationEquivalence
