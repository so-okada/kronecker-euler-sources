import KroneckerAbstractPairIso
import KroneckerReflectionPairStability

section

/-! The coordinate-free two-space isomorphism notion agrees exactly with
the pinned same-label representation isomorphisms for the canonical Kronecker quiver. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairIsoCanonicalDictionary
open KroneckerFiniteQuiverHom KroneckerCanonicalKroneckerModuli KroneckerReflectionPairModel
variable {m a b : ℕ} {R S : PairRep m a b}

def toCanonical (e : KroneckerAbstractPairIso.Iso R S) :
    KroneckerFiniteQuiverHom.Iso (toRepresentation R) (toRepresentation S) where
  map v := Fin.cases (motive:=fun v => Space (dimension a b v) ≃ₗ[ℂ] Space (dimension a b v))
    e.source (fun j => by have hj : j=0 := Subsingleton.elim _ _;subst j;exact e.sink) v
  commutes i x := by
    simp only [source,target,toRepresentation]
    change e.sink (R i x)=S i (e.source x)
    exact e.commutes i x

def fromCanonical (e : KroneckerFiniteQuiverHom.Iso (toRepresentation R) (toRepresentation S)) :
    KroneckerAbstractPairIso.Iso R S := ⟨e.map 0,e.map 1,e.commutes⟩

theorem isomorphic_iff : Nonempty (KroneckerAbstractPairIso.Iso R S) ↔
    Nonempty (KroneckerFiniteQuiverHom.Iso (toRepresentation R) (toRepresentation S)) :=
  ⟨fun ⟨e⟩ => ⟨toCanonical e⟩,fun ⟨e⟩ => ⟨fromCanonical e⟩⟩
end KroneckerPairIsoCanonicalDictionary
end
end

section

/-! Dimension equalities transport actual representations and stability,
with an explicit representation isomorphism recording the coordinate cast. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPairDimensionTransport
open KroneckerReflectionPairModel
variable {m a b c d : ℕ}

def transport (ha : a=c) (hb : b=d) (R : PairRep m a b) : PairRep m c d := ha ▸ hb ▸ R

def iso (ha : a=c) (hb : b=d) (R : PairRep m a b) :
    KroneckerAbstractPairIso.Iso R (transport ha hb R) := by
  subst c
  subst d
  exact KroneckerAbstractPairIso.refl R

theorem stable_iff (ha : a=c) (hb : b=d) (R : PairRep m a b) :
    PairStable (transport ha hb R) ↔ PairStable R := by
  subst c
  subst d
  rfl
end KroneckerPairDimensionTransport
end
end

