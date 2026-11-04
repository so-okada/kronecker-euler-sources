import KroneckerTypedQuiverMaps
import KroneckerDirectSumAbelianCover

/-! An injective quiver map lifts from the direct-sum abelian cover to the
product-character abelian cover by extending finitely supported characters
along the arrow injection. Missing arrow coordinates are exactly zero. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerDirectSumCoverEmbeddingLift
open KroneckerAbelianCover KroneckerTypedQuiverMaps KroneckerDirectSumAbelianCover
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P Q : TypedQuiver}

def pushCharacter (f : QuiverMap P Q) (χ : P.A →₀ ℤ) : Character Q.A := χ.mapDomain f.arrow

theorem pushCharacter_add (f : QuiverMap P Q) (χ ψ : P.A →₀ ℤ) :
    pushCharacter f (χ+ψ) = pushCharacter f χ + pushCharacter f ψ := by
  unfold pushCharacter
  rw [Finsupp.mapDomain_add]
  rfl

theorem pushCharacter_single (f : QuiverMap P Q) (a : P.A) :
    pushCharacter f (Finsupp.single a 1) = unit (f.arrow a) := by
  unfold pushCharacter
  rw [Finsupp.mapDomain_single]
  funext b
  simp only [Finsupp.single_apply,unit,Pi.single_apply,eq_comm]

theorem pushCharacter_injective (f : QuiverMap P Q) (ha : Function.Injective f.arrow) :
    Function.Injective (pushCharacter f) := by
  intro χ ψ h
  apply Finsupp.mapDomain_injective ha
  exact Finsupp.ext (congrFun h)


def liftMap (f : QuiverMap P Q) : QuiverMap (directCover P) Q.abelian where
  vertex v := (f.vertex v.1,pushCharacter f v.2)
  arrow a := (f.arrow a.1,pushCharacter f a.2)
  source a := by
    apply Prod.ext
    · exact f.source a.1
    · rfl
  target a := by
    apply Prod.ext
    · exact f.target a.1
    · change pushCharacter f a.2 + unit (f.arrow a.1) = pushCharacter f (a.2 + Finsupp.single a.1 1)
      rw [pushCharacter_add,pushCharacter_single]

theorem lift_vertex_injective (f : QuiverMap P Q) (hv : Function.Injective f.vertex)
    (ha : Function.Injective f.arrow) : Function.Injective (liftMap f).vertex := by
  intro x y h
  apply Prod.ext
  · exact hv (congrArg (fun z : Q.abelian.V => z.1) h)
  · exact pushCharacter_injective f ha (congrArg (fun z : Q.abelian.V => z.2) h)

theorem lift_arrow_injective (f : QuiverMap P Q) (ha : Function.Injective f.arrow) :
    Function.Injective (liftMap f).arrow := by
  intro x y h
  apply Prod.ext
  · exact ha (congrArg (fun z : Q.abelian.A => z.1) h)
  · exact pushCharacter_injective f ha (congrArg (fun z : Q.abelian.A => z.2) h)

end KroneckerDirectSumCoverEmbeddingLift
