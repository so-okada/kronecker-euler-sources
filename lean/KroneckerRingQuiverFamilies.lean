import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Group.Units.Hom

/- Arbitrary-base finite free quiver families. No stability, quotient, or Euler
claim is built into the definitions. -/
set_option autoImplicit false
namespace KroneckerRingQuiverFamilies
universe u v w
variable {V A : Type} (s t : A → V) (d : V → ℕ)

/-- Actual matrices of arrow maps on vertexwise free modules. -/
abbrev Family (R : Type u) := ∀ a, Matrix (Fin (d (t a))) (Fin (d (s a))) R

def changeRing {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Family s t d R) : Family s t d S :=
  fun a => (M a).map f

@[simp] theorem changeRing_id {R : Type u} [CommRing R] (M : Family s t d R) :
    changeRing s t d (RingHom.id R) M = M := rfl

@[simp] theorem changeRing_comp {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (M : Family s t d R) :
    changeRing s t d g (changeRing s t d f M) = changeRing s t d (g.comp f) M := rfl

/-- Vertexwise changes of basis, including the zero-dimensional matrix ring. -/
abbrev Gauge (R : Type u) [CommRing R] := ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ

def gauge {R : Type u} [CommRing R] (g : Gauge d R)
    (M : Family s t d R) : Family s t d R :=
  fun a => (g (t a) : Matrix _ _ R) * M a * (↑((g (s a))⁻¹) : Matrix _ _ R)

@[simp] theorem gauge_one {R : Type u} [CommRing R] (M : Family s t d R) :
    gauge s t d 1 M = M := by
  funext a
  simp [gauge]

/-- This is a genuine product-GL action, not an equivalence relation declared by hand. -/
theorem gauge_mul {R : Type u} [CommRing R] (g h : Gauge d R)
    (M : Family s t d R) :
    gauge s t d (g * h) M = gauge s t d g (gauge s t d h M) := by
  funext a
  simp [gauge, Matrix.mul_assoc]

/-- Scalar base-change sends invertible vertex matrices to invertible matrices. -/
def changeGauge {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (g : Gauge d R) : Gauge d S :=
  fun v => Units.map (f.mapMatrix.toMonoidHom) (g v)

/-- The GL action is compatible with every base-ring homomorphism. -/
theorem changeRing_gauge {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (g : Gauge d R) (M : Family s t d R) :
    changeRing s t d f (gauge s t d g M) =
      gauge s t d (changeGauge d f g) (changeRing s t d f M) := by
  funext a
  simp [changeRing, gauge, changeGauge, Matrix.map_mul]

abbrev VertexMap (R : Type u) := ∀ v, Matrix (Fin (d v)) (Fin (d v)) R

def commutation {R : Type u} [CommRing R] (M N : Family s t d R)
    (f : VertexMap d R) : Family s t d R :=
  fun a => f (t a) * M a - N a * f (s a)

/-- All commutation equations are polynomial and commute with scalar base-change. -/
theorem changeRing_commutation {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (M N : Family s t d R) (f : VertexMap d R) :
    changeRing s t d φ (commutation s t d M N f) =
      commutation s t d (changeRing s t d φ M) (changeRing s t d φ N)
        (fun v => (f v).map φ) := by
  funext a i j
  simp [changeRing, commutation, Matrix.mul_apply]

/-- The matrix commutation relation is exactly the relation for an arrow family
and its actual change of basis. -/
theorem gauge_commutes {R : Type u} [CommRing R] (g : Gauge d R)
    (M : Family s t d R) :
    commutation s t d M (gauge s t d g M) (fun v => ↑(g v)) = 0 := by
  funext a
  simp [commutation, gauge, Matrix.mul_assoc]

/-- Orbit membership is exactly the existence of an invertible commuting family. -/
theorem gauge_eq_iff {R : Type u} [CommRing R] (g : Gauge d R)
    (M N : Family s t d R) :
    gauge s t d g M = N ↔ ∀ a,
      (g (t a) : Matrix _ _ R) * M a = N a * (g (s a) : Matrix _ _ R) := by
  constructor
  · intro h a
    have ha := congrFun h a
    rw [← ha]
    simp [gauge, Matrix.mul_assoc]
  · intro h
    funext a
    simp [gauge, h a, Matrix.mul_assoc]

/-- Change of bases in both source and target acts on every morphism, and
conjugates the full commutation operator, not only its zero set. -/
theorem commutation_gauge {R : Type u} [CommRing R]
    (g h : Gauge d R) (M N : Family s t d R) (f : VertexMap d R) :
    commutation s t d (gauge s t d h M) (gauge s t d g N)
      (fun v => (g v : Matrix _ _ R) * f v * (↑((h v)⁻¹) : Matrix _ _ R)) =
      fun a => (g (t a) : Matrix _ _ R) * commutation s t d M N f a *
        (↑((h (s a))⁻¹) : Matrix _ _ R) := by
  funext a
  simp [commutation, gauge, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  congr 1
  rw [← Matrix.mul_assoc]
  simp

end KroneckerRingQuiverFamilies
