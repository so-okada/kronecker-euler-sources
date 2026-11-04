import KroneckerCanonicalKroneckerModuli
import KroneckerStableOrbitHomeomorphism
import Mathlib.Topology.Instances.Matrix
import KroneckerOppositeSubrepresentationWeights
import KroneckerHomologyHomeomorphism

/- Original module: KroneckerContragredientMatrixUnits -/
section
/-! The inverse transpose is a group automorphism of GL over every commutative
ring.  Inversion is essential: transpose alone reverses multiplication. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
variable {n : ℕ} {R : Type} [CommRing R]

def contragredient (g : (Matrix (Fin n) (Fin n) R)ˣ) :
    (Matrix (Fin n) (Fin n) R)ˣ where
  val := (↑(g⁻¹) : Matrix _ _ R).transpose
  inv := (↑g : Matrix _ _ R).transpose
  val_inv := by rw [← Matrix.transpose_mul]; simp
  inv_val := by rw [← Matrix.transpose_mul]; simp

@[simp] theorem contragredient_val (g : (Matrix (Fin n) (Fin n) R)ˣ) :
    (↑(contragredient g) : Matrix (Fin n) (Fin n) R) =
      (↑(g⁻¹) : Matrix (Fin n) (Fin n) R).transpose := rfl

@[simp] theorem contragredient_involutive (g : (Matrix (Fin n) (Fin n) R)ˣ) :
    contragredient (contragredient g) = g := by
  apply Units.ext
  rfl

/-- Unlike transpose, inverse transpose preserves the order of group products. -/
def contragredientEquiv :
    (Matrix (Fin n) (Fin n) R)ˣ ≃* (Matrix (Fin n) (Fin n) R)ˣ where
  toFun := contragredient
  invFun := contragredient
  left_inv := contragredient_involutive
  right_inv := contragredient_involutive
  map_mul' g h := by
    apply Units.ext
    simp [contragredient, Matrix.transpose_mul]

end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerContragredientGauge -/
section
/-! The actual product-GL group is carried to itself by inverse transpose,
naturally over every base-ring homomorphism. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open KroneckerRingQuiverFamilies
variable {V : Type} (d : V → ℕ)

def oppositeGaugeEquiv (R : Type) [CommRing R] : Gauge d R ≃* Gauge d R where
  toFun g v := contragredient (g v)
  invFun g v := contragredient (g v)
  left_inv g := by funext v; exact contragredient_involutive (g v)
  right_inv g := by funext v; exact contragredient_involutive (g v)
  map_mul' g h := by
    funext v
    exact (contragredientEquiv (n := d v) (R := R)).map_mul (g v) (h v)

@[simp] theorem oppositeGauge_involutive {R : Type} [CommRing R] (g : Gauge d R) :
    oppositeGaugeEquiv d R (oppositeGaugeEquiv d R g) = g := by
  funext v
  exact contragredient_involutive (g v)


end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerExchangeQuiverCoordinates -/
section
/-! Source/sink exchange is an exact weighted typed-quiver isomorphism from
the opposite m-arrow quiver to the original, for every arrow count. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeQuiverCoordinates
open KroneckerCanonicalKroneckerModuli KroneckerAbelianCover
open KroneckerFiniteSupportDeckRepresentationTransport

def quiver (m : ℕ) : TypedQuiver := ⟨Fin 2,Fin m,source m,target m⟩
def opposite (m : ℕ) : TypedQuiver := ⟨Fin 2,Fin m,target m,source m⟩
instance quiverVertices (m : ℕ) : Fintype (quiver m).V := inferInstanceAs (Fintype (Fin 2))
instance quiverArrows (m : ℕ) : Fintype (quiver m).A := inferInstanceAs (Fintype (Fin m))
instance oppositeVertices (m : ℕ) : Fintype (opposite m).V := inferInstanceAs (Fintype (Fin 2))
instance oppositeArrows (m : ℕ) : Fintype (opposite m).A := inferInstanceAs (Fintype (Fin m))

def exchange (m : ℕ) : TypedQuiverIso (opposite m) (quiver m) where
  vertexEquiv := (Equiv.swap (α := Fin 2) 0 1)
  arrowEquiv := Equiv.refl _
  map_source _ := (Equiv.swap_apply_right (0 : Fin 2) 1).symm
  map_target _ := (Equiv.swap_apply_left (0 : Fin 2) 1).symm

theorem dimension_exchange (m a b : ℕ) (v : Fin 2) :
    dimension b a ((exchange m).vertexEquiv v)=dimension a b v := by
  change dimension b a (Equiv.swap (0 : Fin 2) 1 v)=dimension a b v
  fin_cases v <;> norm_num [dimension,Equiv.swap_apply_def]

theorem character_exchange (m a b : ℕ) (v : Fin 2) :
    character b a ((exchange m).vertexEquiv v)= -character a b v := by
  change character b a (Equiv.swap (0 : Fin 2) 1 v)= -character a b v
  fin_cases v <;> norm_num [character,Equiv.swap_apply_def]
end KroneckerExchangeQuiverCoordinates
end
end

/- Original module: KroneckerOppositeGaugeAction -/
section
/-! Equivariance of actual arrow reversal under the represented product-GL
action.  No quotient or numerical-stability assertion is assumed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open KroneckerRingQuiverFamilies
variable {V A : Type} {s t : A → V} {d : V → ℕ}
  {R : Type} [CommRing R]

theorem oppositeFamily_gauge (g : Gauge d R) (M : Family s t d R) :
    oppositeFamily (gauge s t d g M) =
      gauge t s d (oppositeGaugeEquiv d R g) (oppositeFamily M) := by
  funext a
  simp [oppositeFamily, KroneckerRingQuiverFamilies.gauge, oppositeGaugeEquiv, contragredient,
    Matrix.transpose_mul, Matrix.mul_assoc]

/-- The reverse equivariance equation retains the same actual gauge witness. -/
theorem gauge_oppositeFamily (g : Gauge d R) (M : Family s t d R) :
    gauge t s d g (oppositeFamily M) =
      oppositeFamily (gauge s t d (oppositeGaugeEquiv d R g) M) := by
  rw [oppositeFamily_gauge, oppositeGauge_involutive]

end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerOppositeGaugeOrbits -/
section
/-! Actual gauge orbit and stabilizer correspondences under arrow duality. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open KroneckerRingQuiverFamilies
variable {V A : Type} {s t : A → V} {d : V → ℕ}
  {R : Type} [CommRing R]

theorem opposite_gauge_eq_iff (g : Gauge d R) (M N : Family s t d R) :
    gauge t s d (oppositeGaugeEquiv d R g) (oppositeFamily M) =
      oppositeFamily N ↔ gauge s t d g M = N := by
  rw [← oppositeFamily_gauge]
  exact (oppositeFamilyEquiv (s := s) (t := t) (d := d) R).injective.eq_iff

/-- Every actual gauge witness transports in both directions. -/
theorem opposite_gauge_orbit_iff (M N : Family s t d R) :
    (∃ g : Gauge d R, gauge t s d g (oppositeFamily M) = oppositeFamily N) ↔
      ∃ g : Gauge d R, gauge s t d g M = N := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨oppositeGaugeEquiv d R g, ?_⟩
    apply (opposite_gauge_eq_iff _ M N).mp
    simpa only [oppositeGauge_involutive] using hg
  · rintro ⟨g, hg⟩
    exact ⟨oppositeGaugeEquiv d R g, (opposite_gauge_eq_iff g M N).mpr hg⟩


end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerOppositeFamilyHomeomorphism -/
section
/-! Algebraic arrow transposition is continuous for the actual complex matrix
product topologies, hence defines a homeomorphism of parameter spaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeFamilyHomeomorphism
open KroneckerRingQuiverFamilies KroneckerOppositeArrowFamilies
variable {V A : Type} [Fintype V] [Fintype A]
  (s t : A → V) (d : V → ℕ)

theorem continuous_opposite : Continuous (@oppositeFamily V A s t d ℂ) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp ((continuous_apply j).comp (continuous_apply a))

def homeomorph : Family s t d ℂ ≃ₜ Family t s d ℂ where
  toEquiv := (oppositeFamilyEquiv ℂ).toEquiv
  continuous_toFun := continuous_opposite s t d
  continuous_invFun := continuous_opposite t s d
end KroneckerOppositeFamilyHomeomorphism
end
end

/- Original module: KroneckerOppositeKingStability -/
section
/-! Full numerical King stability is invariant under algebraic quiver duality
with the determinant-character sign reversed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeArrowFamilies
open KroneckerRingQuiverFamilies KroneckerMatrixKingDictionary
open scoped BigOperators
variable {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
  {M : Family s t d ℂ} {θ : V → ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem kingStable_opposite (hM : KingStable θ M) :
    KingStable (fun v => -θ v) (oppositeFamily M) := by
  refine ⟨by simpa [neg_mul, Finset.sum_neg_distrib] using hM.1, ?_⟩
  intro U hn hp
  have hb := (annihilatorSubrep_proper_nonzero_iff U).mpr ⟨hn,hp⟩
  have hw := hM.2 (annihilatorSubrep U) hb.1 hb.2
  have he := annihilatorSubrep_opposite_weight θ hM.1 (annihilatorSubrep U)
  rw [annihilatorSubrep_involutive] at he
  rw [he]
  exact hw

theorem kingStable_opposite_iff :
    KingStable (fun v => -θ v) (oppositeFamily M) ↔ KingStable θ M := by
  constructor
  · intro h
    have hh := kingStable_opposite h
    simpa only [neg_neg, oppositeFamily_opposite] using hh
  · exact kingStable_opposite

end KroneckerOppositeArrowFamilies
end
end

/- Original module: KroneckerOppositeStableHomeomorphism -/
section
/-! The actual internal stable loci are homeomorphic under arrow duality,
with the character sign reversed using all subrepresentations. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeStableHomeomorphism
open KroneckerRingQuiverFamilies KroneckerOppositeArrowFamilies KroneckerFiniteQuiverHom
open KroneckerStableOrbitEuler KroneckerMatrixKingDictionary
variable {V A : Type} [Fintype V] [Fintype A]
  (s t : A → V) (d : V → ℕ) (θ : V → ℤ)

theorem stable_iff (M : Family s t d ℂ) :
    Stable θ (toRepresentation s t d M) ↔
      Stable (fun v => -θ v) (toRepresentation t s d (oppositeFamily M)) := by
  have h := @kingStable_opposite_iff V A _ s t d M (fun v => -θ v)
  simp only [neg_neg,kingStable_iff_internal] at h
  simpa only [neg_neg] using h.symm

def homeomorph : StableFamily s t d θ ≃ₜ StableFamily t s d (fun v => -θ v) :=
  (KroneckerOppositeFamilyHomeomorphism.homeomorph s t d).subtype (stable_iff s t d θ)
end KroneckerOppositeStableHomeomorphism
end
end

/- Original module: KroneckerOppositeOrbitHomeomorphism -/
section
/-! Arrow duality descends to a genuine homeomorphism of canonical stable
orbit spaces, giving homology and ordinary Euler invariance. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerOppositeOrbitHomeomorphism
open KroneckerRingQuiverFamilies KroneckerOppositeArrowFamilies KroneckerStableOrbitEuler
open KroneckerCanonicalStableOrbit KroneckerOrdinarySingularEuler
variable {V A : Type} [Fintype V] [Fintype A]
  (s t : A → V) (d : V → ℕ) (θ : V → ℤ)

def homeomorph : space s t d θ ≃ₜ space t s d (fun v => -θ v) :=
  KroneckerQuotientHomeomorphism.descend (orbitSetoid s t d θ)
    (orbitSetoid t s d (fun v => -θ v))
    (KroneckerOppositeStableHomeomorphism.homeomorph s t d θ)
    (fun M N => (opposite_gauge_orbit_iff M.val N.val).symm)

theorem euler_eq (h : Admissible (space s t d θ))
    (h' : Admissible (space t s d (fun v => -θ v))) :
    ordinaryEuler (space s t d θ) h=ordinaryEuler (space t s d (fun v => -θ v)) h' :=
  KroneckerHomologyHomeomorphism.euler_eq (homeomorph s t d θ) h h'
end KroneckerOppositeOrbitHomeomorphism
end
end

/- Original module: KroneckerExchangeOrbitHomeomorphism -/
section
/-! A concrete homeomorphism of the canonical m-Kronecker stable moduli under
source/sink dimension exchange. This closes the exchange-topology part of R01,
not the separate sink-reflection or King analytification gates. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeOrbitHomeomorphism
open KroneckerCanonicalKroneckerModuli KroneckerExchangeQuiverCoordinates

def homeomorph (m a b : ℕ) : space m a b ≃ₜ space m b a := by
  let e : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm (dimension b a)
  have he : ∀ v,e ((exchange m).vertexEquiv v)=dimension a b v := dimension_exchange m a b
  have H := KroneckerStableOrbitHomeomorphism.orbitHomeomorph (exchange m) (dimension a b) e he
    (character b a)
  have hw : (fun v => character b a ((exchange m).vertexEquiv v))=(fun v => -character a b v) :=
    funext (character_exchange m a b)
  rw [hw] at H
  exact (KroneckerOppositeOrbitHomeomorphism.homeomorph (source m) (target m) (dimension a b)
    (character a b)).trans H.symm
end KroneckerExchangeOrbitHomeomorphism
end
end
