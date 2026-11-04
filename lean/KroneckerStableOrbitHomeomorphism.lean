import KroneckerArrowParameterAlgebra
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Group.Units.Equiv
import KroneckerCanonicalStableOrbit
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import KroneckerFiniteQuiverPullbackStability
import KroneckerQuiverPullbackComposition
import KroneckerQuotientHomeomorphism

/- Original module: KroneckerWeightedQuiverCoordinateEquivalence -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedQuiverCoordinateEquivalence
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerArrowParameterAlgebra
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)

def vertexIndex (v : P.V) : Fin (d v) ≃ Fin (e (f.vertexEquiv v)) :=
  finCongr (h v).symm

def sourceIndex (a : P.A) : Fin (d (P.source a)) ≃ Fin (e (Q.source (f.arrowEquiv a))) :=
  finCongr (by rw [f.map_source, h])

def targetIndex (a : P.A) : Fin (d (P.target a)) ≃ Fin (e (Q.target (f.arrowEquiv a))) :=
  finCongr (by rw [f.map_target, h])

/-- The variables are actual arrow entries, including the endpoint dimension casts. -/
def coordinateEquiv : Coordinate P.source P.target d ≃ Coordinate Q.source Q.target e :=
  Equiv.sigmaCongr f.arrowEquiv fun a =>
    Equiv.prodCongr (targetIndex f d e h a) (sourceIndex f d e h a)

theorem coordinateEquiv_entry (a : P.A) (i : Fin (d (P.target a)))
    (j : Fin (d (P.source a))) :
    coordinateEquiv f d e h ⟨a,i,j⟩ =
      ⟨f.arrowEquiv a,targetIndex f d e h a i,sourceIndex f d e h a j⟩ := rfl

theorem coordinateEquiv_bijective : Function.Bijective (coordinateEquiv f d e h) :=
  (coordinateEquiv f d e h).bijective
end KroneckerWeightedQuiverCoordinateEquivalence
end
end

/- Original module: KroneckerWeightedQuiverFamilyEquivalence -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedQuiverFamilyEquivalence
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)

/-- Pullback of every matrix over an arbitrary coefficient type. -/
def familyEquiv (R : Type) : Family Q.source Q.target e R ≃ Family P.source P.target d R :=
  (Equiv.piCongr f.arrowEquiv fun a =>
    Matrix.reindex (targetIndex f d e h a) (sourceIndex f d e h a)).symm

theorem familyEquiv_entry {R : Type} (M : Family Q.source Q.target e R) (a i j) :
    familyEquiv f d e h R M a i j =
      M (f.arrowEquiv a) (targetIndex f d e h a i) (sourceIndex f d e h a j) := rfl

/-- Naturality includes maps between nonreduced commutative base rings. -/
theorem familyEquiv_natural {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Family Q.source Q.target e R) :
    familyEquiv f d e h S (changeRing Q.source Q.target e φ M) =
      changeRing P.source P.target d φ (familyEquiv f d e h R M) := rfl

theorem familyEquiv_symm_natural {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Family P.source P.target d R) :
    (familyEquiv f d e h S).symm (changeRing P.source P.target d φ M) =
      changeRing Q.source Q.target e φ ((familyEquiv f d e h R).symm M) := by
  apply (familyEquiv f d e h S).injective
  rw [Equiv.apply_symm_apply, familyEquiv_natural, Equiv.apply_symm_apply]
end KroneckerWeightedQuiverFamilyEquivalence
end
end

/- Original module: KroneckerWeightedVertexMatrixEquivalence -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedVertexMatrixEquivalence
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)
  (R : Type) [CommRing R]

def vertexEquiv : VertexMap e R ≃ VertexMap d R :=
  (Equiv.piCongr f.vertexEquiv fun v =>
    (Matrix.reindexAlgEquiv R R (vertexIndex f d e h v)).toEquiv).symm

def vertexRingEquiv : VertexMap e R ≃+* VertexMap d R :=
  { vertexEquiv f d e h R with
    map_add' := by intro M N; funext v; exact map_add (Matrix.reindexAlgEquiv R R (vertexIndex f d e h v).symm) _ _
    map_mul' := by intro M N; funext v; exact map_mul (Matrix.reindexAlgEquiv R R (vertexIndex f d e h v).symm) _ _ }

theorem vertexRingEquiv_entry (M : VertexMap e R) (v i j) :
    vertexRingEquiv f d e h R M v i j =
      M (f.vertexEquiv v) (vertexIndex f d e h v i) (vertexIndex f d e h v j) := rfl

theorem vertexRingEquiv_natural {S : Type} [CommRing S] (φ : R →+* S) (M : VertexMap e R) :
    vertexRingEquiv f d e h S (fun v => (M v).map φ) =
      fun v => ((vertexRingEquiv f d e h R M) v).map φ := rfl
end KroneckerWeightedVertexMatrixEquivalence
end
end

/- Original module: KroneckerWeightedGaugeGroupEquivalence -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedGaugeGroupEquivalence
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)
  (R : Type) [CommRing R]

def gaugeEquiv : Gauge e R ≃ Gauge d R :=
  (Equiv.piCongr f.vertexEquiv fun v =>
    (Units.mapEquiv (Matrix.reindexAlgEquiv R R (vertexIndex f d e h v)).toMulEquiv).toEquiv).symm

/-- An isomorphism of actual products of general linear groups over every base ring. -/
def gaugeMulEquiv : Gauge e R ≃* Gauge d R :=
  { gaugeEquiv f d e h R with
    map_mul' := by
      intro g l
      funext v
      apply Units.ext
      exact map_mul (Matrix.reindexAlgEquiv R R (vertexIndex f d e h v).symm) _ _ }

theorem gaugeMulEquiv_entry (g : Gauge e R) (v i j) :
    (gaugeMulEquiv f d e h R g v : Matrix _ _ R) i j =
      (g (f.vertexEquiv v) : Matrix _ _ R)
        (vertexIndex f d e h v i) (vertexIndex f d e h v j) := rfl

theorem gaugeMulEquiv_natural {S : Type} [CommRing S] (φ : R →+* S) (g : Gauge e R) :
    gaugeMulEquiv f d e h S (changeGauge e φ g) =
      changeGauge d φ (gaugeMulEquiv f d e h R g) := by
  funext v
  apply Units.ext
  rfl
end KroneckerWeightedGaugeGroupEquivalence
end
end

/- Original module: KroneckerWeightedMatrixEndpointTransport -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedMatrixEndpointTransport
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerWeightedVertexMatrixEquivalence
open KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)
  {R : Type} [CommRing R]

theorem endpoint_matrix {v : P.V} {w : Q.V} (hv : w = f.vertexEquiv v)
    (b : Fin (d v) ≃ Fin (e w)) (hb : ∀ i, (b i).val = i.val)
    (M : VertexMap e R) (i j : Fin (d v)) :
    vertexRingEquiv f d e h R M v i j = M w (b i) (b j) := by
  subst w
  rw [vertexRingEquiv_entry]
  congr 1
  · apply Fin.ext; exact (hb i).symm
  · apply Fin.ext; exact (hb j).symm

theorem source_matrix (M : VertexMap e R) (a i j) :
    vertexRingEquiv f d e h R M (P.source a) i j =
      M (Q.source (f.arrowEquiv a)) (sourceIndex f d e h a i) (sourceIndex f d e h a j) :=
  endpoint_matrix f d e h (f.map_source a) (sourceIndex f d e h a) (fun _ => rfl) M i j

theorem target_matrix (M : VertexMap e R) (a i j) :
    vertexRingEquiv f d e h R M (P.target a) i j =
      M (Q.target (f.arrowEquiv a)) (targetIndex f d e h a i) (targetIndex f d e h a j) :=
  endpoint_matrix f d e h (f.map_target a) (targetIndex f d e h a) (fun _ => rfl) M i j
end KroneckerWeightedMatrixEndpointTransport
end
end

/- Original module: KroneckerWeightedMatrixMultiplicationTransport -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedMatrixMultiplicationTransport
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerWeightedQuiverFamilyEquivalence
open KroneckerWeightedVertexMatrixEquivalence KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)
open KroneckerWeightedMatrixEndpointTransport
variable {R : Type} [CommRing R]

theorem left_multiply (N : VertexMap e R) (M : Family Q.source Q.target e R) :
    familyEquiv f d e h R (fun a => N (Q.target a) * M a) =
      fun a => vertexRingEquiv f d e h R N (P.target a) * familyEquiv f d e h R M a := by
  funext a
  have ht : vertexRingEquiv f d e h R N (P.target a) =
      (N (Q.target (f.arrowEquiv a))).submatrix (targetIndex f d e h a) (targetIndex f d e h a) := by
    funext i j
    exact target_matrix f d e h N a i j
  rw [ht]
  exact (Matrix.submatrix_mul_equiv (N (Q.target (f.arrowEquiv a))) (M (f.arrowEquiv a))
    (targetIndex f d e h a) (targetIndex f d e h a) (sourceIndex f d e h a)).symm

theorem right_multiply (N : VertexMap e R) (M : Family Q.source Q.target e R) :
    familyEquiv f d e h R (fun a => M a * N (Q.source a)) =
      fun a => familyEquiv f d e h R M a * vertexRingEquiv f d e h R N (P.source a) := by
  funext a
  have hs : vertexRingEquiv f d e h R N (P.source a) =
      (N (Q.source (f.arrowEquiv a))).submatrix (sourceIndex f d e h a) (sourceIndex f d e h a) := by
    funext i j
    exact source_matrix f d e h N a i j
  rw [hs]
  exact (Matrix.submatrix_mul_equiv (M (f.arrowEquiv a)) (N (Q.source (f.arrowEquiv a)))
    (targetIndex f d e h a) (sourceIndex f d e h a) (sourceIndex f d e h a)).symm
end KroneckerWeightedMatrixMultiplicationTransport
end
end

/- Original module: KroneckerWeightedCommutationTransport -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedCommutationTransport
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerWeightedQuiverFamilyEquivalence
open KroneckerWeightedVertexMatrixEquivalence KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)
open KroneckerWeightedMatrixMultiplicationTransport
variable {R : Type} [CommRing R]

theorem commutation_transport (M N : Family Q.source Q.target e R) (u : VertexMap e R) :
    familyEquiv f d e h R (commutation Q.source Q.target e M N u) =
      commutation P.source P.target d (familyEquiv f d e h R M)
        (familyEquiv f d e h R N) (vertexRingEquiv f d e h R u) := by
  have hl := left_multiply f d e h u M
  have hr := right_multiply f d e h u N
  funext a i j
  exact congrArg₂ (fun x y : R => x - y)
    (congrFun (congrFun (congrFun hl a) i) j)
    (congrFun (congrFun (congrFun hr a) i) j)

theorem commutation_zero_iff (M N : Family Q.source Q.target e R) (u : VertexMap e R) :
    commutation Q.source Q.target e M N u = 0 ↔
      commutation P.source P.target d (familyEquiv f d e h R M)
        (familyEquiv f d e h R N) (vertexRingEquiv f d e h R u) = 0 := by
  rw [← commutation_transport]
  exact ((familyEquiv f d e h R).injective.eq_iff).symm
end KroneckerWeightedCommutationTransport
end
end

/- Original module: KroneckerWeightedFamilyLinearEquivalence -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedFamilyLinearEquivalence
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverFamilyEquivalence KroneckerWeightedVertexMatrixEquivalence
open KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)
  (R : Type) [CommRing R]

def familyLinearEquiv : Family Q.source Q.target e R ≃ₗ[R] Family P.source P.target d R :=
  { familyEquiv f d e h R with
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def vertexLinearEquiv : VertexMap e R ≃ₗ[R] VertexMap d R :=
  { (vertexRingEquiv f d e h R).toAddEquiv with
    map_smul' := by intros; rfl }

/-- Scalar-linear transport intertwines the full equations, not merely their zero sets. -/
theorem linear_commutation (M N : Family Q.source Q.target e R) (u : VertexMap e R) :
    familyLinearEquiv f d e h R (commutation Q.source Q.target e M N u) =
      commutation P.source P.target d (familyLinearEquiv f d e h R M)
        (familyLinearEquiv f d e h R N) (vertexLinearEquiv f d e h R u) :=
  KroneckerWeightedCommutationTransport.commutation_transport f d e h M N u
end KroneckerWeightedFamilyLinearEquivalence
end
end

/- Original module: KroneckerFamilyCoordinateHomeomorphism -/
section
/-! Matrix-coordinate changes induced by weighted quiver isomorphisms preserve
exactly the product complex topology used in the canonical orbit construction. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFamilyCoordinateHomeomorphism
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerRingQuiverFamilies KroneckerWeightedFamilyLinearEquivalence
variable {P Q : TypedQuiver} [Fintype P.V] [Fintype P.A] [Fintype Q.V] [Fintype Q.A]
  (f : TypedQuiverIso P Q) (d : P.V → ℕ) (e : Q.V → ℕ)
  (h : ∀ v, e (f.vertexEquiv v)=d v)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def familyHomeomorph : Family Q.source Q.target e ℂ ≃ₜ Family P.source P.target d ℂ :=
  (familyLinearEquiv f d e h ℂ).toContinuousLinearEquiv.toHomeomorph

theorem familyHomeomorph_entry (M : Family Q.source Q.target e ℂ) (a i j) :
    familyHomeomorph f d e h M a i j =
      M (f.arrowEquiv a)
        (KroneckerWeightedQuiverCoordinateEquivalence.targetIndex f d e h a i)
        (KroneckerWeightedQuiverCoordinateEquivalence.sourceIndex f d e h a j) := rfl

end KroneckerFamilyCoordinateHomeomorphism
end
end

/- Original module: KroneckerFamilyPullbackRepresentation -/
section
/-! The topological matrix-coordinate change is the same actual representation
pullback already used in the subrepresentation stability proof. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFamilyPullbackRepresentation
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerRingQuiverFamilies KroneckerWeightedQuiverFamilyEquivalence
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerFiniteQuiverHom

private theorem matrix_linear_heq {a b c d : ℕ} (ha : a=c) (hb : b=d)
    (M : Matrix (Fin c) (Fin d) ℂ) :
    HEq (Matrix.toLin' (fun i : Fin a => fun j : Fin b => M (finCongr ha i) (finCongr hb j)))
      (Matrix.toLin' M) := by
  subst c; subst d; rfl

variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q) (e : Q.V →₀ ℕ)

theorem coordinate_pullback (M : Family Q.source Q.target e ℂ) :
    toRepresentation P.source P.target (fun v => e (f.vertexEquiv v))
      (familyEquiv f (fun v => e (f.vertexEquiv v)) e (fun _ => rfl) ℂ M) =
    pullRepresentation f e (toRepresentation Q.source Q.target e M) := by
  apply KroneckerFiniteSupportInducedQuiver.representation_ext
  funext a
  apply eq_of_heq
  apply HEq.trans _ (KroneckerQuiverPullbackComposition.pull_arrow_heq f e
    (toRepresentation Q.source Q.target e M) a).symm
  exact matrix_linear_heq _ _ (M (f.arrowEquiv a))

theorem coordinate_stable_iff [Fintype P.V] [Fintype Q.V]
    (θ : Q.V → ℤ) (M : Family Q.source Q.target e ℂ) :
    Stable (fun v => θ (f.vertexEquiv v))
      (toRepresentation P.source P.target (fun v => e (f.vertexEquiv v))
        (familyEquiv f (fun v => e (f.vertexEquiv v)) e (fun _ => rfl) ℂ M)) ↔
      Stable θ (toRepresentation Q.source Q.target e M) := by
  rw [coordinate_pullback]
  exact KroneckerFiniteQuiverPullbackStability.finite_pull_stable_iff f e θ _

end KroneckerFamilyPullbackRepresentation
end
end

/- Original module: KroneckerStableCoordinateHomeomorphism -/
section
/-! Stable loci have homeomorphic complex subspace topologies under weighted
quiver isomorphisms. Stability is proved by actual subrepresentation pullback. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableCoordinateHomeomorphism
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerRingQuiverFamilies KroneckerStableOrbitEuler KroneckerFiniteQuiverHom
open KroneckerFamilyCoordinateHomeomorphism KroneckerFamilyPullbackRepresentation
variable {P Q : TypedQuiver} [Fintype P.V] [Fintype P.A] [Fintype Q.V] [Fintype Q.A]
  (f : TypedQuiverIso P Q) (d : P.V → ℕ) (e : Q.V →₀ ℕ)
  (h : ∀ v, e (f.vertexEquiv v)=d v) (θ : Q.V → ℤ)

theorem weighted_stable_iff (M : Family Q.source Q.target e ℂ) :
    Stable (fun v => θ (f.vertexEquiv v))
      (toRepresentation P.source P.target d (familyHomeomorph f d e h M)) ↔
    Stable θ (toRepresentation Q.source Q.target e M) := by
  have hd : d=fun v => e (f.vertexEquiv v) := funext (fun v => (h v).symm)
  subst d
  exact coordinate_stable_iff f e θ M

def stableHomeomorph : StableFamily Q.source Q.target e θ ≃ₜ
    StableFamily P.source P.target d (fun v => θ (f.vertexEquiv v)) :=
  (familyHomeomorph f d e h).subtype (fun M => (weighted_stable_iff f d e h θ M).symm)

end KroneckerStableCoordinateHomeomorphism
end
end

/- Original module: KroneckerWeightedGaugeActionTransport -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedGaugeActionTransport
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerWeightedQuiverFamilyEquivalence
open KroneckerWeightedVertexMatrixEquivalence KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)
open KroneckerWeightedGaugeGroupEquivalence KroneckerWeightedMatrixMultiplicationTransport
variable {R : Type} [CommRing R]

theorem gauge_values (g : Gauge e R) :
    (fun v => (gaugeMulEquiv f d e h R g v : Matrix _ _ R)) =
      vertexRingEquiv f d e h R (fun v => (g v : Matrix _ _ R)) := rfl

/-- Actual group actions intertwine on every test ring. -/
theorem gauge_transport (g : Gauge e R) (M : Family Q.source Q.target e R) :
    familyEquiv f d e h R (gauge Q.source Q.target e g M) =
      gauge P.source P.target d (gaugeMulEquiv f d e h R g) (familyEquiv f d e h R M) := by
  change familyEquiv f d e h R (fun a =>
    ((g (Q.target a) : Matrix _ _ R) * M a) * (↑((g (Q.source a))⁻¹) : Matrix _ _ R)) = _
  rw [right_multiply f d e h (R := R) (fun v : Q.V => (↑((g v)⁻¹) : Matrix (Fin (e v)) (Fin (e v)) R))
    (fun a : Q.A => (g (Q.target a) : Matrix (Fin (e (Q.target a))) (Fin (e (Q.target a))) R) * M a),
    left_multiply f d e h (R := R) (fun v : Q.V => (g v : Matrix (Fin (e v)) (Fin (e v)) R)) M]
  have hi := map_inv (gaugeMulEquiv f d e h R) g
  have hv := gauge_values f d e h (R := R) g⁻¹
  rw [hi] at hv
  simp only [Pi.inv_apply] at hv
  rw [← gauge_values f d e h g, ← hv]
  rfl
end KroneckerWeightedGaugeActionTransport
end
end

/- Original module: KroneckerWeightedGaugeOrbitEquivalence -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerWeightedGaugeOrbitEquivalence
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerWeightedQuiverCoordinateEquivalence KroneckerWeightedQuiverFamilyEquivalence
open KroneckerWeightedVertexMatrixEquivalence KroneckerRingQuiverFamilies
variable {P Q : TypedQuiver} (f : TypedQuiverIso P Q)
  (d : P.V → ℕ) (e : Q.V → ℕ) (h : ∀ v, e (f.vertexEquiv v) = d v)
open KroneckerWeightedGaugeGroupEquivalence KroneckerWeightedGaugeActionTransport
variable {R : Type} [CommRing R]

def GaugeRelated (M N : Family Q.source Q.target e R) : Prop :=
  ∃ g : Gauge e R, gauge Q.source Q.target e g M = N

theorem gauge_related_iff (M N : Family Q.source Q.target e R) :
    GaugeRelated e M N ↔ GaugeRelated d (familyEquiv f d e h R M) (familyEquiv f d e h R N) := by
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨gaugeMulEquiv f d e h R g, (gauge_transport f d e h g M).symm.trans (congrArg (familyEquiv f d e h R) hg)⟩
  · rintro ⟨g,hg⟩
    refine ⟨(gaugeMulEquiv f d e h R).symm g, (familyEquiv f d e h R).injective ?_⟩
    rw [gauge_transport, MulEquiv.apply_symm_apply]
    exact hg
end KroneckerWeightedGaugeOrbitEquivalence
end
end

/- Original module: KroneckerStableOrbitHomeomorphism -/
section
/-! The complex quotient topology on stable matrix orbits is independent of
weighted quiver coordinates, with the induced map on actual GL orbit classes. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableOrbitHomeomorphism
open KroneckerAbelianCover KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerRingQuiverFamilies KroneckerStableOrbitEuler
open KroneckerStableCoordinateHomeomorphism
variable {P Q : TypedQuiver} [Fintype P.V] [Fintype P.A] [Fintype Q.V] [Fintype Q.A]
  (f : TypedQuiverIso P Q) (d : P.V → ℕ) (e : Q.V →₀ ℕ)
  (h : ∀ v, e (f.vertexEquiv v)=d v) (θ : Q.V → ℤ)

def orbitHomeomorph : StableOrbit Q.source Q.target e θ ≃ₜ
    StableOrbit P.source P.target d (fun v => θ (f.vertexEquiv v)) :=
  KroneckerQuotientHomeomorphism.descend _ _ (stableHomeomorph f d e h θ)
    (fun M N => KroneckerWeightedGaugeOrbitEquivalence.gauge_related_iff f d e h M.val N.val)

theorem orbitHomeomorph_project (M : StableFamily Q.source Q.target e θ) :
    orbitHomeomorph f d e h θ (Quotient.mk (orbitSetoid Q.source Q.target e θ) M) =
      Quotient.mk (orbitSetoid P.source P.target d (fun v => θ (f.vertexEquiv v)))
        (stableHomeomorph f d e h θ M) := rfl

end KroneckerStableOrbitHomeomorphism
end
end
