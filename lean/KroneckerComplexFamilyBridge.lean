import KroneckerRingQuiverFamilies
import KroneckerFiniteQuiverStableIso
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
namespace KroneckerRingQuiverFamilies
variable {V A : Type} (s t : A → V) (d : V → ℕ)

noncomputable def toRepresentation (M : Family s t d ℂ) :
    KroneckerFiniteQuiverHom.Representation s t d where
  arrow a := Matrix.toLin' (M a)

noncomputable def ofRepresentation (M : KroneckerFiniteQuiverHom.Representation s t d) :
    Family s t d ℂ := fun a => LinearMap.toMatrix' (M.arrow a)

/-- The algebraic arrow coordinates parameterize exactly the representations
already used by the internal King-stability and Tits-one uniqueness proofs. -/
noncomputable def complexRepresentationEquiv : Family s t d ℂ ≃
    KroneckerFiniteQuiverHom.Representation s t d where
  toFun := toRepresentation s t d
  invFun := ofRepresentation s t d
  left_inv M := by funext a; simp [ofRepresentation, toRepresentation]
  right_inv M := by cases M; simp [ofRepresentation, toRepresentation]

noncomputable def gaugeLinearEquiv (g : Gauge d ℂ) (v : V) :
    KroneckerFiniteQuiverHom.Space (d v) ≃ₗ[ℂ] KroneckerFiniteQuiverHom.Space (d v) :=
  Matrix.toLin'OfInv (g v).inv_val (g v).val_inv

/-- A genuine product-GL change of arrow matrices yields the existing same-label
representation isomorphism, not merely equality of dimension vectors. -/
noncomputable def gaugeIso (g : Gauge d ℂ) (M : Family s t d ℂ) :
    KroneckerFiniteQuiverHom.Iso (toRepresentation s t d M)
      (toRepresentation s t d (gauge s t d g M)) where
  map := gaugeLinearEquiv d g
  commutes := by
    intro a x
    change Matrix.toLin' (↑(g (t a))) (Matrix.toLin' (M a) x) =
      Matrix.toLin' (gauge s t d g M a) (Matrix.toLin' (↑(g (s a))) x)
    rw [← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply]
    congr 2
    exact (gauge_eq_iff s t d g M _).mp rfl a

noncomputable def isoGauge {M N : Family s t d ℂ}
    (e : KroneckerFiniteQuiverHom.Iso (toRepresentation s t d M)
      (toRepresentation s t d N)) : Gauge d ℂ := fun v =>
  { val := LinearMap.toMatrix' (e.map v).toLinearMap
    inv := LinearMap.toMatrix' (e.map v).symm.toLinearMap
    val_inv := by
      rw [← LinearMap.toMatrix'_comp]
      simp
    inv_val := by
      rw [← LinearMap.toMatrix'_comp]
      simp }

theorem isoGauge_action {M N : Family s t d ℂ}
    (e : KroneckerFiniteQuiverHom.Iso (toRepresentation s t d M)
      (toRepresentation s t d N)) :
    gauge s t d (isoGauge s t d e) M = N := by
  apply (gauge_eq_iff s t d _ _ _).mpr
  intro a
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  apply LinearMap.ext
  intro x
  simpa [isoGauge, toRepresentation] using e.commutes a x

/-- The matrix-GL orbit dictionary is two-way for the exact old representation
isomorphism notion. This does not assert a scheme quotient or an Euler identity. -/
theorem complex_orbit_iff_iso (M N : Family s t d ℂ) :
    (∃ g : Gauge d ℂ, gauge s t d g M = N) ↔
      Nonempty (KroneckerFiniteQuiverHom.Iso (toRepresentation s t d M)
        (toRepresentation s t d N)) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨gaugeIso s t d g M⟩
  · rintro ⟨e⟩
    exact ⟨isoGauge s t d e, isoGauge_action s t d e⟩

/-- Positive Euler and internal King stability put the actual complex stable
families in one GL orbit. This is still a statement about complex points. -/
theorem positive_euler_stable_gauge [Fintype V] [Fintype A]
    (M N : Family s t d ℂ) (θ : V → ℤ)
    (hM : KroneckerFiniteQuiverHom.Stable θ (toRepresentation s t d M))
    (hN : KroneckerFiniteQuiverHom.Stable θ (toRepresentation s t d N))
    (he : (∑ a, d (s a) * d (t a)) < ∑ v, d v * d v) :
    ∃ g : Gauge d ℂ, gauge s t d g M = N :=
  (complex_orbit_iff_iso s t d M N).mpr
    (KroneckerFiniteQuiverHom.positive_euler_stable_iso _ _ hM hN he)

end KroneckerRingQuiverFamilies
