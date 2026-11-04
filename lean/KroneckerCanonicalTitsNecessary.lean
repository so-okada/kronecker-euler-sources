import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import KroneckerCanonicalKroneckerModuli

/- Original module: KroneckerStableSchur -/
section
set_option autoImplicit false
namespace KroneckerFiniteQuiverHom
open Module
open scoped BigOperators

/-- Subtracting the same scalar at every vertex preserves commutation. -/
noncomputable def subtractScalar {V A : Type} {s t : A → V} {d : V → ℕ}
    {R : Representation s t d} (f : Morphism R R) (c : ℂ) : Morphism R R where
  map v := f.map v - c • LinearMap.id
  commutes := by
    intro a x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_sub, map_smul, f.commutes]

/-- At a nonzero vertex, a stable endomorphism has an eigenvalue; the global
scalar subtraction cannot be invertible, hence is zero at every vertex. -/
theorem stable_endomorphism_scalar {V A : Type} [Fintype V]
    {s t : A → V} {d : V → ℕ} {θ : V → ℤ} {R : Representation s t d}
    (hR : Stable θ R) (hv : ∃ v, 0 < d v) (f : Morphism R R) :
    ∃ c : ℂ, ∀ v, f.map v = c • LinearMap.id := by
  classical
  obtain ⟨v, hv⟩ := hv
  let : Nonempty (Fin (d v)) := ⟨⟨0,hv⟩⟩
  obtain ⟨c,hc⟩ := Module.End.exists_eigenvalue (f.map v)
  obtain ⟨x,hx⟩ := hc.exists_hasEigenvector
  have hz : (subtractScalar f c).map = 0 := by
    by_contra hn
    have hi := (stable_nonzero_vertex_bijective hR hR (subtractScalar f c) hn v).1
    have he : (subtractScalar f c).map v x = (subtractScalar f c).map v 0 := by
      simp [subtractScalar, hx.apply_eq_smul]
    exact hx.2 (hi he)
  refine ⟨c,fun w => ?_⟩
  have hw := congrFun hz w
  exact sub_eq_zero.mp hw

/-- The identity family is nonzero exactly when a vertex space is nonzero. -/
theorem identity_family_ne_zero {V : Type} {d : V → ℕ}
    (hv : ∃ v, 0 < d v) : (fun v => (LinearMap.id : Space (d v) →ₗ[ℂ] Space (d v))) ≠ 0 := by
  obtain ⟨v,hv⟩ := hv
  intro hz
  have h := congrArg (fun f : VertexHom d => f v (fun _ => 1) ⟨0,hv⟩) hz
  simp at h

/-- Stable endomorphisms are precisely the scalar identity families. -/
theorem stable_endomorphism_kernel_scalar {V A : Type} [Fintype V]
    {s t : A → V} {d : V → ℕ} {θ : V → ℤ} {R : Representation s t d}
    (hR : Stable θ R) (hv : ∃ v, 0 < d v) (f : VertexHom d) :
    f ∈ LinearMap.ker (commutation R R) ↔
      ∃ c : ℂ, f = c • (fun v => (LinearMap.id : Space (d v) →ₗ[ℂ] Space (d v))) := by
  constructor
  · intro hf
    obtain ⟨c,hc⟩ := stable_endomorphism_scalar hR hv
      (⟨f,(commutation_zero_iff R R f).mp hf⟩ : Morphism R R)
    exact ⟨c,funext hc⟩
  · rintro ⟨c,rfl⟩
    apply (commutation_zero_iff R R _).mpr
    intro a x
    simp

end KroneckerFiniteQuiverHom
end

/- Original module: KroneckerStableEndomorphismDimension -/
section
set_option autoImplicit false
namespace KroneckerFiniteQuiverHom
open Module
open scoped BigOperators

/-- Identity as an element of the actual commutation kernel. -/
noncomputable def identityEndomorphism {V A : Type} {s t : A → V} {d : V → ℕ}
    (R : Representation s t d) : LinearMap.ker (commutation R R) :=
  ⟨fun _ => LinearMap.id, (commutation_zero_iff R R _).mpr (by intros; rfl)⟩

/-- The full endomorphism kernel, not a coordinate-only subspace, has dimension one. -/
theorem stable_endomorphism_finrank {V A : Type} [Fintype V]
    {s t : A → V} {d : V → ℕ} {θ : V → ℤ} {R : Representation s t d}
    (hR : Stable θ R) (hv : ∃ v, 0 < d v) :
    finrank ℂ (LinearMap.ker (commutation R R)) = 1 := by
  have hn : identityEndomorphism R ≠ 0 := by
    intro h
    exact identity_family_ne_zero hv (congrArg Subtype.val h)
  apply (finrank_eq_one_iff_of_nonzero' (identityEndomorphism R) hn).mpr
  intro f
  obtain ⟨c,hc⟩ := (stable_endomorphism_kernel_scalar hR hv f.val).mp f.property
  exact ⟨c,Subtype.ext hc.symm⟩

/-- For a nonzero stable complex representation, self Euler form is at most one. -/
theorem stable_euler_le_one {V A : Type} [Fintype V] [Fintype A]
    {s t : A → V} {d : V → ℕ} {θ : V → ℤ} {R : Representation s t d}
    (hR : Stable θ R) (hv : ∃ v, 0 < d v) :
    (∑ v, d v * d v) ≤ (∑ a, d (s a) * d (t a)) + 1 := by
  have hr := (commutation R R).finrank_range_add_finrank_ker
  have hb := (LinearMap.range (commutation R R)).finrank_le
  rw [stable_endomorphism_finrank hR hv, vertexHom_dimension] at hr
  rw [arrowHom_dimension] at hb
  omega


end KroneckerFiniteQuiverHom
end

/- Original module: KroneckerCanonicalTitsNecessary -/
section
/-! The arithmetic Tits inequality is necessary for actual canonical moduli
nonemptiness. This proves one direction of the manuscript nonempty-domain gate. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalTitsNecessary
open KroneckerCanonicalKroneckerModuli KroneckerFiniteQuiverHom
open scoped BigOperators

theorem tits_le_one (m a b : ℕ) (ha : 0<a) (hn : Nonempty (space m a b)) :
    (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b≤1 := by
  obtain ⟨R,hR⟩ := (space_nonempty_iff m a b).mp hn
  have H := stable_euler_le_one hR (show ∃ v,0<dimension a b v from ⟨0,ha⟩)
  have HH : a*a+b*b≤m*(a*b)+1 := by
    simpa [Fin.sum_univ_two,dimension,source,target] using H
  have HI : (a : ℤ)*a+(b : ℤ)*b≤(m : ℤ)*(a*b)+1 := by exact_mod_cast HH
  nlinarith
end KroneckerCanonicalTitsNecessary
end
end
