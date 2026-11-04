import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push

section

/- Included in the Lean 4.35 migration checkpoint.
   Saved compiler provenance: audit/lean435-migration-20261031/VERIFICATION.md. -/
set_option autoImplicit false
namespace KroneckerFiniteQuiverHom
open Module
open scoped BigOperators

abbrev Space (n : ℕ) := Fin n → ℂ

structure Representation {V A : Type} (s t : A → V) (d : V → ℕ) where
  arrow : ∀ a, Space (d (s a)) →ₗ[ℂ] Space (d (t a))

abbrev VertexHom {V : Type} (d : V → ℕ) := ∀ v, Space (d v) →ₗ[ℂ] Space (d v)
abbrev ArrowHom {V A : Type} (s t : A → V) (d : V → ℕ) :=
  ∀ a, Space (d (s a)) →ₗ[ℂ] Space (d (t a))

/-- Its kernel is precisely the space of representation morphisms R → S. -/
def commutation {V A : Type} {s t : A → V} {d : V → ℕ}
    (R S : Representation s t d) : VertexHom d →ₗ[ℂ] ArrowHom s t d where
  toFun f a := (f (t a)).comp (R.arrow a) - (S.arrow a).comp (f (s a))
  map_add' := by
    intro f g
    funext a
    ext x
    simp [LinearMap.comp_apply, sub_eq_add_neg]
    abel
  map_smul' := by
    intro c f
    funext a
    ext x
    simp [LinearMap.comp_apply, smul_sub]

theorem commutation_zero_iff {V A : Type} {s t : A → V} {d : V → ℕ}
    (R S : Representation s t d) (f : VertexHom d) :
    commutation R S f = 0 ↔ ∀ a x, f (t a) (R.arrow a x) = S.arrow a (f (s a) x) := by
  constructor
  · intro h a x
    have hx := congrArg (fun g : ArrowHom s t d => g a x) h
    simpa [commutation, LinearMap.comp_apply, sub_eq_zero] using hx
  · intro h
    funext a
    ext x
    simp [commutation, LinearMap.comp_apply, h]

structure Morphism {V A : Type} {s t : A → V} {d : V → ℕ}
    (R S : Representation s t d) where
  map : VertexHom d
  commutes : ∀ a x, map (t a) (R.arrow a x) = S.arrow a (map (s a) x)

structure Subrep {V A : Type} {s t : A → V} {d : V → ℕ}
    (R : Representation s t d) where
  space : ∀ v, Submodule ℂ (Space (d v))
  invariant : ∀ a x, x ∈ space (s a) → R.arrow a x ∈ space (t a)

noncomputable def kernelSubrep {V A : Type} {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (f : Morphism R S) : Subrep R where
  space v := LinearMap.ker (f.map v)
  invariant := by
    intro a x hx
    change f.map (t a) (R.arrow a x) = 0
    rw [f.commutes, LinearMap.mem_ker.mp hx, map_zero]

noncomputable def rangeSubrep {V A : Type} {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (f : Morphism R S) : Subrep S where
  space v := LinearMap.range (f.map v)
  invariant := by
    intro a x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨R.arrow a y, f.commutes a y⟩

theorem vertex_rank_nullity {V A : Type} {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (f : Morphism R S) (v : V) :
    finrank ℂ ((rangeSubrep f).space v) + finrank ℂ ((kernelSubrep f).space v) = d v := by
  change finrank ℂ (LinearMap.range (f.map v)) +
    finrank ℂ (LinearMap.ker (f.map v)) = d v
  calc
    _ = finrank ℂ (Space (d v)) := (f.map v).finrank_range_add_finrank_ker
    _ = d v := by simp [Space]

theorem vertexHom_dimension {V : Type} [Fintype V] (d : V → ℕ) :
    finrank ℂ (VertexHom d) = ∑ v, d v * d v := by
  simp [VertexHom, Space, Module.finrank_pi_fintype, Module.finrank_linearMap]

theorem arrowHom_dimension {V A : Type} [Fintype A] (s t : A → V) (d : V → ℕ) :
    finrank ℂ (ArrowHom s t d) = ∑ a, d (s a) * d (t a) := by
  simp [ArrowHom, Space, Module.finrank_pi_fintype, Module.finrank_linearMap]

/-- No geometric assertion is used: more unknowns than commutation equations
forces a nonzero solution. The inequality is the positive self Euler form. -/
theorem positive_euler_nonzero_morphism {V A : Type} [Fintype V] [Fintype A]
    {s t : A → V} {d : V → ℕ} (R S : Representation s t d)
    (h : (∑ a, d (s a) * d (t a)) < ∑ v, d v * d v) :
    ∃ f : Morphism R S, f.map ≠ 0 := by
  classical
  have hn : ¬ Function.Injective (commutation R S) := by
    intro hi
    have hd := LinearMap.finrank_le_finrank_of_injective hi
    rw [vertexHom_dimension, arrowHom_dimension] at hd
    omega
  have hk : LinearMap.ker (commutation R S) ≠ ⊥ := by
    intro hk
    exact hn (LinearMap.ker_eq_bot.mp hk)
  have hex : ∃ f ∈ LinearMap.ker (commutation R S), f ≠ 0 := by
    by_contra he
    push Not at he
    apply hk
    apply le_antisymm
    · intro f hf
      exact he f hf
    · exact bot_le
  obtain ⟨f, hf, hne⟩ := hex
  exact ⟨⟨f, (commutation_zero_iff R S f).mp (LinearMap.mem_ker.mp hf)⟩, hne⟩

end KroneckerFiniteQuiverHom
end

section

/- Included in the Lean 4.35 migration checkpoint.
   Saved compiler provenance: audit/lean435-migration-20261031/VERIFICATION.md. -/
set_option autoImplicit false
namespace KroneckerFiniteQuiverHom
open Module
open scoped BigOperators

noncomputable def size {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R : Representation s t d} (U : Subrep R) : ℕ := ∑ v, finrank ℂ (U.space v)

noncomputable def weight {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R : Representation s t d} (θ : V → ℤ) (U : Subrep R) : ℤ :=
  ∑ v, θ v * (finrank ℂ (U.space v) : ℤ)

/-- The weight is the negative of King's stability parameter: every nonzero proper
subrepresentation has negative weight. The full representation has weight zero. -/
def Stable {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    (θ : V → ℤ) (R : Representation s t d) : Prop :=
  (∑ v, θ v * (d v : ℤ)) = 0 ∧
    ∀ U : Subrep R, 0 < size U → size U < ∑ v, d v → weight θ U < 0


theorem size_eq_zero_iff {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R : Representation s t d} (U : Subrep R) : size U = 0 ↔ ∀ v, U.space v = ⊥ := by
  constructor
  · intro h v
    have hv : finrank ℂ (U.space v) ≤ size U :=
      Finset.single_le_sum (f := fun w => finrank ℂ (U.space w))
        (fun w _ => Nat.zero_le _) (Finset.mem_univ v)
    apply Submodule.finrank_eq_zero.mp
    omega
  · intro h
    simp [size, h]

theorem size_rank_nullity {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (f : Morphism R S) :
    size (rangeSubrep f) + size (kernelSubrep f) = ∑ v, d v := by
  rw [size, size, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => vertex_rank_nullity f v)

theorem weight_rank_nullity {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (θ : V → ℤ) (f : Morphism R S) :
    weight θ (rangeSubrep f) + weight θ (kernelSubrep f) = ∑ v, θ v * (d v : ℤ) := by
  rw [weight, weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hv : (finrank ℂ ((rangeSubrep f).space v) : ℤ) +
      (finrank ℂ ((kernelSubrep f).space v) : ℤ) = (d v : ℤ) := by
    exact_mod_cast vertex_rank_nullity f v
  rw [← mul_add, hv]

theorem nonzero_range_size {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (f : Morphism R S) (hne : f.map ≠ 0) :
    0 < size (rangeSubrep f) := by
  by_contra hn
  have hz : size (rangeSubrep f) = 0 := by omega
  have hbot := (size_eq_zero_iff (rangeSubrep f)).mp hz
  apply hne
  funext v
  apply LinearMap.ext
  intro x
  have hx : f.map v x ∈ (rangeSubrep f).space v := ⟨x, rfl⟩
  rw [hbot v] at hx
  exact hx

/-- Stability excludes simultaneous nonzero proper kernel and image. -/
theorem stable_nonzero_kernel_zero {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} {θ : V → ℤ} (hR : Stable θ R) (hS : Stable θ S)
    (f : Morphism R S) (hne : f.map ≠ 0) : size (kernelSubrep f) = 0 := by
  have hr := nonzero_range_size f hne
  have hdim := size_rank_nullity f
  by_contra hker
  have hk : 0 < size (kernelSubrep f) := by omega
  have hkproper : size (kernelSubrep f) < ∑ v, d v := by omega
  have hrproper : size (rangeSubrep f) < ∑ v, d v := by omega
  have hkw := hR.2 (kernelSubrep f) hk hkproper
  have hrw := hS.2 (rangeSubrep f) hr hrproper
  have hw := weight_rank_nullity θ f
  rw [hR.1] at hw
  omega

theorem stable_nonzero_vertex_bijective {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} {θ : V → ℤ} (hR : Stable θ R) (hS : Stable θ S)
    (f : Morphism R S) (hne : f.map ≠ 0) : ∀ v, Function.Bijective (f.map v) := by
  have hk := (size_eq_zero_iff (kernelSubrep f)).mp (stable_nonzero_kernel_zero hR hS f hne)
  intro v
  have hi : Function.Injective (f.map v) := LinearMap.ker_eq_bot.mp (hk v)
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

structure Iso {V A : Type} {s t : A → V} {d : V → ℕ}
    (R S : Representation s t d) where
  map : ∀ v, Space (d v) ≃ₗ[ℂ] Space (d v)
  commutes : ∀ a x, map (t a) (R.arrow a x) = S.arrow a (map (s a) x)

/-- The chosen vertexwise inverses commute with every arrow as well. -/
noncomputable def Iso.symm {V A : Type} {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} (e : Iso R S) : Iso S R where
  map v := (e.map v).symm
  commutes := by
    intro a x
    apply (e.map (t a)).injective
    simpa using (e.commutes a ((e.map (s a)).symm x)).symm

noncomputable def stableIso {V A : Type} [Fintype V] {s t : A → V} {d : V → ℕ}
    {R S : Representation s t d} {θ : V → ℤ} (hR : Stable θ R) (hS : Stable θ S)
    (f : Morphism R S) (hne : f.map ≠ 0) : Iso R S where
  map v := LinearEquiv.ofBijective (f.map v) (stable_nonzero_vertex_bijective hR hS f hne v)
  commutes := f.commutes

/-- Positive self Euler form plus stability proves uniqueness of the stable
isomorphism class for these finite coordinate representations. This statement
does NOT construct an algebraic moduli space or compute an Euler characteristic. -/
theorem positive_euler_stable_iso {V A : Type} [Fintype V] [Fintype A]
    {s t : A → V} {d : V → ℕ} {θ : V → ℤ} (R S : Representation s t d)
    (hR : Stable θ R) (hS : Stable θ S)
    (h : (∑ a, d (s a) * d (t a)) < ∑ v, d v * d v) : Nonempty (Iso R S) := by
  obtain ⟨f, hf⟩ := positive_euler_nonzero_morphism R S h
  exact ⟨stableIso hR hS f hf⟩

end KroneckerFiniteQuiverHom
end

