import KroneckerComplexFamilyBridge
import KroneckerOrdinarySingularEuler
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Constructions

/- Original module: KroneckerStableOrbitEuler -/
section
/-! The actual complex stable-family orbit set at positive Euler form is a
singleton and has ordinary rational singular Euler characteristic one for any
topology. This is a set-level orbit quotient, not a King/GIT moduli scheme. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace KroneckerStableOrbitEuler
open KroneckerRingQuiverFamilies KroneckerOrdinarySingularEuler
variable {V A : Type} [Fintype V] [Fintype A]
  (s t : A → V) (d : V → ℕ) (θ : V → ℤ)

abbrev StableFamily := {M : Family s t d ℂ //
  KroneckerFiniteQuiverHom.Stable θ (toRepresentation s t d M)}

def orbitRel (M N : StableFamily s t d θ) : Prop :=
  ∃ g : Gauge d ℂ, gauge s t d g M.1 = N.1

theorem orbitRel_refl (M : StableFamily s t d θ) : orbitRel s t d θ M M := by
  exact ⟨1, gauge_one s t d M.1⟩

theorem orbitRel_symm {M N : StableFamily s t d θ}
    (h : orbitRel s t d θ M N) : orbitRel s t d θ N M := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, ?_⟩
  calc
    gauge s t d g⁻¹ N.1 = gauge s t d g⁻¹ (gauge s t d g M.1) := by rw [hg]
    _ = gauge s t d (g⁻¹ * g) M.1 := (gauge_mul s t d g⁻¹ g M.1).symm
    _ = M.1 := by simp

theorem orbitRel_trans {M N P : StableFamily s t d θ}
    (hMN : orbitRel s t d θ M N) (hNP : orbitRel s t d θ N P) :
    orbitRel s t d θ M P := by
  obtain ⟨g, hg⟩ := hMN
  obtain ⟨h, hh⟩ := hNP
  refine ⟨h * g, ?_⟩
  rw [gauge_mul, hg, hh]

def orbitSetoid : Setoid (StableFamily s t d θ) where
  r := orbitRel s t d θ
  iseqv := ⟨orbitRel_refl s t d θ, orbitRel_symm s t d θ,
    orbitRel_trans s t d θ⟩

abbrev StableOrbit := Quotient (orbitSetoid s t d θ)

/-- Positive Euler form puts every pair of actual stable complex families in the
same genuine product-GL orbit, hence the orbit quotient is subsingleton. -/
theorem stableOrbit_subsingleton
    (he : (∑ a, d (s a) * d (t a)) < ∑ v, d v * d v) :
    Subsingleton (StableOrbit s t d θ) := by
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | _ M =>
    induction y using Quotient.inductionOn with
    | _ N =>
      apply Quotient.sound
      exact positive_euler_stable_gauge s t d M.1 N.1 θ M.2 N.2 he



end KroneckerStableOrbitEuler
end
end

/- Original module: KroneckerCanonicalStableOrbit -/
section
/-! The quotient topology on genuine stable complex matrix families. Unlike the
older singleton-only Euler lemmas, this fixes the topology from the matrix space.
Identification with the analytification of King's moduli remains a source input. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalStableOrbit
open KroneckerRingQuiverFamilies KroneckerStableOrbitEuler
open KroneckerFiniteQuiverHom
variable {V A : Type} [Fintype V] [Fintype A]
    (s t : A → V) (d : V → ℕ) (θ : V → ℤ)

instance familyTopology : TopologicalSpace (Family s t d ℂ) :=
  inferInstanceAs (TopologicalSpace (∀ z : A, Fin (d (t z)) → Fin (d (s z)) → ℂ))

instance stableTopology : TopologicalSpace (StableFamily s t d θ) :=
  inferInstanceAs (TopologicalSpace {M : Family s t d ℂ // Stable θ (toRepresentation s t d M)})

instance orbitTopology : TopologicalSpace (StableOrbit s t d θ) :=
  inferInstanceAs (TopologicalSpace (Quotient (orbitSetoid s t d θ)))

/-- Product complex topology on arrow matrices, subspace topology on stable
families, then the quotient topology by the actual product-GL orbit relation. -/
def space : TopCat.{0} := TopCat.of (StableOrbit s t d θ)

def project : StableFamily s t d θ → space s t d θ :=
  Quotient.mk (orbitSetoid s t d θ)

theorem project_surjective : Function.Surjective (project s t d θ) :=
  Quotient.mk_surjective

theorem project_continuous : Continuous (project s t d θ) :=
  continuous_quot_mk

theorem project_eq_iff (M N : StableFamily s t d θ) :
    project s t d θ M = project s t d θ N ↔
      ∃ g : Gauge d ℂ, gauge s t d g M.val = N.val :=
  Quotient.eq

theorem space_nonempty_iff : Nonempty (space s t d θ) ↔
    ∃ R : Representation s t d, Stable θ R := by
  constructor
  · rintro ⟨q⟩
    obtain ⟨M,rfl⟩ := project_surjective s t d θ q
    exact ⟨toRepresentation s t d M.val,M.property⟩
  · rintro ⟨R,hR⟩
    let M := (complexRepresentationEquiv s t d).symm R
    have hM : Stable θ (toRepresentation s t d M) := by
      change Stable θ ((complexRepresentationEquiv s t d) ((complexRepresentationEquiv s t d).symm R))
      simpa only [Equiv.apply_symm_apply] using hR
    exact ⟨project s t d θ ⟨M,hM⟩⟩

end KroneckerCanonicalStableOrbit
end
end
