import KroneckerQuiverPullbackStability

/-! Finite-vertex statistics for the same actual quiver pullback. This is
supporting infrastructure for the two concrete cover presentations. -/
set_option autoImplicit false
namespace KroneckerFiniteQuiverPullbackStability
open KroneckerAbelianCover KroneckerFiniteQuiverHom
open KroneckerFiniteSupportDeckRepresentationTransport
open KroneckerQuiverPullbackSubrepresentations
open scoped BigOperators

theorem finite_pull_stable_iff {Q R : TypedQuiver} [Fintype Q.V] [Fintype R.V]
    (f : TypedQuiverIso Q R) (d : R.V →₀ ℕ) (θ : R.V → ℤ)
    (S : Representation R.source R.target (fun v => d v)) :
    Stable (fun v => θ (f.vertexEquiv v)) (pullRepresentation f d S) ↔ Stable θ S := by
  have hb : (∑ v, θ (f.vertexEquiv v) * (d (f.vertexEquiv v) : ℤ)) =
      ∑ v, θ v * (d v : ℤ) := f.vertexEquiv.sum_comp (fun v => θ v * (d v : ℤ))
  have ht : (∑ v, d (f.vertexEquiv v)) = ∑ v, d v := f.vertexEquiv.sum_comp (fun v => d v)
  have hs (U : Subrep S) : size (pullSubrep f d S U) = size U :=
    f.vertexEquiv.sum_comp (fun v => Module.finrank ℂ (U.space v))
  have hw (U : Subrep S) : weight (fun v => θ (f.vertexEquiv v)) (pullSubrep f d S U) =
      weight θ U := f.vertexEquiv.sum_comp (fun v => θ v * (Module.finrank ℂ (U.space v) : ℤ))
  constructor
  · intro h
    refine ⟨hb ▸ h.1, ?_⟩
    intro U hn hp
    have hU := h.2 (pullSubrep f d S U) (by rw [hs]; exact hn)
      (by rw [hs, ht]; exact hp)
    rwa [hw] at hU
  · intro h
    refine ⟨by rw [hb]; exact h.1, ?_⟩
    intro U hn hp
    obtain ⟨W, rfl⟩ := pullSubrep_surjective f d S U
    rw [hs] at hn
    rw [hs, ht] at hp
    rw [hw]
    exact h.2 W hn hp

end KroneckerFiniteQuiverPullbackStability
