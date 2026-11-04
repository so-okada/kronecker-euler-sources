import KroneckerGluedSubrepEquivalence

set_option autoImplicit false
noncomputable section

namespace KroneckerManuscriptAttachments
open KroneckerLinearCoverBlocks KroneckerGluedSubrepEquivalence

theorem scalar_mem_iff (V : Submodule ℂ ℂ) (z y : ℂ) (hz : z ≠ 0) :
    z * y ∈ V ↔ y ∈ V := by
  constructor
  · intro h
    have hh := V.smul_mem z⁻¹ h
    simpa [smul_eq_mul, ← mul_assoc, hz] using hh
  · exact fun h => V.smul_mem z h

theorem one_dimensional_map (f : ℂ →ₗ[ℂ] ℂ) : f = f 1 • LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h := f.map_smul x 1
  simpa [smul_eq_mul, mul_comm] using h

theorem nonzero_attachment (f : ℂ →ₗ[ℂ] ℂ) (hf : f ≠ 0)
    (V : Submodule ℂ ℂ) (x : ℂ) : f x ∈ V ↔ x ∈ V := by
  have hz : f 1 ≠ 0 := by
    intro hz
    apply hf
    rw [one_dimensional_map f, hz, zero_smul]
  rw [one_dimensional_map f]
  exact scalar_mem_iff V (f 1) x hz

def rescale (B : LinearCoverBlock) (z : B.Source → B.Sink → ℂ) :
    LinearCoverBlock := { B with arrow := fun s t => z s t • B.arrow s t }

def rescaleSubrep (B : LinearCoverBlock) (z : B.Source → B.Sink → ℂ)
    (S : BlockSubrep B) : BlockSubrep (rescale B z) where
  source := S.source
  sink := S.sink
  invariant := fun s t x hx => (S.sink t).smul_mem (z s t) (S.invariant s t x hx)

def unscaleSubrep (B : LinearCoverBlock) (z : B.Source → B.Sink → ℂ)
    (hz : ∀ s t, z s t ≠ 0) (S : BlockSubrep (rescale B z)) : BlockSubrep B where
  source := S.source
  sink := S.sink
  invariant := fun s t x hx => (scalar_mem_iff (S.sink t) (z s t)
    (B.arrow s t x) (hz s t)).mp (S.invariant s t x hx)

def subrepEquiv (B : LinearCoverBlock) (z : B.Source → B.Sink → ℂ)
    (hz : ∀ s t, z s t ≠ 0) : BlockSubrep B ≃ BlockSubrep (rescale B z) where
  toFun := rescaleSubrep B z
  invFun := unscaleSubrep B z hz
  left_inv _ := block_subrep_ext rfl rfl
  right_inv _ := block_subrep_ext rfl rfl

theorem rescale_stable_iff (B : LinearCoverBlock) (z : B.Source → B.Sink → ℂ)
    (hz : ∀ s t, z s t ≠ 0) : BlockKingStable (rescale B z) ↔ BlockKingStable B := by
  constructor
  · intro h S hn hp
    exact h (rescaleSubrep B z S) hn hp
  · intro h S hn hp
    exact h (unscaleSubrep B z hz S) hn hp

theorem rescale_support (B : LinearCoverBlock) (z : B.Source → B.Sink → ℂ)
    (hz : ∀ s t, z s t ≠ 0) (s : B.Source) (t : B.Sink) :
    (rescale B z).arrow s t = 0 ↔ B.arrow s t = 0 := by
  change z s t • B.arrow s t = 0 ↔ _
  simp [hz s t]

end KroneckerManuscriptAttachments
