import KroneckerReflectionPairModel

/-! The combined outgoing map has precisely the common arrow kernel. Stable
representations with positive sink dimension have no common source kernel. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionOutgoingMap
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
variable {m a b : ℕ} (R : PairRep m a b)

def outgoing : Space a →ₗ[ℂ] (Fin m → Space b) := LinearMap.pi R

theorem outgoing_injective (hb : 0<b) (hR : PairStable R) : Function.Injective (outgoing R) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra hnot
  let U := LinearMap.ker (outgoing R)
  have hu : 0<finrank ℂ U := by
    by_contra h
    have hz : finrank ℂ U=0 := Nat.eq_zero_of_not_pos h
    exact hnot (Submodule.finrank_eq_zero.mp hz)
  have hule : finrank ℂ U≤a := by simpa [Space] using U.finrank_le
  have hs : PairInvariant R U ⊥ := by
    intro i x hx
    exact congrFun (LinearMap.mem_ker.mp hx) i
  have ht : finrank ℂ (⊥ : Submodule ℂ (Space b))=0 := by simp
  have H := hR U ⊥ hs (by omega) (by omega)
  rw [ht] at H
  have hb' : (0 : ℤ)<b := by exact_mod_cast hb
  have hu' : (0 : ℤ)<finrank ℂ U := by exact_mod_cast hu
  norm_num at H
  nlinarith
end KroneckerReflectionOutgoingMap
