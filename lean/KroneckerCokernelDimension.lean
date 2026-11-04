import KroneckerAbstractCokernelReflection

/-! The actual source-reflection cokernel has dimension m*b-a whenever the
original outgoing map is injective, with its nonnegative dimension bound proved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCokernelDimension
open Module KroneckerFiniteQuiverHom KroneckerReflectionPairModel
open KroneckerAbstractOutgoingNaturality KroneckerAbstractCokernelReflection
variable {m a b : ℕ} (R : PairRep m a b)

theorem rank (h : Function.Injective (outgoing R)) :
    finrank ℂ (LinearMap.range (outgoing R))=a := by
  have he := (outgoing R).finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr h] at he
  simpa [Space] using he

theorem dimension (h : Function.Injective (outgoing R)) :
    finrank ℂ (Cokernel R)=m*b-a := by
  have he := (LinearMap.range (outgoing R)).finrank_quotient_add_finrank
  rw [rank R h] at he
  have hd : finrank ℂ (Fin m → Space b)=m*b := by simp [Space,Module.finrank_pi_fintype]
  rw [hd] at he
  change finrank ℂ (Cokernel R)+a=m*b at he
  omega

theorem bound (h : Function.Injective (outgoing R)) : a≤m*b := by
  have he := (LinearMap.range (outgoing R)).finrank_quotient_add_finrank
  rw [rank R h] at he
  have hd : finrank ℂ (Fin m → Space b)=m*b := by simp [Space,Module.finrank_pi_fintype]
  rw [hd] at he
  omega
end KroneckerCokernelDimension
