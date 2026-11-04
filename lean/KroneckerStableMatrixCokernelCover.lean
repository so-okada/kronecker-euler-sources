import Mathlib.LinearAlgebra.Basis.VectorSpace
import KroneckerStableMatrixKernelCover

/- Original module: KroneckerMatrixCokernelChartCover -/
section
/-! Every injective matrix has an open fixed-retraction chart; invertibility
of its source block is enough to prove injectivity throughout that chart. -/
noncomputable section
set_option autoImplicit false
open Matrix
namespace KroneckerMatrixCokernelChartCover
open KroneckerMatrixCokernelChart
variable {v w : Type} [Fintype v] [Fintype w] [DecidableEq v] [DecidableEq w]
theorem exists_retraction (I : Matrix w v ℂ) (hI : Function.Injective (Matrix.toLin' I)) :
    ∃ R : Matrix v w ℂ, R*I=1 := by
  obtain ⟨r,hr⟩ := (Matrix.toLin' I).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hI)
  refine ⟨LinearMap.toMatrix' r,?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
  exact hr
theorem covered (I : Matrix w v ℂ) (hI : Function.Injective (Matrix.toLin' I)) :
    ∃ R : Matrix v w ℂ,I ∈ Domain R := by
  obtain ⟨R,hR⟩ := exists_retraction I hI
  refine ⟨R,?_⟩
  change (R*I).det ≠ 0
  rw [hR,Matrix.det_one]
  exact one_ne_zero
end KroneckerMatrixCokernelChartCover
end
end

/- Original module: KroneckerStableMatrixOutgoingInjective -/
section
/-! Positive-sink stable families have injective outgoing block matrices,
providing the chart-cover hypothesis for the inverse reflection construction. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableMatrixOutgoingInjective
open KroneckerPairMatrixCoordinates KroneckerPairMatrixOutgoing KroneckerStableRectangularMatrices
variable {m a b : ℕ}
theorem injective (hb : 0<b) (M : Stable m a b) :
    Function.Injective (Matrix.toLin' (outgoing M.val)) := by
  intro x y hxy
  apply KroneckerReflectionOutgoingMap.outgoing_injective (pair M.val) hb M.property
  apply KroneckerPairMatrixIncoming.flatten.injective
  exact hxy
end KroneckerStableMatrixOutgoingInjective
end
end

/- Original module: KroneckerStableMatrixCokernelCover -/
section
/-! Fixed-retraction charts pull back to an open cover of positive-sink
stable matrix families, with continuous outgoing parameter maps. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerStableMatrixCokernelCover
open KroneckerPairMatrixOutgoing KroneckerStableRectangularMatrices
variable {m a b : ℕ}
def chart (R : Matrix (Fin a) (Fin m × Fin b) ℂ) : Set (Stable m a b) :=
  {M | outgoing M.val ∈ KroneckerMatrixCokernelChart.Domain R}
theorem chart_open (R : Matrix (Fin a) (Fin m × Fin b) ℂ) : IsOpen (chart R) :=
  (KroneckerMatrixCokernelChart.isOpen_domain R).preimage
    (continuous_outgoing.comp continuous_subtype_val)
theorem cover (hb : 0<b) (M : Stable m a b) :
    ∃ R : Matrix (Fin a) (Fin m × Fin b) ℂ,M ∈ chart R :=
  KroneckerMatrixCokernelChartCover.covered _ (KroneckerStableMatrixOutgoingInjective.injective hb M)
def parameter (R : Matrix (Fin a) (Fin m × Fin b) ℂ) (M : chart R) :
    KroneckerMatrixCokernelChart.Domain R := ⟨outgoing M.val.val,M.property⟩
theorem continuous_parameter (R : Matrix (Fin a) (Fin m × Fin b) ℂ) : Continuous (parameter R) :=
  (continuous_outgoing.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
end KroneckerStableMatrixCokernelCover
end
end
