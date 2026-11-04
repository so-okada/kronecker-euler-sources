import KroneckerReducedColorWords
import Mathlib.Data.Finsupp.Basic
import Mathlib.Basic.Finite.Prod

set_option autoImplicit false
namespace KroneckerBoundedCoverDimensions
open KroneckerReducedColorWords
open scoped BigOperators

/-- Every positive coordinate consumes at least one unit of total dimension. -/
theorem support_card_le_total {V : Type} (d : V →₀ ℕ) :
    d.support.card ≤ d.sum (fun _ n => n) := by
  classical
  change d.support.card ≤ ∑ v ∈ d.support, d v
  calc
    d.support.card = ∑ v ∈ d.support, (1 : ℕ) := by simp
    _ ≤ ∑ v ∈ d.support, d v := Finset.sum_le_sum (fun v hv =>
      Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))

/-- Each vertex dimension is bounded by the total dimension. -/
theorem coordinate_le_total {V : Type} (d : V →₀ ℕ) (v : V) :
    d v ≤ d.sum (fun _ n => n) := by
  classical
  by_cases h : v ∈ d.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) h
  · have hz : d v = 0 := Finsupp.notMem_support_iff.mp h
    rw [hz]
    exact Nat.zero_le _






end KroneckerBoundedCoverDimensions
