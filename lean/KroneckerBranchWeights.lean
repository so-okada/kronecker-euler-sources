import KroneckerFiniteMarkingPolynomial
import KroneckerSinkBranchLeafProfile

/- Original module: KroneckerGradedProfileWeights -/
section
set_option autoImplicit false
namespace KroneckerGradedProfileWeights
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

/-- The source degree and the actual leaf profile are independent exponents. -/
def gradedWeight (x : R) (y : Fin 3 → R) (n : ℕ) (N : Fin 3 → ℕ) : R :=
  x^n*∏ d,y d^(N d)

theorem graded_weight_add (x : R) (y : Fin 3 → R) (n m : ℕ) (N M : Fin 3 → ℕ) :
    gradedWeight x y (n+m) (fun d => N d+M d)=gradedWeight x y n N*gradedWeight x y m M := by
  simp only [gradedWeight,pow_add,Finset.prod_mul_distrib]
  ring

theorem graded_weight_sum {K : Type*} [Fintype K]
    (x : R) (y : Fin 3 → R) (n : K → ℕ) (N : K → Fin 3 → ℕ) :
    gradedWeight x y (∑ k,n k) (fun d => ∑ k,N k d)=∏ k,gradedWeight x y (n k) (N k) := by
  classical
  have hp : (∏ d,y d^(∑ k,N k d))=∏ k,∏ d,y d^(N k d) := by
    simp_rw [←Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_comm
  simp only [gradedWeight]
  rw [hp,←Finset.prod_pow_eq_pow_sum,Finset.prod_mul_distrib]

theorem graded_weight_leaf (x : R) (y : Fin 3 → R) (d : Fin 3) :
    gradedWeight x y 0 (fun e => if e=d then 1 else 0)=y d := by
  classical
  simp [gradedWeight]

theorem graded_weight_source (x : R) (y : Fin 3 → R) :
    gradedWeight x y 1 (fun _ => 0)=x := by simp [gradedWeight]

end KroneckerGradedProfileWeights
end

/- Original module: KroneckerBranchWeights -/
section
set_option autoImplicit false
namespace KroneckerBranchWeights
open KroneckerFiniteColoredTables KroneckerTableLeafMarks KroneckerSinkBranchLeafProfile
open KroneckerGradedProfileWeights KroneckerColoredIncidenceIso
attribute [local instance] Classical.propDecidable

variable {R : Type*} [CommSemiring R] {I J : Type} [Fintype I] [Fintype J]

noncomputable def sourceWeight (T : ColoredTable I J) (x : R) (y : Fin 3 → R) : R :=
  gradedWeight x y (Fintype.card I) (fun e => Fintype.card {j // LeafMark T e j})

noncomputable def sinkWeight (T : ColoredTable I J) (r : J) (d : Fin 3)
    (x : R) (y : Fin 3 → R) : R :=
  gradedWeight x y (Fintype.card I) (fun e => Fintype.card {j // SinkLeaf T r d e j})

theorem source_weight_iso {I' J' : Type} [Fintype I'] [Fintype J']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (f : ColoredIso (coloring T) (coloring U)) (x : R) (y : Fin 3 → R) :
    sourceWeight T x y=sourceWeight U x y := by
  unfold sourceWeight
  rw [Fintype.card_congr f.source]
  congr 1
  funext e
  exact leaf_mark_count_invariant f e

theorem sink_weight_iso {I' J' : Type} [Fintype I'] [Fintype J']
    {T : ColoredTable I J} {U : ColoredTable I' J'}
    (f : ColoredIso (coloring T) (coloring U)) (r : J) (d : Fin 3)
    (x : R) (y : Fin 3 → R) : sinkWeight T r d x y=sinkWeight U (f.sink r) d x y := by
  unfold sinkWeight
  rw [Fintype.card_congr f.source]
  congr 1
  funext e
  exact sink_leaf_count_invariant f r d e

end KroneckerBranchWeights
end
