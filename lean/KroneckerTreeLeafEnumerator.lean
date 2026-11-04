import KroneckerFiniteMarkingPolynomial
import KroneckerPairTreeClassCount

set_option autoImplicit false
namespace KroneckerTreeLeafEnumerator
open KroneckerFiniteMarkingPolynomial KroneckerTableLeafMarks KroneckerLabelledTreeClassCount
open KroneckerMarkedTreeClassCount KroneckerPairTreeClassCount MvPolynomial
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable (I J : Type) [Fintype I] [Fintype J]

noncomputable def leafProfile (q : TreeClass I J) (d : Fin 3) : ℕ :=
  Fintype.card {j // LeafMark q.out.1 d j}

noncomputable def leafEnumerator : MvPolynomial (Fin 3) ℚ := profilePolynomial (leafProfile I J)



theorem repeated_marked_enumerator_count (d : Fin 3) :
    eval (fun _ => (1 : ℚ)) (pderiv d (pderiv d (leafEnumerator I J)))=
      Fintype.card (PairClass I J d d) := by
  rw [leafEnumerator,repeated_marking_derivative,equal_color_class_count]
  simp only [leafProfile,Nat.cast_sum,Nat.cast_mul]

theorem mixed_marked_enumerator_count {d e : Fin 3} (hde : d≠e) :
    eval (fun _ => (1 : ℚ)) (pderiv e (pderiv d (leafEnumerator I J)))=
      Fintype.card (PairClass I J d e) := by
  rw [leafEnumerator,mixed_marking_derivative _ hde,distinct_color_class_count hde]
  simp only [leafProfile,Nat.cast_sum,Nat.cast_mul]

end KroneckerTreeLeafEnumerator
