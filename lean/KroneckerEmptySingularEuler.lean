import KroneckerOrdinarySingularEuler

/-! Rational singular homology and ordinary Euler characteristic of an actually
empty topological space.  This supplies the empty endpoint needed by the
projective hyperplane filtration; it is not a point-count convention. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace KroneckerOrdinarySingularEuler

variable (X : TopCat.{0}) [IsEmpty X]

private theorem coproduct_isZero_of_isEmpty :
    IsZero (∐ fun _ : X ↦ ModuleCat.of ℚ ℚ) := by
  apply IsInitial.isZero
  exact isColimitEquivIsInitialOfIsEmpty (ModuleCat ℚ)
    (colimit.cocone (Discrete.functor fun _ : X ↦ ModuleCat.of ℚ ℚ))
    (colimit.isColimit _)

theorem homology_empty_isZero (n : ℕ) : IsZero (Homology X n) := by
  by_cases hn : n = 0
  · subst n
    exact IsZero.of_iso (coproduct_isZero_of_isEmpty X)
      (singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (ModuleCat ℚ) (ModuleCat.of ℚ ℚ) X)
  · exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℚ) n (ModuleCat.of ℚ ℚ) X hn

theorem betti_empty (n : ℕ) : betti X n = 0 := by
  let := ModuleCat.isZero_iff_subsingleton.mp (homology_empty_isZero X n)
  exact Module.finrank_zero_of_subsingleton

theorem empty_admissible : Admissible X := by
  constructor
  · intro n
    let := ModuleCat.isZero_iff_subsingleton.mp (homology_empty_isZero X n)
    infer_instance
  · rw [show Function.support (betti X) = ∅ by
      ext n
      simp [Function.mem_support, betti_empty X n]]
    exact Set.finite_empty

/-- The ordinary rational singular-homology Euler characteristic of an empty
space is zero. -/
theorem ordinaryEuler_empty : ordinaryEuler X (empty_admissible X) = 0 := by
  unfold ordinaryEuler
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  simp [betti_empty X n]

end KroneckerOrdinarySingularEuler
