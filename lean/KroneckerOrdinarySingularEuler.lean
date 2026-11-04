import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-! Ordinary Euler characteristic by actual rational singular homology.
The admissibility predicate excludes infinite-dimensional or infinitely supported
homology. This does not identify any scheme point space with a moduli space. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace KroneckerOrdinarySingularEuler
abbrev Homology (X : TopCat.{0}) (n : ℕ) : ModuleCat ℚ :=
  ((singularHomologyFunctor (ModuleCat ℚ) n).obj (ModuleCat.of ℚ ℚ)).obj X

def betti (X : TopCat.{0}) (n : ℕ) : ℕ := Module.finrank ℚ (Homology X n)
def Admissible (X : TopCat.{0}) : Prop :=
  (∀ n, FiniteDimensional ℚ (Homology X n)) ∧ (Function.support (betti X)).Finite

def ordinaryEuler (X : TopCat.{0}) (_ : Admissible X) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (betti X n : ℤ)

def homologyIso {X Y : TopCat.{0}} (e : X ≅ Y) (n : ℕ) :
    Homology X n ≅ Homology Y n :=
  ((singularHomologyFunctor (ModuleCat ℚ) n).obj (ModuleCat.of ℚ ℚ)).mapIso e

theorem betti_iso {X Y : TopCat.{0}} (e : X ≅ Y) (n : ℕ) :
    betti X n = betti Y n := (homologyIso e n).toLinearEquiv.finrank_eq

theorem ordinaryEuler_iso {X Y : TopCat.{0}} (e : X ≅ Y)
    (hX : Admissible X) (hY : Admissible Y) : ordinaryEuler X hX = ordinaryEuler Y hY := by
  unfold ordinaryEuler
  congr 1
  funext n
  rw [betti_iso e n]

variable (X : TopCat.{0}) [Subsingleton X] [Nonempty X]

def homologyZeroIso : Homology X 0 ≅ ModuleCat.of ℚ ℚ := by
  letI : Unique X := ⟨⟨Classical.choice (inferInstance : Nonempty X)⟩,
    fun x => Subsingleton.elim _ _⟩
  exact singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat ℚ)
    (ModuleCat.of ℚ ℚ) X ≪≫ coproductUniqueIso (fun _ : X => ModuleCat.of ℚ ℚ)

theorem homology_positive_subsingleton {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (Homology X n) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat ℚ) n (ModuleCat.of ℚ ℚ) X hn)

theorem betti_singleton (n : ℕ) : betti X n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simpa [betti] using (homologyZeroIso X).toLinearEquiv.finrank_eq
  · let := homology_positive_subsingleton X hn
    simpa [betti, hn] using (Module.finrank_zero_of_subsingleton (R := ℚ) (M := Homology X n))

theorem singleton_admissible : Admissible X := by
  constructor
  · intro n
    by_cases hn : n = 0
    · subst n
      exact FiniteDimensional.of_injective (homologyZeroIso X).toLinearEquiv.toLinearMap
        (homologyZeroIso X).toLinearEquiv.injective
    · let := homology_positive_subsingleton X hn
      infer_instance
  · apply (Set.finite_singleton 0).subset
    intro n hn
    by_contra h
    exact hn (by simpa [betti_singleton, Set.mem_singleton_iff.mp, h])

/-- The ordinary singular-homology Euler characteristic of any nonempty
singleton topological space is one; it is not defined as a point count. -/
theorem ordinaryEuler_singleton : ordinaryEuler X (singleton_admissible X) = 1 := by
  unfold ordinaryEuler
  rw [finsum_eq_single _ 0]
  · simp [betti_singleton]
  · intro n hn
    simp [betti_singleton, hn]
end KroneckerOrdinarySingularEuler
