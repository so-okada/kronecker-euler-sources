import KroneckerReflectionPairModel

/- Original module: KroneckerReflectionPairSubrepresentations -/
section
/-! Every invariant pair is an actual two-vertex subrepresentation and every
actual subrepresentation supplies that pair, with exact size and weight. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionPairSubrepresentations
open Module KroneckerFiniteQuiverHom KroneckerCanonicalKroneckerModuli
open KroneckerReflectionPairModel
open scoped BigOperators
variable {m a b : ℕ} (R : PairRep m a b)

def ofPair (U : Submodule ℂ (Space a)) (W : Submodule ℂ (Space b)) (h : PairInvariant R U W) :
    Subrep (toRepresentation R) where
  space v := Fin.cases (motive := fun i : Fin 2 => Submodule ℂ (Space (dimension a b i))) U (fun _ => W) v
  invariant := by
    intro i x hx
    exact h i x hx

theorem ofPair_size (U : Submodule ℂ (Space a)) (W : Submodule ℂ (Space b)) (h : PairInvariant R U W) :
    size (ofPair R U W h)=finrank ℂ U+finrank ℂ W := by
  unfold size
  rw [Fin.sum_univ_two]
  rfl

theorem ofPair_weight (U : Submodule ℂ (Space a)) (W : Submodule ℂ (Space b)) (h : PairInvariant R U W) :
    weight (character a b) (ofPair R U W h)=
      (b : ℤ)*(finrank ℂ U : ℤ)-(a : ℤ)*(finrank ℂ W : ℤ) := by
  unfold weight
  rw [Fin.sum_univ_two]
  change (b : ℤ)*(finrank ℂ U : ℤ)+(-(a : ℤ))*(finrank ℂ W : ℤ)=_
  ring

theorem subrep_size (S : Subrep (toRepresentation R)) : size S=finrank ℂ (S.space 0)+finrank ℂ (S.space 1) := by
  simp [size,Fin.sum_univ_two]

theorem subrep_weight (S : Subrep (toRepresentation R)) :
    weight (character a b) S=(b : ℤ)*(finrank ℂ (S.space 0) : ℤ)-(a : ℤ)*(finrank ℂ (S.space 1) : ℤ) := by
  simp [weight,character,Fin.sum_univ_two,sub_eq_add_neg]
end KroneckerReflectionPairSubrepresentations
end
end

/- Original module: KroneckerReflectionPairStability -/
section
/-! The two-space reflection stability predicate is exactly the internal
stability of the actual canonical m-Kronecker representation, for all m,a,b. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerReflectionPairStability
open Module KroneckerFiniteQuiverHom KroneckerCanonicalKroneckerModuli
open KroneckerReflectionPairModel KroneckerReflectionPairSubrepresentations
open scoped BigOperators
variable {m a b : ℕ} (R : PairRep m a b)

theorem stable_iff : Stable (character a b) (toRepresentation R) ↔ PairStable R := by
  have ht : (∑ v : Fin 2,dimension a b v)=a+b := by simp [Fin.sum_univ_two,dimension]
  constructor
  · intro h U W hs hn hp
    have H := h.2 (ofPair R U W hs)
    rw [ofPair_size,ofPair_weight,ht] at H
    exact H hn hp
  · intro h
    refine ⟨?_,?_⟩
    · simp [Fin.sum_univ_two,dimension,character]
      ring
    · intro S hn hp
      rw [subrep_size] at hn hp
      rw [subrep_weight]
      exact h (S.space 0) (S.space 1) S.invariant hn (by rwa [ht] at hp)
end KroneckerReflectionPairStability
end
end
