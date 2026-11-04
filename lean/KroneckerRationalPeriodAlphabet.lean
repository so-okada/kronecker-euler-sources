import KroneckerMechanicalWords
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.List.Rotate

section

/- Original module: KroneckerRationalRunPeriod -/
section
/-! Exact rational natural run sequences are periodic, including modular reduction. -/
set_option autoImplicit false
namespace KroneckerRationalRunPeriod
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalPeriodicity

theorem natRun_rational_periodic (p : ℤ) (q : ℕ) (hq : 0 < q) (u : ℝ) :
    Function.Periodic (natRun ((p : ℝ)/(q : ℝ)) u) q := by
  intro i
  unfold natRun
  rw [rational_mechanical_period p q hq u i]

theorem natRun_rational_mod (p : ℤ) (q : ℕ) (hq : 0 < q) (u : ℝ) (i : ℕ) :
    natRun ((p : ℝ)/(q : ℝ)) u (i%q)=natRun ((p : ℝ)/(q : ℝ)) u i :=
  (natRun_rational_periodic p q hq u).map_mod_nat i

end KroneckerRationalRunPeriod
end

/- Original module: KroneckerPeriodicListRotation -/
section
/-! One period of a periodic sequence at any start is a list rotation. -/
set_option autoImplicit false
namespace KroneckerPeriodicListRotation

theorem periodic_list_rotation {α : Type*} (f : ℕ → α) (q start : ℕ)
    (hf : Function.Periodic f q) :
    List.ofFn (fun i : Fin q => f (start+i.val)) =
      (List.ofFn (fun i : Fin q => f i.val)).rotate start := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    rw [List.getElem_rotate]
    simp only [List.getElem_ofFn, List.length_ofFn]
    simpa only [Nat.add_comm] using (hf.map_mod_nat (start+i)).symm

end KroneckerPeriodicListRotation
end

/- Original module: KroneckerRationalWordRotation -/
section
/-! The canonical mechanical period and its shifted copies have exact cyclic phases. -/
set_option autoImplicit false
namespace KroneckerRationalWordRotation
open KroneckerMechanicalWords KroneckerRationalRunPeriod KroneckerPeriodicListRotation

noncomputable def rationalPeriod (p q : ℕ) : List ℕ :=
  mechanicalWord ((p : ℝ)/(q : ℝ)) 0 0 q

theorem rationalPeriod_length (p q : ℕ) : (rationalPeriod p q).length=q := by
  simp [rationalPeriod,mechanicalWord_length]

theorem rational_word_rotation (p q : ℕ) (hq : 0 < q) (start : ℕ) :
    mechanicalWord ((p : ℝ)/(q : ℝ)) 0 start q = (rationalPeriod p q).rotate start := by
  simpa only [mechanicalWord,rationalPeriod,Nat.zero_add,Int.cast_natCast] using
    periodic_list_rotation (natRun ((p : ℝ)/(q : ℝ)) 0) q start
      (natRun_rational_periodic (p : ℤ) q hq 0)

end KroneckerRationalWordRotation
end
end

section

/-! The canonical rational period has the alphabet needed by the counting estimates. -/
set_option autoImplicit false
namespace KroneckerRationalPeriodAlphabet
open KroneckerMechanicalWords KroneckerRationalWordRotation

theorem rationalPeriod_nonempty (p q : ℕ) (hq : 0 < q) : rationalPeriod p q ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [rationalPeriod_length,List.length_nil] at hl
  omega

theorem rationalPeriod_legal (p q M : ℕ)
    (h₁ : 1 ≤ (p : ℝ)/(q : ℝ)) (hM : (p : ℝ)/(q : ℝ) ≤ (M : ℝ)) :
    ∀ r ∈ rationalPeriod p q, 1 ≤ r ∧ r ≤ M :=
  mechanicalWord_legal ((p : ℝ)/(q : ℝ)) 0 0 q M h₁ hM

end KroneckerRationalPeriodAlphabet
end

