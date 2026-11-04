import KroneckerManuscriptSlotBounds

/-! Admissible positive pairs for real sequences, with the fixed base 256/27.
The index zero is unused because the threshold is a positive natural number. -/
noncomputable section
set_option autoImplicit false

namespace KroneckerManuscriptAdmissiblePairs
open KroneckerManuscriptSlotBounds
open KroneckerReflectedSingleSlotCounts KroneckerReflectedPairSlotCounts

def Admissible (p q : ℕ → ℝ) (N : ℕ+) (A B : ℝ) : Prop :=
  0 < A ∧ 0 < B ∧
  (∀ j : ℕ, (N : ℕ) ≤ j → A * (256 / 27 : ℝ)^j * (j : ℝ)^(-3/2 : ℝ) ≤ p j) ∧
  (∀ j : ℕ, (N : ℕ) ≤ j → B * (256 / 27 : ℝ)^j * (j : ℝ)^(-1/2 : ℝ) ≤ q j)

def singleCount (d : Fin 3) (j : ℕ) : ℝ :=
  Fintype.card (SingleSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d)

def equalPairCount (d : Fin 3) (j : ℕ) : ℝ :=
  Fintype.card (PairSlotClass (Fin (j+1)) (Fin (2*(j+1)+1)) d d)

theorem admissible_iff_slotBounds (A B : ℝ) (d : Fin 3) :
    Admissible (singleCount d) (equalPairCount d) 256 A B ↔
      0 < A ∧ 0 < B ∧ SlotBounds256 A B := by
  constructor
  · rintro ⟨hA, hB, hp, hq⟩
    exact ⟨hA, hB, from_one_color A B d hp hq⟩
  · rintro ⟨hA, hB, hp, hq⟩
    exact ⟨hA, hB, fun j hj => hp j hj d, fun j hj => hq j hj d d⟩

end KroneckerManuscriptAdmissiblePairs

#print axioms KroneckerManuscriptAdmissiblePairs.Admissible
#print axioms KroneckerManuscriptAdmissiblePairs.singleCount
#print axioms KroneckerManuscriptAdmissiblePairs.equalPairCount
#print axioms KroneckerManuscriptAdmissiblePairs.admissible_iff_slotBounds
