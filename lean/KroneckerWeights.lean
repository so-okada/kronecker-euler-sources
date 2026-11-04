import KroneckerColoring
import Mathlib.Data.Nat.Choose.Sum

/-! Cardinalities of the actual binomial-colored grading sets. -/
set_option autoImplicit false
namespace KroneckerWeights
open KroneckerColoring
open scoped BigOperators

abbrev Grades (m n : ℕ) := Fin n → Fin (m+1)
abbrev ColorFiber {m n : ℕ} (d : Grades m n) :=
  (i : Fin n) → Fin (Nat.choose m (d i).val)

def grades {m n : ℕ} (g : Coloring m n) : Grades m n := fun i => (g i).1

/-- Fix color zero at every allowed grade. Every fiber is nonempty. -/
def representative {m n : ℕ} (d : Grades m n) : Coloring m n :=
  fun i => ⟨d i,⟨0,Nat.choose_pos (Nat.le_of_lt_succ (d i).isLt)⟩⟩


def colorEquiv (m n : ℕ) : Coloring m n ≃ (d : Grades m n) × ColorFiber d where
  toFun g := ⟨grades g,fun i => (g i).2⟩
  invFun dc := fun i => ⟨dc.1 i,dc.2 i⟩
  left_inv g := rfl
  right_inv dc := by cases dc; rfl

def coloredSubtypeEquiv {m n : ℕ} (P : Grades m n → Prop) :
    {g : Coloring m n // P (grades g)} ≃ (d : {d : Grades m n // P d}) × ColorFiber d.val where
  toFun g := ⟨⟨grades g.val,g.property⟩,fun i => (g.val i).2⟩
  invFun dc := ⟨fun i => ⟨dc.1.val i,dc.2 i⟩,dc.1.property⟩
  left_inv g := rfl
  right_inv dc := by cases dc; rfl

def weight {m n : ℕ} (d : Grades m n) : ℕ :=
  ∏ i : Fin n,Nat.choose m (d i).val

noncomputable def weightedCount {m n : ℕ} (P : Grades m n → Prop) : ℕ := by
  classical
  exact ∑ d : Grades m n,if P d then weight d else 0

theorem fiber_card {m n : ℕ} (d : Grades m n) :
    Fintype.card (ColorFiber d)=weight d := by
  simp [ColorFiber,weight]

theorem colored_count {m n : ℕ} (P : Grades m n → Prop) :
    Nat.card {g : Coloring m n // P (grades g)}=weightedCount P := by
  classical
  rw [Nat.card_congr (coloredSubtypeEquiv P),Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [fiber_card]
  simp only [weightedCount,← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) weight).symm

theorem palette_card (m : ℕ) : Fintype.card (Palette m)=2^m := by
  simp only [Palette,Fintype.card_sigma,Fintype.card_fin]
  simpa only [Fin.sum_univ_eq_sum_range] using Nat.sum_range_choose m

theorem coloring_card (m n : ℕ) : Fintype.card (Coloring m n)=(2^m)^n := by
  rw [Fintype.card_fun,palette_card,Fintype.card_fin]

theorem colored_count_bound {m n : ℕ} (P : Grades m n → Prop) :
    weightedCount P≤(2^m)^n := by
  classical
  rw [← colored_count,Nat.card_eq_fintype_card,← coloring_card]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

end KroneckerWeights
