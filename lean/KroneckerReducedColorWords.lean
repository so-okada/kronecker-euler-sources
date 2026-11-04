import Mathlib.Data.List.Chain
import Mathlib.Tactic

set_option autoImplicit false
namespace KroneckerReducedColorWords

abbrev Color := Fin 3
def Reduced (l : List Color) : Prop := l.IsChain (· ≠ ·)
abbrev Word := {l : List Color // Reduced l}

def root : Word := ⟨[], List.isChain_nil⟩

def toggleList (c : Color) : List Color → List Color
  | [] => [c]
  | d :: l => if c = d then l else c :: d :: l

theorem reduced_tail {c : Color} {l : List Color} (h : Reduced (c :: l)) :
    Reduced l := by
  cases l with
  | nil => exact List.isChain_nil
  | cons d l => exact (List.isChain_cons_cons.mp h).2

theorem toggle_reduced (c : Color) {l : List Color} (h : Reduced l) :
    Reduced (toggleList c l) := by
  cases l with
  | nil => exact List.isChain_singleton c
  | cons d l =>
    by_cases hc : c = d
    · simpa only [toggleList, ite_eq_left hc] using reduced_tail h
    · simpa only [Reduced, toggleList, ite_eq_right hc] using List.isChain_cons_cons.mpr ⟨hc,h⟩

def toggle (c : Color) (w : Word) : Word := ⟨toggleList c w.val, toggle_reduced c w.property⟩

theorem toggleList_involution (c : Color) {l : List Color} (h : Reduced l) :
    toggleList c (toggleList c l) = l := by
  cases l with
  | nil => simp [toggleList]
  | cons d l =>
    by_cases hc : c = d
    · subst d
      cases l with
      | nil => simp [toggleList]
      | cons e l =>
        have he := (List.isChain_cons_cons.mp h).1
        simp [toggleList, he]
    · simp [toggleList, hc]

theorem toggle_involution (c : Color) (w : Word) : toggle c (toggle c w) = w :=
  Subtype.ext (toggleList_involution c w.property)

theorem toggle_injective (c : Color) : Function.Injective (toggle c) :=
  Function.LeftInverse.injective (toggle_involution c)

theorem toggle_length (c : Color) (w : Word) :
    (toggle c w).val.length + 1 = w.val.length ∨
    (toggle c w).val.length = w.val.length + 1 := by
  rcases w with ⟨l,h⟩
  cases l with
  | nil => exact Or.inr rfl
  | cons d l =>
    by_cases hc : c = d
    · exact Or.inl (by simp [toggle, toggleList, hc])
    · exact Or.inr (by simp [toggle, toggleList, hc])

theorem toggle_ne (c : Color) (w : Word) : toggle c w ≠ w := by
  intro h
  have hl := toggle_length c w
  rw [h] at hl
  omega

theorem toggle_color_injective (w : Word) : Function.Injective (fun c => toggle c w) := by
  intro c d h
  have he := congrArg Subtype.val h
  rcases w with ⟨l,hl⟩
  cases l with
  | nil => simpa [toggle, toggleList] using he
  | cons e l =>
    by_cases hc : c = e <;> by_cases hd : d = e
    · exact hc.trans hd.symm
    · have hh := congrArg List.length he
      simp [toggle, toggleList, hc, hd] at hh
      omega
    · have hh := congrArg List.length he
      simp [toggle, toggleList, hc, hd] at hh
      omega
    · simpa [toggle, toggleList, hc, hd] using he

end KroneckerReducedColorWords
