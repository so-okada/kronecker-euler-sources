import KroneckerReducedColorWords

set_option autoImplicit false
namespace KroneckerColorWordAction
open KroneckerReducedColorWords

def act : List Color → Word → Word
  | [], w => w
  | c :: l, w => toggle c (act l w)

def normal (l : List Color) : Word := act l root

theorem act_append (l k : List Color) (w : Word) : act (l ++ k) w = act l (act k w) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.cons_append, act, ih]

theorem act_toggle (c : Color) (w v : Word) :
    act (toggle c w).val v = toggle c (act w.val v) := by
  rcases w with ⟨l,hl⟩
  cases l with
  | nil => rfl
  | cons d l =>
    by_cases hc : c = d
    · subst d
      change act (if c = c then l else c :: c :: l) v = toggle c (toggle c (act l v))
      rw [ite_eq_left rfl, toggle_involution]
    · change act (if c = d then l else c :: d :: l) v = toggle c (toggle d (act l v))
      rw [ite_eq_right hc]
      rfl

theorem normal_reduced (w : Word) : normal w.val = w := by
  rcases w with ⟨l,hl⟩
  induction l with
  | nil => rfl
  | cons c l ih =>
    have ht := reduced_tail hl
    change toggle c (normal l) = ⟨c :: l,hl⟩
    rw [ih ht]
    apply Subtype.ext
    cases l with
    | nil => rfl
    | cons d l =>
      have hc := (List.isChain_cons_cons.mp hl).1
      simp only [toggle, toggleList, ite_eq_right hc]

theorem act_normal (l : List Color) (w : Word) : act (normal l).val w = act l w := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    change act (toggle c (normal l)).val w = toggle c (act l w)
    rw [act_toggle, ih]

theorem act_normalized (l : List Color) (g w : Word) :
    act (act l g).val w = act l (act g.val w) := by
  have hg : act l g = normal (l ++ g.val) := by
    simp only [normal, act_append]
    rw [show act g.val root = g from normal_reduced g]
  rw [hg, act_normal, act_append]

theorem act_reverse_cancel (l : List Color) (w : Word) : act l.reverse (act l w) = w := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.reverse_cons, act_append, act, toggle_involution, ih]

theorem act_cancel_reverse (l : List Color) (w : Word) : act l (act l.reverse w) = w := by
  simpa only [List.reverse_reverse] using act_reverse_cancel l.reverse w

theorem act_injective (l : List Color) : Function.Injective (act l) :=
  Function.LeftInverse.injective (act_reverse_cancel l)

end KroneckerColorWordAction
