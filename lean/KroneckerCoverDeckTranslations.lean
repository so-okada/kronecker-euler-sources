import KroneckerColorWordCover

set_option autoImplicit false
namespace KroneckerCoverDeckTranslations
open KroneckerReducedColorWords KroneckerColorWordAction KroneckerWordTranslations
open KroneckerWordParity KroneckerColorWordCover

structure Deck where
  equiv : Word ≃ Word
  commutes : ∀ c w, equiv (toggle c w) = toggle c (equiv w)
  preserves_parity : ∀ w, parity (equiv w) = parity w

instance : CoeFun Deck (fun _ => Word → Word) := ⟨fun d => d.equiv⟩

theorem translate_parity (g w : Word) : parity (translate g w) = (parity w + parity g) % 2 := by
  rw [translate, act_parity]
  unfold parity
  omega

def evenTranslation (g : Word) (hg : parity g = 0) : Deck where
  equiv := translation g
  commutes := translate_toggle g
  preserves_parity w := by
    change parity (translate g w) = parity w
    rw [translate_parity, hg, add_zero]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))

theorem commutes_act (f : Word → Word) (hf : ∀ c w, f (toggle c w) = toggle c (f w))
    (l : List Color) (w : Word) : f (act l w) = act l (f w) := by
  induction l with
  | nil => rfl
  | cons c l ih => rw [act, hf, ih]; rfl

theorem deck_determined_by_root (d : Deck) (w : Word) : d w = translate (d root) w := by
  have h := commutes_act d d.commutes w.val root
  simpa only [show act w.val root = w from normal_reduced w, translate] using h


theorem deck_transitive_same_parity {u v : Word} (h : parity u = parity v) :
    ∃ d : Deck, d u = v := by
  let g := translate v (inverseWord u)
  have hg : parity g = 0 := by
    have hi : parity (inverseWord u) = parity u := by
      rw [inverseWord, normal_parity, List.length_reverse]
      rfl
    change parity (translate v (inverseWord u)) = 0
    rw [translate_parity, hi, h]
    have : parity v < 2 := Nat.mod_lt _ (by omega)
    omega
  refine ⟨evenTranslation g hg, ?_⟩
  change translate (translate v (inverseWord u)) u = v
  rw [←translate_comp, inverse_translate, translate_root]

end KroneckerCoverDeckTranslations
