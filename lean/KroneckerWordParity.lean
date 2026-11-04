import KroneckerColorWordAction

set_option autoImplicit false
namespace KroneckerWordParity
open KroneckerReducedColorWords KroneckerColorWordAction

def parity (w : Word) : ℕ := w.val.length % 2

theorem toggle_parity (c : Color) (w : Word) : parity (toggle c w) = (parity w + 1) % 2 := by
  have h := toggle_length c w
  unfold parity
  omega

theorem act_parity (l : List Color) (w : Word) :
    parity (act l w) = (l.length + parity w) % 2 := by
  induction l with
  | nil => simp [act, parity]
  | cons c l ih =>
    rw [act, toggle_parity, ih]
    simp only [List.length_cons]
    omega

theorem normal_parity (l : List Color) : parity (normal l) = l.length % 2 := by
  simpa only [normal, parity, root, List.length_nil, Nat.zero_mod, add_zero] using act_parity l root

theorem toggle_opposite_parity (c : Color) (w : Word) : parity (toggle c w) ≠ parity w := by
  rw [toggle_parity]
  have : parity w < 2 := Nat.mod_lt _ (by omega)
  omega

end KroneckerWordParity
