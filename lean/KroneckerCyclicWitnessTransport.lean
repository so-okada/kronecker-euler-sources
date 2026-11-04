import KroneckerCompatibility

set_option autoImplicit false

namespace KroneckerCompatibility
open KroneckerStack

theorem walk_subpath {E F : ℕ → Edge} {a l : ℕ}
    (h : ∀ k, k < l → F k = E (a + k)) (f : Edge → ℤ) (k : ℕ) (hk : k ≤ l) :
    walk f F k = walk f E (a + k) - walk f E a := by
  induction k with
  | zero => simp [walk]
  | succ k ih =>
    rw [walk, h k (by omega), Nat.add_succ, walk, ih (by omega)]
    omega

theorem hwitness_subpath {E F : ℕ → Edge} {a l : ℕ} (hl : 0 < l)
    (h : ∀ k, k < l → F k = E (a + k)) :
    HWitness F 0 (l - 1) ↔ HWitness E a (a + l - 1) := by
  constructor
  · rintro ⟨k, hk, hkl, hv, hd⟩
    refine ⟨a + k, by omega, by omega, ?_, ?_⟩
    · simpa only [Vertical, h k (by omega)] using hv
    · have hw := walk_subpath h Edge.debtChange (k + 1) (by omega)
      change walk Edge.debtChange F (k + 1) = 0 at hd
      change walk Edge.debtChange E (a + k + 1) = walk Edge.debtChange E a
      rw [show a + (k + 1) = a + k + 1 by omega] at hw
      omega
  · rintro ⟨k, hk, hkl, hv, hd⟩
    refine ⟨k - a, by omega, by omega, ?_, ?_⟩
    · simpa only [Vertical, h (k - a) (by omega), Nat.add_sub_cancel' (by omega : a ≤ k)] using hv
    · have hw := walk_subpath h Edge.debtChange (k - a + 1) (by omega)
      rw [show a + (k - a + 1) = k + 1 by omega] at hw
      change walk Edge.debtChange F (k - a + 1) = 0
      change walk Edge.debtChange E (k + 1) = walk Edge.debtChange E a at hd
      omega

theorem vwitness_subpath {E F : ℕ → Edge} {a l : ℕ} (hl : 0 < l)
    (h : ∀ k, k < l → F k = E (a + k)) :
    VWitness F 0 (l - 1) ↔ VWitness E a (a + l - 1) := by
  have ht : l - 1 + 1 = l := by omega
  have ht' : a + l - 1 + 1 = a + l := by omega
  constructor
  · rintro ⟨k, hk, hkl, hh, hb⟩
    refine ⟨a + k, by omega, by omega, ?_, ?_⟩
    · simpa only [Horizontal, h k (by omega)] using hh
    · have hw := walk_subpath h Edge.credit k (by omega)
      have hw' := walk_subpath h Edge.credit l le_rfl
      change walk Edge.credit F k = walk Edge.credit F (l - 1 + 1) at hb
      rw [ht] at hb
      change walk Edge.credit E (a + k) = walk Edge.credit E (a + l - 1 + 1)
      rw [ht']
      omega
  · rintro ⟨k, hk, hkl, hh, hb⟩
    refine ⟨k - a, by omega, by omega, ?_, ?_⟩
    · simpa only [Horizontal, h (k - a) (by omega), Nat.add_sub_cancel' (by omega : a ≤ k)] using hh
    · have hw := walk_subpath h Edge.credit (k - a) (by omega)
      have hw' := walk_subpath h Edge.credit l le_rfl
      rw [show a + (k - a) = k by omega] at hw
      change walk Edge.credit E k = walk Edge.credit E (a + l - 1 + 1) at hb
      rw [ht'] at hb
      change walk Edge.credit F (k - a) = walk Edge.credit F (l - 1 + 1)
      rw [ht]
      omega

end KroneckerCompatibility
