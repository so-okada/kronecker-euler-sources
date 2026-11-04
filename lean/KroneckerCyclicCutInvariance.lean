import KroneckerCyclicWitnessTransport
import Mathlib.Data.Nat.Periodic

set_option autoImplicit false

namespace KroneckerCompatibility
open KroneckerStack

theorem witness_interval_congr {E F : ℕ → Edge} {p q l : ℕ}
    (h : ∀ k, k < l + 1 → E (p + k) = F (q + k)) :
    (HWitness E p (p + l) ∨ VWitness E p (p + l)) ↔
      (HWitness F q (q + l) ∨ VWitness F q (q + l)) := by
  let A := fun k => E (p + k)
  have he : ∀ k, k < l + 1 → A k = E (p + k) := fun _ _ => rfl
  have hf : ∀ k, k < l + 1 → A k = F (q + k) := h
  have hE := or_congr (hwitness_subpath (Nat.succ_pos l) he)
    (vwitness_subpath (Nat.succ_pos l) he)
  have hF := or_congr (hwitness_subpath (Nat.succ_pos l) hf)
    (vwitness_subpath (Nat.succ_pos l) hf)
  have hp : p + l.succ - 1 = p + l := by omega
  have hq : q + l.succ - 1 = q + l := by omega
  simpa only [hp, hq] using hE.symm.trans hF

theorem cyclic_span_shift {N a u v : ℕ} (ha : a < N) (hu : u < N) (hv : v < N) :
    (if (a + u) % N ≤ (a + v) % N then (a + v) % N else (a + v) % N + N) -
      (a + u) % N = (if u ≤ v then v else v + N) - u := by
  have hm (x : ℕ) (hx : x < 2 * N) : x % N = if x < N then x else x - N := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hm (a + u) (by omega), hm (a + v) (by omega)]
  split_ifs <;> omega

theorem cyclicCompatible_shift_forward {E : ℕ → Edge} {N a : ℕ}
    (hE : Function.Periodic E N) (ha : a < N) (hc : CyclicCompatible E N) :
    CyclicCompatible (fun k => E (a + k)) N := by
  intro u v hu hv hU hV
  let p := (a + u) % N
  let q := (a + v) % N
  have hN : 0 < N := by omega
  have hp : p < N := Nat.mod_lt _ hN
  have hq : q < N := Nat.mod_lt _ hN
  have hpu : E p = E (a + u) := hE.map_mod_nat _
  have hqv : E q = E (a + v) := hE.map_mod_nat _
  have hP : PositiveH E p := by simpa only [PositiveH, hpu] using hU
  have hQ : PositiveV E q := by simpa only [PositiveV, hqv] using hV
  have hw := hc p q hp hq hP hQ
  let l := (if u ≤ v then v else v + N) - u
  have hlu : u + l = if u ≤ v then v else v + N := by
    dsimp [l]; split_ifs <;> omega
  have hlp : p + l = if p ≤ q then q else q + N := by
    have hs := cyclic_span_shift ha hu hv
    change (if p ≤ q then q else q + N) - p = l at hs
    split_ifs at hs ⊢ <;> omega
  have he : ∀ k, k < l + 1 → E (p + k) = E (a + (u + k)) := by
    intro k _
    calc
      E (p + k) = E ((p + k) % N) := (hE.map_mod_nat _).symm
      _ = E ((a + (u + k)) % N) := by
        congr 1
        change (((a + u) % N + k) % N) = ((a + (u + k)) % N)
        rw [Nat.mod_add_mod, Nat.add_assoc]
      _ = E (a + (u + k)) := hE.map_mod_nat _
  have ht := (witness_interval_congr (F := fun k => E (a + k)) he).mp
  rw [hlp] at ht
  have hh := ht hw
  simpa only [hlu] using hh

theorem cyclicCompatible_shift {E : ℕ → Edge} {N a : ℕ}
    (hE : Function.Periodic E N) (ha : a < N) :
    CyclicCompatible (fun k => E (a + k)) N ↔ CyclicCompatible E N := by
  constructor
  · intro hc
    by_cases hz : a = 0
    · simpa only [hz, Nat.zero_add] using hc
    · have hF : Function.Periodic (fun k => E (a + k)) N := by
        intro k
        simpa only [Nat.add_assoc] using hE (a + k)
      have ht := cyclicCompatible_shift_forward hF (show N - a < N by omega) hc
      have he : (fun k => E (a + (N - a + k))) = E := by
        funext k
        rw [show a + (N - a + k) = k + N by omega]
        exact hE k
      simpa only [he] using ht
  · exact cyclicCompatible_shift_forward hE ha

end KroneckerCompatibility
