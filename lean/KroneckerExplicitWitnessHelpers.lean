import KroneckerPrecursorPrefixHelpers
import KroneckerShadowDebtHelpers

/-! The first upward crossing and the least failing owned-edge inequality.
The sets and their minima are explicit. All word indices are zero based;
balance arguments are boundary indices, as in the manuscript. -/
set_option autoImplicit false
namespace KroneckerExplicitWitnessHelpers
noncomputable section
open KroneckerStack KroneckerPredecessor

def crossingSet {n : ℕ} (U : Word n) (r s : Fin n) : Finset ℕ :=
  (Finset.Icc (r.val + 2) s.val).filter fun j => balance U (s.val + 1) < balance U j

theorem crossing_nonempty {n : ℕ} {U : Word n} {r s : Fin n}
    (hrs : r.val < s.val) (hs : ¬ IsHorizontal U s) (hg : 0 < (U s).grade)
    (hb : baseline U r ≤ balance U (s.val + 1)) : (crossingSet U r s).Nonempty := by
  have step := balance_succ U s.isLt
  change balance U (s.val + 1) = balance U s.val + (U s).credit at step
  have hc : (U s).credit = -(U s).grade := by
    cases he : U s with
    | H g => simp [IsHorizontal, he] at hs
    | V g => rfl
  have hi : balance U (s.val + 1) < balance U s.val := by
    rw [hc] at step
    omega
  have hbound : r.val + 2 ≤ s.val := by
    unfold baseline at hb
    by_contra hn
    have he : s.val = r.val + 1 := by omega
    rw [he] at hb hi
    omega
  exact ⟨s.val, by simp [crossingSet, hbound, hi]⟩

theorem first_crossing {n : ℕ} {U : Word n} {r s : Fin n}
    (hJ : (crossingSet U r s).Nonempty) (hb : baseline U r ≤ balance U (s.val + 1)) :
    let j := (crossingSet U r s).min' hJ
    r.val + 1 < j ∧ j ≤ s.val ∧
    (∀ hj : j - 1 < n, IsHorizontal U ⟨j - 1, hj⟩) ∧
    balance U (j - 1) = balance U (s.val + 1) ∧
    balance U j = balance U (s.val + 1) + 1 := by
  dsimp only
  set j := (crossingSet U r s).min' hJ with hjdef
  have hm := Finset.min'_mem (crossingSet U r s) hJ
  change j ∈ crossingSet U r s at hm
  obtain ⟨⟨hlo, hhi⟩, hcross⟩ := by
    simpa only [crossingSet, Finset.mem_filter, Finset.mem_Icc] using hm
  have hjn : j - 1 < n := by omega
  have hprev : balance U (j - 1) ≤ balance U (s.val + 1) := by
    by_cases he : j = r.val + 2
    · have he' : j - 1 = r.val + 1 := by omega
      simpa only [he', baseline] using hb
    · by_contra hn
      have hm' : j - 1 ∈ crossingSet U r s := by
        simp only [crossingSet, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      have hmin := Finset.min'_le (crossingSet U r s) (j - 1) hm'
      change j ≤ j - 1 at hmin
      omega
  have step := balance_succ U hjn
  have he : j - 1 + 1 = j := by omega
  rw [he] at step
  have hh : IsHorizontal U ⟨j - 1, hjn⟩ := by
    cases heU : U ⟨j - 1, hjn⟩ with
    | H g => simp [IsHorizontal, heU]
    | V g => simp only [heU, Edge.credit] at step; omega
  rw [credit_horizontal hh] at step
  exact ⟨by omega, hhi, fun _ => hh, by omega, by omega⟩

def failureSet {n : ℕ} (U : Word n) (p : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun s => ¬ IsHorizontal U s ∧ balance U (s.val + 1) < baseline U (p s)

theorem least_failure {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hS : (failureSet U p).Nonempty) :
    let s := (failureSet U p).min' hS
    ¬ IsHorizontal U s ∧ balance U (s.val + 1) < baseline U (p s) ∧
      ∀ w : Fin n, w.val < s.val → ¬ IsHorizontal U w →
        baseline U (p w) ≤ balance U (w.val + 1) := by
  dsimp only
  let s := (failureSet U p).min' hS
  have hm := Finset.min'_mem (failureSet U p) hS
  change s ∈ failureSet U p at hm
  have hs : ¬ IsHorizontal U s ∧ balance U (s.val + 1) < baseline U (p s) := by
    simpa [failureSet] using hm
  refine ⟨hs.1, hs.2, ?_⟩
  intro w hws hw
  by_contra hn
  have hmem : w ∈ failureSet U p := by simp [failureSet, hw, show balance U (w.val + 1) < baseline U (p w) by omega]
  have hmin := Finset.min'_le (failureSet U p) w hmem
  change s ≤ w at hmin
  have hv : s.val ≤ w.val := hmin
  omega

theorem before_first_failure {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n) {s : Fin n} (hs : ¬ IsHorizontal U s)
    (hearlier : ∀ w : Fin n, w.val < s.val → ¬ IsHorizontal U w →
      baseline U (p w) ≤ balance U (w.val + 1)) :
    ∀ k, (p s).val + 1 ≤ k → k ≤ s.val → baseline U (p s) ≤ balance U k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hstart hend
    by_cases he : k = (p s).val + 1
    · simpa [he, baseline]
    have hlt : (p s).val + 1 < k := by omega
    have hkn : k - 1 < n := by omega
    let w : Fin n := ⟨k - 1, hkn⟩
    by_cases hw : IsHorizontal U w
    · have hprev := ih (k - 1) (by omega) (by omega) (by omega)
      have step := balance_succ U hkn
      have he' : k - 1 + 1 = k := by omega
      rw [he', credit_horizontal hw] at step
      omega
    · have hbounds := KroneckerPrecursorPrefixHelpers.assignments_between hp hs
        (rfl : p s = p s) (w := w) (by dsimp [w]; omega) (by dsimp [w]; omega) hw
      change IsHorizontal U (p w) ∧ (p s).val ≤ (p w).val ∧ (p w).val < w.val at hbounds
      have hwval : w.val = k - 1 := rfl
      have hown := hearlier w (by dsimp [w]; omega) hw
      have hbase := ih ((p w).val + 1) (by rw [hwval] at hbounds; omega)
        (by omega) (by rw [hwval] at hbounds; omega)
      unfold baseline at hbase hown ⊢
      rw [hwval] at hown
      have he' : k - 1 + 1 = k := by omega
      rw [he'] at hown
      omega

theorem first_failure_contract {n : ℕ} {U : Word n} {p : Fin n → Fin n}
    (hp : ValidThrough U p n)
    (hnodes : ∀ x, IsHorizontal U x → 0 < (U x).grade → ∃ t, IsNode U p x t)
    (hS : (failureSet U p).Nonempty) :
    let s := (failureSet U p).min' hS
    let r := p s
    IsHorizontal U r ∧ ¬ IsHorizontal U s ∧ r.val < s.val ∧
    0 < (U r).grade ∧ 0 < (U s).grade ∧
    (∀ k, r.val + 1 ≤ k → k ≤ s.val →
      balance U (s.val + 1) < baseline U r ∧ baseline U r ≤ balance U k) ∧
    (∀ j : Fin n, r.val < j.val → j.val < s.val → IsHorizontal U j →
      balance U (s.val + 1) - balance U j.val < 0) ∧
    (∀ j : Fin n, r.val < j.val → j.val < s.val → ¬ IsHorizontal U j →
      (intervalVerticalCount U r.val (j.val + 1) : ℤ) -
        (intervalHorizontalGrade U r.val (j.val + 1) : ℤ) < 0) := by
  dsimp only
  set s := (failureSet U p).min' hS with hsdef
  obtain ⟨hs, hbad, hearlier⟩ := least_failure hS
  change ¬ IsHorizontal U s at hs
  change balance U (s.val + 1) < baseline U (p s) at hbad
  obtain ⟨hr, hrs, hcap, _⟩ := hp s s.isLt hs
  have hrg : 0 < (U (p s)).grade := by omega
  have hprefix := before_first_failure hp hs hearlier
  have hsbound := hprefix s.val (by omega) le_rfl
  have step := balance_succ U s.isLt
  change balance U (s.val + 1) = balance U s.val + (U s).credit at step
  have hc : (U s).credit = -(U s).grade := by
    cases he : U s with
    | H g => simp [IsHorizontal, he] at hs
    | V g => rfl
  rw [hc] at step
  have hsg : 0 < (U s).grade := by omega
  refine ⟨hr, hs, hrs, hrg, hsg, ?_, ?_, ?_⟩
  · intro k hstart hend
    exact ⟨hbad, hprefix k hstart hend⟩
  · intro j hrj hjs _
    have hj := hprefix j.val (by omega) (by omega)
    omega
  · intro j hrj hjs _
    obtain ⟨t, ht⟩ := hnodes (p s) hr hrg
    have hst := ht.last_assigned s hs rfl
    have hj := ht.horizontal_shadow_prefix hp (by omega : (p s).val < j.val + 1)
      (by omega : j.val + 1 ≤ t.val)
    omega

#print axioms crossing_nonempty
#print axioms first_crossing
#print axioms least_failure
#print axioms before_first_failure
#print axioms first_failure_contract
end
end KroneckerExplicitWitnessHelpers
