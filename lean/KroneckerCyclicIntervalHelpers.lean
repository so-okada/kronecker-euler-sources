import KroneckerPaperNodeShadow
import KroneckerCyclicCutInvariance

/-! Cyclic witnesses on every interval whose positive horizontal fibers close.
No full-root or connectedness hypothesis is used. -/
set_option autoImplicit false
namespace KroneckerCyclicIntervalHelpers
noncomputable section
open KroneckerStack KroneckerPredecessor KroneckerCompatibility

theorem intervalEdges_succ {n a k : ℕ} (hk : k < n) (ha : a ≤ k) :
    @intervalEdges n a (k + 1) = insert ⟨k, hk⟩ (intervalEdges a k) := by
  ext w
  simp only [mem_intervalEdges, Finset.mem_insert]
  constructor
  · rintro ⟨haw, hw⟩
    by_cases he : w.val = k
    · exact Or.inl (Fin.ext he)
    · exact Or.inr ⟨haw, by omega⟩
  · rintro (rfl | ⟨haw, hw⟩)
    · exact ⟨ha, Nat.lt_succ_self k⟩
    · exact ⟨haw, by omega⟩

theorem intervalHorizontalGrade_succ {n a k : ℕ} (U : Word n)
    (hk : k < n) (ha : a ≤ k) :
    intervalHorizontalGrade U a (k + 1) = intervalHorizontalGrade U a k +
      if IsHorizontal U ⟨k, hk⟩ then (U ⟨k, hk⟩).grade else 0 := by
  classical
  simp [intervalHorizontalGrade, intervalEdges_succ hk ha, add_comm]

theorem intervalVerticalCount_succ {n a k : ℕ} (U : Word n)
    (hk : k < n) (ha : a ≤ k) :
    intervalVerticalCount U a (k + 1) = intervalVerticalCount U a k +
      if ¬ IsHorizontal U ⟨k, hk⟩ then 1 else 0 := by
  classical
  simp [intervalVerticalCount, intervalEdges_succ hk ha, add_comm]

theorem debt_interval_counts (E : ℕ → Edge) {n a k : ℕ} (hak : a ≤ k) (hkn : k ≤ n) :
    debt E k - debt E a =
      (intervalHorizontalGrade (fun i : Fin n => E i.val) a k : ℤ) -
        (intervalVerticalCount (fun i : Fin n => E i.val) a k : ℤ) := by
  induction k, hak using Nat.le_induction with
  | base => simp [intervalHorizontalGrade, intervalVerticalCount]
  | succ k hak ih =>
    have hkn' : k < n := by omega
    rw [debt_step, intervalHorizontalGrade_succ _ hkn' hak,
      intervalVerticalCount_succ _ hkn' hak]
    have hprev := ih (by omega)
    cases he : E k <;> simp [IsHorizontal, he, Edge.grade, Edge.debtChange] <;> omega

/-- Every positive horizontal edge has an explicit closing vertical edge
before the end of this linear interval. -/
def PositiveClosures (E : ℕ → Edge) (n : ℕ) : Prop :=
  ∀ u, u < n → PositiveH E u → ∃ t, u < t ∧ t < n ∧ KroneckerCompatibility.Vertical E t ∧ debt E (t + 1) = debt E u

theorem nodes_close {E : ℕ → Edge} {n : ℕ} {p : Fin n → Fin n}
    (hp : ValidThrough (fun i : Fin n => E i.val) p n)
    (hnodes : ∀ x, IsHorizontal (fun i : Fin n => E i.val) x → 0 < (E x.val).grade →
      ∃ t, IsNode (fun i : Fin n => E i.val) p x t) : PositiveClosures E n := by
  intro u hun hu
  obtain ⟨g, hg, he⟩ := hu
  let x : Fin n := ⟨u, hun⟩
  have hx : IsHorizontal (fun i : Fin n => E i.val) x := by simp [IsHorizontal, x, he]
  obtain ⟨t, ht⟩ := hnodes x hx (by simpa [x, he, Edge.grade] using hg)
  have hut := ht.start_lt_end hp
  change u < t.val at hut
  have hv : KroneckerCompatibility.Vertical E t.val := by
    have hv' := ht.end_vertical
    cases hE : E t.val with
    | H a => simp [IsHorizontal, hE] at hv'
    | V a => exact ⟨a, hE⟩
  have hcounts := ht.horizontal_shadow_equality hp
  have hd := debt_interval_counts E (n := n) (a := u) (k := t.val + 1)
    (by omega) (by omega)
  change intervalVerticalCount (fun i : Fin n => E i.val) u (t.val + 1) =
    intervalHorizontalGrade (fun i : Fin n => E i.val) u (t.val + 1) at hcounts
  rw [hcounts] at hd
  exact ⟨t.val, hut, t.isLt, hv, by omega⟩

theorem walk_prefix {E F : ℕ → Edge} {n : ℕ} (h : ∀ k, k < n → F k = E k)
    (f : Edge → ℤ) {k : ℕ} (hk : k ≤ n) : walk f F k = walk f E k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [walk, walk, h k (by omega), ih (by omega)]

/-- Each individual ordered witness is transported at the same index. -/
theorem ordered_witness_at {E F : ℕ → Edge} {n u v t : ℕ}
    (h : ∀ k, k < n → F k = E k) (hu : u < t) (ht : t < v) (hv : v < n) :
    (KroneckerCompatibility.Vertical F t ∧ debt F (t + 1) = debt F u ↔
      KroneckerCompatibility.Vertical E t ∧ debt E (t + 1) = debt E u) ∧
    (KroneckerCompatibility.Horizontal F t ∧ KroneckerCompatibility.balance F t = KroneckerCompatibility.balance F (v + 1) ↔
      KroneckerCompatibility.Horizontal E t ∧ KroneckerCompatibility.balance E t = KroneckerCompatibility.balance E (v + 1)) := by
  have htu := walk_prefix h Edge.debtChange (show t + 1 ≤ n by omega)
  have huu := walk_prefix h Edge.debtChange (show u ≤ n by omega)
  have hbt := walk_prefix h Edge.credit (show t ≤ n by omega)
  have hbv := walk_prefix h Edge.credit (show v + 1 ≤ n by omega)
  simp only [KroneckerCompatibility.Vertical, KroneckerCompatibility.Horizontal, h t (by omega), debt, KroneckerCompatibility.balance,
    htu, huu, hbt, hbv, iff_self, and_self]

theorem ordered_witness_iff {E F : ℕ → Edge} {n u v : ℕ}
    (h : ∀ k, k < n → F k = E k) (huv : u ≤ v) (hv : v < n) :
    (HWitness F u v ∨ VWitness F u v) ↔ (HWitness E u v ∨ VWitness E u v) := by
  have hinterval : ∀ k, k < v - u + 1 → F (u + k) = E (u + k) := by
    intro k hk
    exact h _ (by omega)
  have hh := witness_interval_congr hinterval
  simpa only [Nat.add_sub_cancel' huv] using hh

theorem reversed_endpoint {E F : ℕ → Edge} {n N u v : ℕ}
    (hclose : PositiveClosures E n) (h : ∀ k, k < n → F k = E k)
    (hnN : n ≤ N) (hu : u < n) (hpos : PositiveH E u) :
    ∃ t, u < t ∧ t < n ∧ KroneckerCompatibility.Vertical E t ∧ KroneckerCompatibility.Vertical F t ∧
      debt E (t + 1) = debt E u ∧ debt F (t + 1) = debt F u ∧
      t < v + n ∧ t < v + N := by
  obtain ⟨t, hut, htn, htV, htd⟩ := hclose u hu hpos
  have hFV : KroneckerCompatibility.Vertical F t := by simpa only [KroneckerCompatibility.Vertical, h t htn] using htV
  have hFd : debt F (t + 1) = debt F u := by
    unfold debt
    rw [walk_prefix h Edge.debtChange (by omega), walk_prefix h Edge.debtChange (by omega)]
    exact htd
  exact ⟨t, hut, htn, htV, hFV, htd, hFd, by omega, by omega⟩

theorem restriction_compatible {E F : ℕ → Edge} {n N : ℕ}
    (hclose : PositiveClosures E n) (h : ∀ k, k < n → F k = E k)
    (hnN : n ≤ N) (hc : CyclicCompatible F N) : CyclicCompatible E n := by
  intro u v hu hv hU hV
  by_cases huv : u ≤ v
  · have hUF : PositiveH F u := by simpa only [PositiveH, h u hu] using hU
    have hVF : PositiveV F v := by simpa only [PositiveV, h v hv] using hV
    have hw := hc u v (by omega) (by omega) hUF hVF
    rw [ite_eq_left huv] at hw ⊢
    exact (ordered_witness_iff h huv hv).mp hw
  · obtain ⟨t, hut, htn, htV, htd⟩ := hclose u hu hU
    rw [ite_eq_right huv]
    exact Or.inl ⟨t, hut, by omega, htV, htd⟩

theorem zero_extension_compatible {E F : ℕ → Edge} {n N : ℕ}
    (hclose : PositiveClosures E n) (h : ∀ k, k < n → F k = E k)
    (hnN : n ≤ N) (hz : ∀ k, n ≤ k → k < N → (F k).grade = 0) :
    CyclicCompatible F N ↔ CyclicCompatible E n := by
  refine ⟨restriction_compatible hclose h hnN, ?_⟩
  intro hc u v hu hv hU hV
  have hun : u < n := by
    by_contra hn
    obtain ⟨g, hg, he⟩ := hU
    have hzero := hz u (by omega) hu
    simp [he, Edge.grade] at hzero
    omega
  have hvn : v < n := by
    by_contra hn
    obtain ⟨g, hg, he⟩ := hV
    have hzero := hz v (by omega) hv
    simp [he, Edge.grade] at hzero
    omega
  have hUE : PositiveH E u := by simpa only [PositiveH, h u hun] using hU
  have hVE : PositiveV E v := by simpa only [PositiveV, h v hvn] using hV
  by_cases huv : u ≤ v
  · have hw := hc u v hun hvn hUE hVE
    rw [ite_eq_left huv] at hw ⊢
    exact (ordered_witness_iff h huv hvn).mpr hw
  · obtain ⟨t, hut, _, _, htV, _, htd, _, htN⟩ := reversed_endpoint
      (v := v) hclose h hnN hun hUE
    rw [ite_eq_right huv]
    exact Or.inl ⟨t, hut, htN, htV, htd⟩

theorem nodes_restriction_compatible {E F : ℕ → Edge} {n N : ℕ} {p : Fin n → Fin n}
    (hp : ValidThrough (fun i : Fin n => E i.val) p n)
    (hnodes : ∀ x, IsHorizontal (fun i : Fin n => E i.val) x → 0 < (E x.val).grade →
      ∃ t, IsNode (fun i : Fin n => E i.val) p x t)
    (h : ∀ k, k < n → F k = E k) (hnN : n ≤ N) (hc : CyclicCompatible F N) :
    CyclicCompatible E n := restriction_compatible (nodes_close hp hnodes) h hnN hc

#print axioms nodes_restriction_compatible
#print axioms debt_interval_counts
#print axioms nodes_close
#print axioms ordered_witness_at
#print axioms ordered_witness_iff
#print axioms reversed_endpoint
#print axioms restriction_compatible
#print axioms zero_extension_compatible
end
end KroneckerCyclicIntervalHelpers

