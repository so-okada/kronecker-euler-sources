import KroneckerCyclicIntervalHelpers

/-! Explicit inverse cyclic indices and zero-extension formula.
Manuscript indices are one more than these Fin values. The inverse formula
(k + N - q) % N is the nonnegative representative of the integer k-q. -/
set_option autoImplicit false
namespace KroneckerCyclicIndexHelpers
noncomputable section
open KroneckerStack KroneckerCompatibility

def eta {N : ℕ} (q j : Fin N) : Fin N :=
  ⟨(q.val + j.val) % N, Nat.mod_lt _ (by have hq := q.isLt; omega)⟩

def theta {N : ℕ} (q k : Fin N) : Fin N :=
  ⟨(k.val + N - q.val) % N, Nat.mod_lt _ (by have hq := q.isLt; omega)⟩

theorem eta_cases {N : ℕ} (q j : Fin N) :
    (eta q j).val = if q.val + j.val < N then q.val + j.val else q.val + j.val - N := by
  change (q.val + j.val) % N = _
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem theta_cases {N : ℕ} (q k : Fin N) :
    (theta q k).val = if q.val ≤ k.val then k.val - q.val else k.val + N - q.val := by
  change (k.val + N - q.val) % N = _
  split_ifs with h
  · rw [show k.val + N - q.val = (k.val - q.val) + N by omega, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (show k.val - q.val < N by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem theta_eta {N : ℕ} (q j : Fin N) : theta q (eta q j) = j := by
  apply Fin.ext
  rw [theta_cases, eta_cases]
  split_ifs <;> omega

theorem eta_theta {N : ℕ} (q k : Fin N) : eta q (theta q k) = k := by
  apply Fin.ext
  rw [eta_cases, theta_cases]
  split_ifs <;> omega

def cyclicEquiv {N : ℕ} (q : Fin N) : Fin N ≃ Fin N where
  toFun := eta q
  invFun := theta q
  left_inv := theta_eta q
  right_inv := eta_theta q

theorem cyclic_span {N : ℕ} (q i j : Fin N) :
    (if (eta q i).val ≤ (eta q j).val then (eta q j).val else (eta q j).val + N)
      - (eta q i).val = (if i.val ≤ j.val then j.val else j.val + N) - i.val :=
  cyclic_span_shift q.isLt i.isLt j.isLt

def inclusion {l N : ℕ} (hlN : l ≤ N) (i : Fin l) : Fin N := ⟨i.val, by omega⟩

def zeroGrades {l N : ℕ} (q : Fin N) (h : Fin l → ℕ) (k : Fin N) : ℕ :=
  if hk : (theta q k).val < l then h ⟨(theta q k).val, hk⟩ else 0

theorem zeroGrades_inside {l N : ℕ} (q : Fin N) (h : Fin l → ℕ)
    (hlN : l ≤ N) (i : Fin l) : zeroGrades q h (eta q (inclusion hlN i)) = h i := by
  simp [zeroGrades, theta_eta, inclusion, i.isLt]

theorem zeroGrades_outside {l N : ℕ} (q : Fin N) (h : Fin l → ℕ)
    (k : Fin N) (hk : l ≤ (theta q k).val) : zeroGrades q h k = 0 := by
  simp [zeroGrades, show ¬ (theta q k).val < l by omega]

theorem zeroGrades_positive_index {l N : ℕ} (q : Fin N) (h : Fin l → ℕ)
    (hlN : l ≤ N) (k : Fin N) (hk : 0 < zeroGrades q h k) :
    ∃ hi : (theta q k).val < l,
      eta q (inclusion hlN ⟨(theta q k).val, hi⟩) = k ∧
      0 < h ⟨(theta q k).val, hi⟩ := by
  have hi : (theta q k).val < l := by
    by_contra hn
    rw [zeroGrades_outside q h k (by omega)] at hk
    omega
  refine ⟨hi, ?_, ?_⟩
  · exact eta_theta q k
  · simpa only [zeroGrades, dite_eq_left hi] using hk

/-- Explicit zero extension of the whole graded edge, retaining its direction. -/
def zeroEdge (e : Edge) : Edge := match e with | .H _ => .H 0 | .V _ => .V 0

def zeroWord {l N : ℕ} (q : Fin N) (h : Fin l → Edge) (D : Fin N → Edge)
    (k : Fin N) : Edge :=
  if hk : (theta q k).val < l then h ⟨(theta q k).val, hk⟩ else zeroEdge (D k)

def zeroTrace {l N : ℕ} (q : Fin N) (h : Fin l → Edge) (D : Fin N → Edge)
    (k : ℕ) : Edge := zeroWord q h D ⟨k % N, Nat.mod_lt _ (by have hq := q.isLt; omega)⟩

theorem zeroTrace_periodic {l N : ℕ} (q : Fin N) (h : Fin l → Edge) (D : Fin N → Edge) :
    Function.Periodic (zeroTrace q h D) N := by
  intro k
  simp [zeroTrace]

theorem zeroTrace_inside {l N : ℕ} (q : Fin N) (h : Fin l → Edge) (D : Fin N → Edge)
    (hlN : l ≤ N) (i : Fin l) : zeroTrace q h D (q.val + i.val) = h i := by
  change zeroWord q h D (eta q (inclusion hlN i)) = h i
  simp [zeroWord, theta_eta, inclusion, i.isLt]

theorem zeroTrace_outside {l N : ℕ} (q : Fin N) (h : Fin l → Edge) (D : Fin N → Edge)
    {k : ℕ} (hlk : l ≤ k) (hkN : k < N) : (zeroTrace q h D (q.val + k)).grade = 0 := by
  let i : Fin N := ⟨k, hkN⟩
  change (zeroWord q h D (eta q i)).grade = 0
  simp only [zeroWord, theta_eta]
  have hn : ¬ i.val < l := by dsimp [i]; omega
  rw [dite_eq_right hn]
  cases D (eta q i) <;> rfl

/-- Composes the actual inverse-index zero extension, cyclic rotation and
the general interval theorem; the whole interval need not be a root node. -/
theorem explicit_zero_extension_compatible {l N : ℕ} (q : Fin N)
    (h : Fin l → Edge) (D : Fin N → Edge) (F : ℕ → Edge) (hlN : l ≤ N)
    (hF : ∀ i : Fin l, F i.val = h i)
    (hclose : KroneckerCyclicIntervalHelpers.PositiveClosures F l) :
    CyclicCompatible (zeroTrace q h D) N ↔ CyclicCompatible F l := by
  have he : ∀ k, k < l → zeroTrace q h D (q.val + k) = F k := by
    intro k hk
    rw [zeroTrace_inside q h D hlN ⟨k, hk⟩, hF ⟨k, hk⟩]
  have hz : ∀ k, l ≤ k → k < N → (zeroTrace q h D (q.val + k)).grade = 0 :=
    fun _ hk hN => zeroTrace_outside q h D hk hN
  exact (cyclicCompatible_shift (zeroTrace_periodic q h D) q.isLt).symm.trans
    (KroneckerCyclicIntervalHelpers.zero_extension_compatible hclose he hlN hz)

theorem nodes_explicit_zero_extension {l N : ℕ} (q : Fin N)
    (h : Fin l → Edge) (D : Fin N → Edge) (F : ℕ → Edge) (hlN : l ≤ N)
    (hF : ∀ i : Fin l, F i.val = h i) (p : Fin l → Fin l)
    (hp : KroneckerPredecessor.ValidThrough h p l)
    (hnodes : ∀ x, KroneckerPredecessor.IsHorizontal h x → 0 < (h x).grade →
      ∃ t, KroneckerPredecessor.IsNode h p x t) :
    CyclicCompatible (zeroTrace q h D) N ↔ CyclicCompatible F l := by
  have he : (fun i : Fin l => F i.val) = h := funext hF
  have hpF : KroneckerPredecessor.ValidThrough (fun i : Fin l => F i.val) p l := by
    rw [he]; exact hp
  have hnF : ∀ x, KroneckerPredecessor.IsHorizontal (fun i : Fin l => F i.val) x →
      0 < (F x.val).grade → ∃ t, KroneckerPredecessor.IsNode (fun i : Fin l => F i.val) p x t := by
    simpa only [hF, he] using hnodes
  exact explicit_zero_extension_compatible q h D F hlN hF
    (KroneckerCyclicIntervalHelpers.nodes_close hpF hnF)

#print axioms nodes_explicit_zero_extension
#print axioms theta_eta
#print axioms eta_theta
#print axioms cyclicEquiv
#print axioms cyclic_span
#print axioms zeroGrades_inside
#print axioms zeroGrades_outside
#print axioms zeroGrades_positive_index
#print axioms explicit_zero_extension_compatible
end
end KroneckerCyclicIndexHelpers
