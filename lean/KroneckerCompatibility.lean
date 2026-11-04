import KroneckerStack

/-!
Compatibility on a cut path, with the endpoint exclusions retained.
`balance` is #H minus the sum of V grades; `debt` is the sum of H
grades minus #V. Indices denote edges and trace values denote vertices.
This file does not assume the manuscript's stack/compatibility lemma.
-/
set_option autoImplicit false
namespace KroneckerCompatibility
open KroneckerStack

def walk (f : Edge → ℤ) (E : ℕ → Edge) : ℕ → ℤ
  | 0 => 0
  | k+1 => walk f E k + f (E k)

def balance (E : ℕ → Edge) : ℕ → ℤ := walk Edge.credit E
def debt (E : ℕ → Edge) : ℕ → ℤ := walk Edge.debtChange E

def Horizontal (E : ℕ → Edge) (i : ℕ) : Prop := ∃ g, E i = .H g
def Vertical (E : ℕ → Edge) (i : ℕ) : Prop := ∃ g, E i = .V g
def PositiveH (E : ℕ → Edge) (i : ℕ) : Prop := ∃ g, 0 < g ∧ E i = .H g
def PositiveV (E : ℕ → Edge) (i : ℕ) : Prop := ∃ g, 0 < g ∧ E i = .V g

/-- A horizontal grading witness occurs at a vertical edge strictly before v. -/
def HWitness (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ∃ e, u < e ∧ e < v ∧ Vertical E e ∧ debt E (e+1) = debt E u

/-- A vertical grading witness occurs at a horizontal edge strictly after u. -/
def VWitness (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ∃ e, u < e ∧ e < v ∧ Horizontal E e ∧ balance E e = balance E (v+1)

/-- The shadow beginning at u has not closed before edge v. -/
def Active (E : ℕ → Edge) (u v : ℕ) : Prop :=
  ∀ k, u < k → k ≤ v → debt E u < debt E k

def LinearCompatible (E : ℕ → Edge) (n : ℕ) : Prop :=
  ∀ u v, u < v → v < n → PositiveH E u → PositiveV E v →
    HWitness E u v ∨ VWitness E u v

def ShadowBaselines (E : ℕ → Edge) (n : ℕ) : Prop :=
  ∀ u v, u < v → v < n → PositiveH E u → Vertical E v → Active E u v →
    balance E (u+1) ≤ balance E (v+1)

theorem balance_step (E : ℕ → Edge) (k : ℕ) :
    balance E (k+1) = balance E k + (E k).credit := rfl

theorem debt_step (E : ℕ → Edge) (k : ℕ) :
    debt E (k+1) = debt E k + (E k).debtChange := rfl

/-- A downward crossing of an integer debt level occurs at a vertical edge. -/
theorem debt_crossing (E : ℕ → Edge) (z : ℤ) {s t : ℕ}
    (hst : s ≤ t) (hs : z < debt E s) (ht : debt E t ≤ z) :
    ∃ e, s ≤ e ∧ e < t ∧ Vertical E e ∧ debt E (e+1) = z := by
  induction t with
  | zero =>
    have : s = 0 := by omega
    subst s
    omega
  | succ t ih =>
    have hst' : s ≤ t := by
      by_contra h
      have : s = t+1 := by omega
      subst s
      omega
    by_cases h : debt E t ≤ z
    · obtain ⟨e, he, het, hv, hd⟩ := ih hst' h
      exact ⟨e, he, by omega, hv, hd⟩
    · cases he : E t with
      | H g => simp only [debt_step, he, Edge.debtChange] at ht; omega
      | V g =>
        refine ⟨t, hst', by omega, ⟨g, he⟩, ?_⟩
        simp only [debt_step, he, Edge.debtChange] at ht ⊢
        omega

/-- An upward crossing of an integer balance level occurs at a horizontal edge. -/
theorem balance_crossing (E : ℕ → Edge) (z : ℤ) {s t : ℕ}
    (hst : s ≤ t) (hs : balance E s ≤ z) (ht : z < balance E t) :
    ∃ e, s ≤ e ∧ e < t ∧ Horizontal E e ∧ balance E e = z := by
  induction t with
  | zero =>
    have : s = 0 := by omega
    subst s
    omega
  | succ t ih =>
    have hst' : s ≤ t := by
      by_contra h
      have : s = t+1 := by omega
      subst s
      omega
    by_cases h : z < balance E t
    · obtain ⟨e, he, het, hv, hd⟩ := ih hst' h
      exact ⟨e, he, by omega, hv, hd⟩
    · cases he : E t with
      | H g =>
        refine ⟨t, hst', by omega, ⟨g, he⟩, ?_⟩
        simp only [balance_step, he, Edge.credit] at ht
        omega
      | V g => simp only [balance_step, he, Edge.credit] at ht; omega

theorem active_no_hwitness {E : ℕ → Edge} {u v : ℕ}
    (ha : Active E u v) : ¬ HWitness E u v := by
  rintro ⟨e, hue, hev, _, he⟩
  have := ha (e+1) (by omega) (by omega)
  omega

theorem active_of_no_hwitness {E : ℕ → Edge} {u v : ℕ}
    (hu : PositiveH E u) (hn : ¬ HWitness E u v) : Active E u v := by
  obtain ⟨g, hg, he⟩ := hu
  intro k huk hkv
  by_contra h
  have hs : debt E u < debt E (u+1) := by rw [debt_step, he]; simp [Edge.debtChange]; omega
  obtain ⟨e, hle, hlt, hv, hd⟩ := debt_crossing E (debt E u) (by omega : u+1 ≤ k) hs (by omega)
  exact hn ⟨e, by omega, by omega, hv, hd⟩

theorem baselines_imply_linear {E : ℕ → Edge} {n : ℕ}
    (hb : ShadowBaselines E n) : LinearCompatible E n := by
  intro u v huv hvn hu hv
  by_cases hw : HWitness E u v
  · exact Or.inl hw
  · right
    obtain ⟨g, hg, he⟩ := hv
    have hlow := hb u v huv hvn hu ⟨g, he⟩ (active_of_no_hwitness hu hw)
    have hhigh : balance E (v+1) < balance E v := by
      rw [balance_step, he]; simp only [Edge.credit]; omega
    obtain ⟨e, hle, hlt, hh, hz⟩ :=
      balance_crossing E (balance E (v+1)) (by omega : u+1 ≤ v) hlow hhigh
    exact ⟨e, by omega, hlt, hh, hz⟩

theorem linear_implies_baselines {E : ℕ → Edge} {n : ℕ}
    (hc : LinearCompatible E n) : ShadowBaselines E n := by
  intro u v huv hvn hu hv ha
  induction v using Nat.strong_induction_on with
  | h v ih =>
    have hprefix : ∀ k, u+1 ≤ k → k ≤ v → balance E (u+1) ≤ balance E k := by
      intro k hstart
      induction k, hstart using Nat.le_induction with
      | base => intro _; exact le_refl _
      | succ k hstart hk =>
        intro hkv
        cases he : E k with
        | H g =>
          have hprev := hk (by omega)
          rw [balance_step E k, he]
          simp only [Edge.credit]
          omega
        | V g =>
          apply ih k (by omega) (by omega) (by omega) ⟨g, he⟩
          intro j huj hjk
          exact ha j huj (by omega)
    obtain ⟨g, he⟩ := hv
    by_cases hg : g=0
    · have hp := hprefix v (by omega) (by omega)
      rw [balance_step E v, he, hg]
      simpa [Edge.credit] using hp
    · have hp : PositiveV E v := ⟨g, by omega, he⟩
      rcases hc u v huv hvn hu hp with hw | hw
      · exact False.elim (active_no_hwitness ha hw)
      · obtain ⟨e, hue, hev, _, heq⟩ := hw
        rw [← heq]
        exact hprefix e (by omega) (by omega)

theorem linear_iff_baselines (E : ℕ → Edge) (n : ℕ) :
    LinearCompatible E n ↔ ShadowBaselines E n :=
  ⟨linear_implies_baselines, baselines_imply_linear⟩

/-- The cut lies just before the first edge of one complete horizontal shadow. -/
def RootComponent (E : ℕ → Edge) (n : ℕ) : Prop :=
  0 < n ∧ PositiveH E 0 ∧ debt E n = 0 ∧
    ∀ k, 0 < k → k < n → 0 < debt E k

/-- A first return to debt zero gives the positive proper prefixes used
by `RootComponent`; this is a consequence of unit downward steps. -/
theorem root_iff_first_return (E : ℕ → Edge) (n : ℕ) :
    RootComponent E n ↔ 0<n ∧ PositiveH E 0 ∧ debt E n=0 ∧
      ∀ k, 0<k → k<n → debt E k≠0 := by
  constructor
  · rintro ⟨hn,hh,hz,hp⟩
    exact ⟨hn,hh,hz,fun k hk hkn => ne_of_gt (hp k hk hkn)⟩
  · rintro ⟨hn,hh,hz,hp⟩
    refine ⟨hn,hh,hz,?_⟩
    intro k hk hkn
    by_contra h
    obtain ⟨g,hg,he⟩ := hh
    have hd : 0 < debt E 1 := by simp [debt,walk,he,Edge.debtChange]; omega
    obtain ⟨e,hle,hlt,_,heq⟩ := debt_crossing E 0 (by omega : 1≤k) hd (by omega)
    exact hp (e+1) (by omega) (by omega) heq

/-- Witnesses are on the inclusive cyclic subpath. E may be taken to be the
periodic extension of the finite word; the wrapping witness proved below
already occurs before the cut, so its existence is independent of the tail. -/
def CyclicCompatible (E : ℕ → Edge) (n : ℕ) : Prop :=
  ∀ u v, u < n → v < n → PositiveH E u → PositiveV E v →
    HWitness E u (if u ≤ v then v else v+n) ∨
    VWitness E u (if u ≤ v then v else v+n)

theorem wrapping_witness {E : ℕ → Edge} {n u v : ℕ}
    (hr : RootComponent E n) (hun : u < n)
    (hu : PositiveH E u) : HWitness E u (v+n) := by
  have hdu : 0 ≤ debt E u := by
    by_cases h : u=0
    · subst u; simp [debt, walk]
    · exact le_of_lt (hr.2.2.2 u (by omega) hun)
  obtain ⟨g, hg, he⟩ := hu
  have hd : debt E u < debt E (u+1) := by
    rw [debt_step, he]; simp only [Edge.debtChange]; omega
  obtain ⟨e, hle, hlt, hv, hz⟩ := debt_crossing E (debt E u)
    (by omega : u+1 ≤ n) hd (by rw [hr.2.2.1]; exact hdu)
  exact ⟨e, by omega, by omega, hv, hz⟩

theorem cyclic_iff_linear {E : ℕ → Edge} {n : ℕ}
    (hr : RootComponent E n) : CyclicCompatible E n ↔ LinearCompatible E n := by
  constructor
  · intro hc u v huv hvn hu hv
    simpa [ite_eq_left (by omega : u ≤ v)] using hc u v (by omega) hvn hu hv
  · intro hc u v hun hvn hu hv
    by_cases h : u ≤ v
    · have hne : u ≠ v := by
        intro heq; subst v
        obtain ⟨g, _, hg⟩ := hu
        obtain ⟨j, _, hj⟩ := hv
        rw [hg] at hj
        cases hj
      simpa [ite_eq_left h] using hc u v (by omega) hvn hu hv
    · simpa [ite_eq_right h] using
        (Or.inl (wrapping_witness hr hun hu) :
          HWitness E u (v+n) ∨ VWitness E u (v+n))

theorem cyclic_iff_shadow_baselines {E : ℕ → Edge} {n : ℕ}
    (hr : RootComponent E n) : CyclicCompatible E n ↔ ShadowBaselines E n :=
  (cyclic_iff_linear hr).trans (linear_iff_baselines E n)

def intervalSum (f : Edge → ℤ) (E : ℕ → Edge) (s len : ℕ) : ℤ :=
  ∑ j ∈ Finset.range len, f (E (s+j))

def hCount : Edge → ℤ | .H _ => 1 | .V _ => 0
def vCount : Edge → ℤ | .H _ => 0 | .V _ => 1
def hGrade : Edge → ℤ | .H g => g | .V _ => 0
def vGrade : Edge → ℤ | .H _ => 0 | .V g => g

theorem walk_interval (f : Edge → ℤ) (E : ℕ → Edge) (s len : ℕ) :
    walk f E (s+len) - walk f E s = intervalSum f E s len := by
  induction len with
  | zero => simp [intervalSum]
  | succ len ih =>
    rw [Nat.add_succ, walk]
    simp only [intervalSum, Finset.sum_range_succ] at ih ⊢
    omega

theorem debt_interval (E : ℕ → Edge) (s len : ℕ) :
    debt E (s+len) - debt E s =
      intervalSum hGrade E s len - intervalSum vCount E s len := by
  rw [debt, walk_interval]
  simp only [intervalSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases E (s+i) <;> simp [Edge.debtChange, hGrade, vCount]

theorem balance_interval (E : ℕ → Edge) (s len : ℕ) :
    balance E (s+len) - balance E s =
      intervalSum hCount E s len - intervalSum vGrade E s len := by
  rw [balance, walk_interval]
  simp only [intervalSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases E (s+i) <;> simp [Edge.credit, hCount, vGrade]

/-- This is the equality of horizontal grades and vertical-edge counts on
the inclusive interval from u to e used in the manuscript definition. -/
theorem hwitness_counts (E : ℕ → Edge) (u v : ℕ) :
    HWitness E u v ↔ ∃ e, u < e ∧ e < v ∧ Vertical E e ∧
      intervalSum hGrade E u (e+1-u) = intervalSum vCount E u (e+1-u) := by
  constructor <;> rintro ⟨e, hue, hev, hh, hz⟩ <;>
    refine ⟨e, hue, hev, hh, ?_⟩
  all_goals
    have hi := debt_interval E u (e+1-u)
    have heq : u+(e+1-u)=e+1 := by omega
    rw [heq] at hi
    omega

/-- This is the equality of horizontal-edge counts and vertical grades on
the inclusive interval from e to v used in the manuscript definition. -/
theorem vwitness_counts (E : ℕ → Edge) (u v : ℕ) :
    VWitness E u v ↔ ∃ e, u < e ∧ e < v ∧ Horizontal E e ∧
      intervalSum hCount E e (v+1-e) = intervalSum vGrade E e (v+1-e) := by
  constructor <;> rintro ⟨e, hue, hev, hh, hz⟩ <;>
    refine ⟨e, hue, hev, hh, ?_⟩
  all_goals
    have hi := balance_interval E e (v+1-e)
    have heq : e+(v+1-e)=v+1 := by omega
    rw [heq] at hi
    omega

end KroneckerCompatibility
