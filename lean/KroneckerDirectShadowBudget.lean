import KroneckerPublishedPositionApplication
import KroneckerCyclicCutInvariance

/-! Direct decomposition of a compatible grading at a minimum of its debt walk.
No published positioning assertion is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace KroneckerDirectShadowBudget
open KroneckerStack KroneckerCompatibility KroneckerSourceIntervalCounts
open KroneckerSourceCompatibility KroneckerSourceHorizontalShadow
open KroneckerSourcePrefixBounds KroneckerSourcePeriodicSums

def cost (E : ℕ → Edge) (d₁ d₂ : ℤ) (s t : ℕ) : ℤ :=
  d₁ * hWeight E s t - d₂ * vWeight E s t

def Clean (E : ℕ → Edge) (s : ℕ) : Prop :=
  ∀ i, i ≤ s → debt E s ≤ debt E i

def LinearSupport (E : ℕ → Edge) (N : ℕ) : Prop :=
  ∀ v, v < N → PositiveV E v →
    ∃ u, u < v ∧ PositiveH E u ∧ Active E u v

def ZeroOn (E : ℕ → Edge) (s t : ℕ) : Prop :=
  ∀ i, s ≤ i → i < t → (E i).grade = 0

theorem cost_add (E : ℕ → Edge) (d₁ d₂ : ℤ) {s u t : ℕ}
    (hs : s ≤ u) (ht : u ≤ t) :
    cost E d₁ d₂ s t = cost E d₁ d₂ s u + cost E d₁ d₂ u t := by
  unfold cost
  rw [← horizontal_weight_add E s u t hs ht,
    ← vertical_weight_add E s u t hs ht]
  ring

theorem cost_zero_step {E : ℕ → Edge} {d₁ d₂ : ℤ} {s : ℕ}
    (hz : (E s).grade = 0) : cost E d₁ d₂ s (s+1) = 0 := by
  cases he : E s <;>
    simp_all [cost, hWeight, vWeight, hGrade, vGrade, Edge.grade]

theorem clean_zero_step {E : ℕ → Edge} {s : ℕ}
    (hc : Clean E s) (hz : (E s).grade = 0) : Clean E (s+1) := by
  have hd : debt E (s+1) ≤ debt E s := by
    cases he : E s <;> simp_all [debt_step, Edge.debtChange, Edge.grade]
  intro i hi
  by_cases his : i ≤ s
  · exact hd.trans (hc i his)
  · have : i = s+1 := by omega
    subst i
    exact le_rfl

theorem clean_closure {E : ℕ → Edge} {s e : ℕ}
    (hc : Clean E s) (hp : PositiveH E s) (hf : FirstClosure E s e) :
    Clean E (e+1) := by
  have hr := first_return_debt hp hf
  have ha := (shadow_iff_active hp).mp hf.2.2.2
  intro i hi
  rw [hr.1]
  by_cases his : i ≤ s
  · exact hc i his
  · by_cases hie : i ≤ e
    · exact (ha i (by omega) hie).le
    · have : i = e+1 := by omega
      subst i
      exact hr.1.ge

theorem clean_vertical_zero {E : ℕ → Edge} {N s : ℕ}
    (hs : s < N) (hc : Clean E s) (ht : LinearSupport E N)
    (hv : Vertical E s) : (E s).grade = 0 := by
  obtain ⟨g, hg⟩ := hv
  by_contra hn
  have hgp : 0 < g := Nat.pos_of_ne_zero (by simpa [hg, Edge.grade] using hn)
  have hp : PositiveV E s := ⟨g, hgp, hg⟩
  obtain ⟨u, hu, _, ha⟩ := ht s hs hp
  have hlow := hc u hu.le
  have hhigh := ha s hu le_rfl
  omega

theorem closure_before_end {E : ℕ → Edge} {N s : ℕ}
    (hs : s < N) (hp : PositiveH E s)
    (hmin : ∀ i, i ≤ N → debt E N ≤ debt E i) :
    ∃ e, e < N ∧ FirstClosure E s e := by
  have hi := KroneckerSourceIntervalCounts.debt_interval E s N hs.le
  have hm := hmin s hs.le
  have ht : hWeight E s (s + (N-s)) ≤
      KroneckerSourceIntervalCounts.vCount E s (s + (N-s)) := by
    rw [Nat.add_sub_of_le hs.le]
    omega
  obtain ⟨e, he, hf⟩ := first_exists (show 1 ≤ N-s by omega) hp ht
  exact ⟨e, by omega, hf⟩

theorem coordinate_interval {E : ℕ → Edge} {d₁ d₂ : ℤ} {φ : ℕ → ℤ}
    (hstep : ∀ i, φ (i+1) = φ i + d₂ * hFlag (E i) - d₁ * vFlag (E i))
    {s t : ℕ} (hst : s ≤ t) :
    φ t - φ s = d₂ * KroneckerSourceIntervalCounts.hCount E s t -
      d₁ * KroneckerSourceIntervalCounts.vCount E s t := by
  have hp : ∀ n, φ n = φ 0 + d₂ * walk hFlag E n - d₁ * walk vFlag E n := by
    intro n
    induction n with
    | zero => simp [walk]
    | succ n ih => rw [hstep, ih, walk, walk]; ring
  rw [hp t, hp s]
  unfold KroneckerSourceIntervalCounts.hCount KroneckerSourceIntervalCounts.vCount
  rw [interval_walk _ E s t hst, interval_walk _ E s t hst]
  ring

theorem shadow_cost_bound {E : ℕ → Edge} {N : ℕ} {d₁ d₂ : ℤ} {φ : ℕ → ℤ}
    (hd₂ : 0 < d₂)
    (hstep : ∀ i, φ (i+1) = φ i + d₂ * hFlag (E i) - d₁ * vFlag (E i))
    (hc : LinearCompatible E N) {s e : ℕ} (he : e < N)
    (hp : PositiveH E s) (hf : FirstClosure E s e) :
    φ s + d₁ + d₂ - φ e ≤ cost E d₁ d₂ s (e+1) := by
  have hse : s < e := by
    have hle := hf.1
    obtain ⟨g, _, hg⟩ := hp
    obtain ⟨k, hk⟩ := hf.2.1
    by_contra h
    have : s = e := by omega
    subst e
    rw [hg] at hk
    contradiction
  have hb := linear_implies_baselines hc s e hse he hp hf.2.1
    ((shadow_iff_active hp).mp hf.2.2.2)
  have hb' := KroneckerSourceIntervalCounts.balance_interval E s (e+1) (by omega)
  have hsstep : balance E (s+1) = balance E s + 1 := by
    obtain ⟨g, _, hg⟩ := hp
    simp [balance_step, hg, Edge.credit]
  have hcoord := coordinate_interval hstep (show s ≤ e+1 by omega)
  have hestep : φ (e+1) = φ e - d₁ := by
    obtain ⟨g, hg⟩ := hf.2.1
    simp [hstep, hg, hFlag, vFlag]
  have heq := hf.2.2.1
  unfold HEquality at heq
  rw [heq] at hcoord
  unfold cost
  have hbal : 0 ≤ KroneckerSourceIntervalCounts.hCount E s (e+1) -
      vWeight E s (e+1) - 1 := by omega
  have hmul := mul_nonneg hd₂.le hbal
  nlinarith

theorem shadow_cost_positive {E : ℕ → Edge} {N : ℕ} {d₁ d₂ : ℤ} {φ : ℕ → ℤ}
    (hd₂ : 0 < d₂)
    (hstep : ∀ i, φ (i+1) = φ i + d₂ * hFlag (E i) - d₁ * vFlag (E i))
    (hbound : ∀ i, 0 ≤ φ i ∧ φ i < d₁+d₂)
    (hc : LinearCompatible E N) {s e : ℕ} (he : e < N)
    (hp : PositiveH E s) (hf : FirstClosure E s e) :
    1 ≤ cost E d₁ d₂ s (e+1) := by
  have h := shadow_cost_bound hd₂ hstep hc he hp hf
  have hs := (hbound s).1
  have he := (hbound e).2
  omega

/-- Every complete supported shadow has positive cost. At total cost one,
there is one complete shadow and every grade outside it is zero. -/
theorem budget_decomposition {E : ℕ → Edge} {N : ℕ} {d₁ d₂ : ℤ}
    (hsupp : LinearSupport E N)
    (hmin : ∀ i, i ≤ N → debt E N ≤ debt E i)
    (hblock : ∀ s e, e < N → PositiveH E s → FirstClosure E s e →
      1 ≤ cost E d₁ d₂ s (e+1))
    (s : ℕ) (hs : s ≤ N) (hclean : Clean E s) :
    0 ≤ cost E d₁ d₂ s N ∧
    (cost E d₁ d₂ s N = 0 → ZeroOn E s N) ∧
    (cost E d₁ d₂ s N = 1 →
      ∃ u e, s ≤ u ∧ e < N ∧ PositiveH E u ∧ FirstClosure E u e ∧
        cost E d₁ d₂ u (e+1) = 1 ∧ ZeroOn E s u ∧ ZeroOn E (e+1) N) := by
  generalize hn : N-s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hsn : s = N
    · subst s
      simp only [cost, hWeight, vWeight, Finset.Ico_self, Finset.sum_empty,
        mul_zero, sub_self, le_refl, zero_ne_one, false_implies, and_true, true_and]
      intro _ i hi hiN
      omega
    have hsN : s < N := by omega
    by_cases hp : PositiveH E s
    · obtain ⟨e, he, hf⟩ := closure_before_end hsN hp hmin
      have hse : s < e+1 := by have := hf.1; omega
      have hend := clean_closure hclean hp hf
      have ht := ih (N-(e+1)) (by omega) (e+1) (by omega) hend rfl
      have hb := hblock s e he hp hf
      have hadd := cost_add E d₁ d₂ hse.le (by omega : e+1 ≤ N)
      refine ⟨by omega, ?_, ?_⟩
      · intro hz
        omega
      · intro hone
        have hz : cost E d₁ d₂ (e+1) N = 0 := by omega
        refine ⟨s, e, le_rfl, he, hp, hf, by omega, ?_, ht.2.1 hz⟩
        intro i hsi his
        omega
    · have hz : (E s).grade = 0 := by
        cases he : E s with
        | H g =>
          have : g = 0 := by
            by_contra h
            exact hp ⟨g, Nat.pos_of_ne_zero h, he⟩
          simp [this, Edge.grade]
        | V g => simpa only [he] using clean_vertical_zero (E := E) hsN hclean hsupp ⟨g, he⟩
      have ht := ih (N-(s+1)) (by omega) (s+1) (by omega)
        (clean_zero_step hclean hz) rfl
      have hadd := cost_add E d₁ d₂ (Nat.le_succ s) (by omega : s+1 ≤ N)
      have heq : cost E d₁ d₂ s N = cost E d₁ d₂ (s+1) N := by
        rw [cost_zero_step hz, zero_add] at hadd
        exact hadd
      refine ⟨by omega, ?_, ?_⟩
      · intro hzero i hsi hiN
        by_cases hi : i = s
        · simpa [hi] using hz
        · exact ht.2.1 (by omega) i (by omega) hiN
      · intro hone
        obtain ⟨u,e,hu,he,hpu,hfu,hcu,hpre,hpost⟩ := ht.2.2 (by omega)
        refine ⟨u,e,by omega,he,hpu,hfu,hcu,?_,hpost⟩
        intro i hsi hiu
        by_cases hi : i = s
        · simpa [hi] using hz
        · exact hpre i (by omega) hiu

end KroneckerDirectShadowBudget
