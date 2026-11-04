import KroneckerLowerEntropyKernel

/-! Transfer a positive finite lower estimate to a genuine joint lower-limit
statement. The latter is stated by eventual lower bounds, so it remains valid
without assuming boundedness above or existence of a finite entropy limit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerLowerEntropyTransfer
open Filter KroneckerLowerEntropyKernel
open scoped Topology

def lower (C q : ℝ) (a k : ℕ) : ℝ :=
  C*(256/27 : ℝ)^a*((k : ℝ)/a)^(5/2 : ℝ)*q^(k-1)

theorem lower_pos {C q : ℝ} (hC : 0 < C) (hq : 0 < q)
    (a k : ℕ) (ha : 0 < a) (hk : 0 < k) : 0 < lower C q a k := by
  unfold lower
  positivity

theorem log_lower {C q : ℝ} (hC : 0 < C) (hq : 0 < q)
    (a k : ℕ) (ha : 0 < a) (hk : 0 < k) :
    Real.log (lower C q a k)/(a : ℝ) =
      Real.log (256/27 : ℝ) + correction C q a k := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : 0 < ((k : ℝ)/a)^(5/2 : ℝ) := Real.rpow_pos_of_pos (div_pos hkp hap) _
  unfold lower correction
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hp.ne', Real.log_mul hC.ne' (by positivity),
    Real.log_pow, Real.log_pow, Real.log_rpow (div_pos hkp hap)]
  field_simp
  ring

theorem lower_log_le {C q E : ℝ} (hC : 0 < C) (hq : 0 < q)
    (a k : ℕ) (ha : 0 < a) (hk : 0 < k) (h : lower C q a k ≤ E) :
    Real.log (256/27 : ℝ) + correction C q a k ≤ Real.log E/(a : ℝ) := by
  rw [← log_lower hC hq a k ha hk]
  exact div_le_div_of_nonneg_right (Real.log_le_log (lower_pos hC hq a k ha hk) h)
    (Nat.cast_nonneg _)

/-- Equivalent to a liminf lower bound in the extended real line. The explicit
eventual formulation does not introduce a finite-limit assumption. -/
def LowerLimit {α : Type*} (l : Filter α) (f : α → ℝ) (L : ℝ) : Prop :=
  ∀ c : ℝ, c < L → ∀ᶠ i in l, c ≤ f i

variable {α : Type*} {l : Filter α} (a k : α → ℕ) (E : α → ℝ)

theorem lower_limit_of_finite_bound {C q : ℝ} (hC : 0 < C) (hq : 0 < q)
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/a i) l (𝓝 0))
    (hkpos : ∀ᶠ i in l, 1 ≤ k i)
    (hbound : ∀ᶠ i in l, lower C q (a i) (k i) ≤ E i) :
    LowerLimit l (fun i => Real.log (E i)/(a i : ℝ)) (Real.log (256/27 : ℝ)) := by
  have herror := (correction_tendsto a k ha hk hkpos C q).const_add
    (Real.log (256/27 : ℝ))
  simp only [add_zero] at herror
  intro c hc
  have hnear := herror.eventually (lt_mem_nhds hc)
  filter_upwards [hnear, hbound, hkpos, eventually_positive a ha] with i hi hb hki hai
  exact hi.le.trans (lower_log_le hC hq (a i) (k i) hai (by omega) hb)

theorem LowerLimit.le_of_tendsto {f : α → ℝ} {L K : ℝ} [l.NeBot]
    (h : LowerLimit l f L) (hK : Tendsto f l (𝓝 K)) : L ≤ K := by
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  exact _root_.ge_of_tendsto hK (h c hc)

end KroneckerLowerEntropyTransfer
