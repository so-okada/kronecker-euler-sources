import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Logical and analytic parts of the Kronecker entropy argument

This is a partial formalization. `X` can be the subtype of positive coprime
dimension vectors with nonempty stable moduli. `height` is the first dimension,
`slope` is b/a, and `value` is log(E_m(a,b))/a. No construction or enumeration
of quiver moduli is asserted in this file. Such inputs occur as hypotheses.
-/

open Filter
open scoped Topology BigOperators

set_option autoImplicit false

namespace KroneckerLogic

section JointLimits

variable {X : Type*} (height : X → ℕ) (slope value : X → ℝ)

/-- The neighborhood formulation of the joint dimension/slope limit. -/
def JointLimit (r L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ x : X,
    N ≤ height x → dist (slope x) r < δ → dist (value x) L < ε

/-- Every slope neighborhood contains admissible vectors of arbitrarily
large first dimension. Nonemptiness of moduli is part of the choice of X. -/
def Approximable (r : ℝ) : Prop :=
  ∀ δ > 0, ∀ N : ℕ, ∃ x : X, N ≤ height x ∧ dist (slope x) r < δ

theorem jointLimit_sequence {r L : ℝ}
    (h : JointLimit height slope value r L) (x : ℕ → X)
    (ha : Tendsto (fun n => height (x n)) atTop atTop)
    (hr : Tendsto (fun n => slope (x n)) atTop (𝓝 r)) :
    Tendsto (fun n => value (x n)) atTop (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := h ε hε
  filter_upwards [ha.eventually (eventually_ge_atTop N),
    (Metric.tendsto_nhds.mp hr) δ hδ] with n hn hnr
  exact hN (x n) hn hnr

/-- The diagonal argument is valid without a prescribed rate of slope
convergence. -/
theorem jointLimit_of_sequences {r L : ℝ}
    (h : ∀ x : ℕ → X,
      Tendsto (fun n => height (x n)) atTop atTop →
      Tendsto (fun n => slope (x n)) atTop (𝓝 r) →
      Tendsto (fun n => value (x n)) atTop (𝓝 L)) :
    JointLimit height slope value r L := by
  classical
  by_contra hn
  simp only [JointLimit, not_forall, not_exists, not_and, not_lt] at hn
  obtain ⟨ε, hε, hbad⟩ := hn
  have hex : ∀ n : ℕ, ∃ x : X, n ≤ height x ∧
      dist (slope x) r < 1 / ((n : ℝ) + 1) ∧ ε ≤ dist (value x) L := by
    intro n
    have hnpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simpa [and_comm, and_left_comm, and_assoc] using
      hbad (1 / ((n : ℝ) + 1)) hnpos n
  choose x hx using hex
  have ha : Tendsto (fun n => height (x n)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => (hx n).1) tendsto_id
  have hr : Tendsto (fun n => slope (x n)) atTop (𝓝 r) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [(Metric.tendsto_nhds.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) δ hδ] with n hn
    have hnonneg : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hn
    exact (hx n).2.1.trans hn
  have hv := (Metric.tendsto_nhds.mp (h x ha hr)) ε hε
  obtain ⟨n, hn⟩ := hv.exists
  exact (not_lt_of_ge (hx n).2.2) hn

theorem jointLimit_iff_sequences {r L : ℝ} :
    JointLimit height slope value r L ↔
      ∀ x : ℕ → X,
        Tendsto (fun n => height (x n)) atTop atTop →
        Tendsto (fun n => slope (x n)) atTop (𝓝 r) →
        Tendsto (fun n => value (x n)) atTop (𝓝 L) :=
  ⟨fun h => jointLimit_sequence height slope value h,
    jointLimit_of_sequences height slope value⟩

/-- Continuity uses density at the comparison slope, not uniformity of
the dimension threshold as that slope varies. Works on closed intervals too. -/
theorem continuousOn_of_jointLimits {J : Set ℝ} {F : ℝ → ℝ}
    (hlim : ∀ r ∈ J, JointLimit height slope value r (F r))
    (hdense : ∀ r ∈ J, Approximable height slope r) : ContinuousOn F J := by
  apply Metric.continuousOn_iff.mpr
  intro r hr ε hε
  obtain ⟨δ, hδ, N, hN⟩ := hlim r hr (ε / 3) (by linarith)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro s hs hsr
  obtain ⟨γ, hγ, M, hM⟩ := hlim s hs (ε / 3) (by linarith)
  obtain ⟨x, hxN, hxs⟩ := hdense s hs (min γ (δ / 2))
    (lt_min hγ (by linarith)) (max N M)
  have hxsr : dist (slope x) r < δ := by
    calc
      dist (slope x) r ≤ dist (slope x) s + dist s r := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (hxs.trans_le (min_le_right _ _)) hsr
      _ = δ := by ring
  have hvr := hN x (le_trans (le_max_left _ _) hxN) hxsr
  have hvs := hM x (le_trans (le_max_right _ _) hxN)
    (hxs.trans_le (min_le_left _ _))
  calc
    dist (F s) (F r) ≤ dist (F s) (value x) + dist (value x) (F r) :=
      dist_triangle _ _ _
    _ < ε / 3 + ε / 3 := add_lt_add (by simpa [dist_comm] using hvs) hvr
    _ < ε := by linarith

end JointLimits

section CommonIntervals

/-- Common shrinking intervals give one limit for a whole nonempty family.
The index after which a sequence lies in an interval can depend on that
sequence. No continuity of the rational comparison value is assumed. -/
theorem common_intervals_limit {I : Type*} [Nonempty I] (u : I → ℕ → ℝ)
    (h : ∀ ε > 0, ∃ l b : ℝ, b - l < ε ∧
      ∀ i, ∀ᶠ n in atTop, l ≤ u i n ∧ u i n ≤ b) :
    ∃ L : ℝ, ∀ i, Tendsto (u i) atTop (𝓝 L) := by
  have hcauchy : ∀ i, CauchySeq (u i) := by
    intro i
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨l, b, hwidth, hb⟩ := h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hb i)
    refine ⟨N, ?_⟩
    intro m hm n hn
    rw [Real.dist_eq, abs_lt]
    have hm' := hN m hm
    have hn' := hN n hn
    constructor <;> linarith
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hcauchy i₀)
  refine ⟨L, fun i => ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨l, b, hwidth, hb⟩ := h (ε / 2) (by linarith)
  filter_upwards [hb i, hb i₀, (Metric.tendsto_nhds.mp hL) (ε / 2)
    (by linarith)] with n hn hn₀ hnL
  have hd : dist (u i n) (u i₀ n) < ε / 2 := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hn.1, hn.2, hn₀.1, hn₀.2]
  calc
    dist (u i n) L ≤ dist (u i n) (u i₀ n) + dist (u i₀ n) L :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hd hnL
    _ = ε := by ring

end CommonIntervals

section CentralLimit

/-- The logarithmic error is negligible even when k stays fixed. -/
theorem log_ratio_div_tendsto_zero {a k : ℕ → ℝ}
    (ha : Tendsto a atTop atTop)
    (hk : ∀ᶠ n in atTop, 1 ≤ k n ∧ k n ≤ a n) :
    Tendsto (fun n => Real.log (a n / k n) / a n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (a n) / a n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ha
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
  · filter_upwards [hk] with n hn
    have hkpos : 0 < k n := lt_of_lt_of_le zero_lt_one hn.1
    have hapos : 0 < a n := lt_of_lt_of_le hkpos hn.2
    exact div_nonneg (Real.log_nonneg ((le_div_iff₀ hkpos).mpr (by simpa using hn.2)))
      hapos.le
  · filter_upwards [hk] with n hn
    have hkpos : 0 < k n := lt_of_lt_of_le zero_lt_one hn.1
    have hapos : 0 < a n := lt_of_lt_of_le hkpos hn.2
    apply div_le_div_of_nonneg_right _ hapos.le
    apply Real.log_le_log (div_pos hapos hkpos)
    exact (div_le_iff₀ hkpos).mpr (le_mul_of_one_le_right hapos.le hn.1)

/-- The revised Section 7 lower bound and Section 8 upper bound imply
the central limit. C, q and U are logarithmic constants; no sign is needed
for them here. In particular the term involving log(q) is not discarded. -/
theorem central_squeeze {a k H : ℕ → ℝ} (L C q U : ℝ)
    (ha : Tendsto a atTop atTop)
    (hk : ∀ᶠ n in atTop, 1 ≤ k n ∧ k n ≤ a n)
    (hr : Tendsto (fun n => k n / a n) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      (C - (5 / 2 : ℝ) * Real.log (a n / k n) + (k n - 1) * q) / a n
        ≤ H n - L ∧ H n - L ≤ k n / a n * U) :
    Tendsto H atTop (𝓝 L) := by
  have hi : Tendsto (fun n => 1 / a n) atTop (𝓝 0) :=
    by simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ha
  have hc : Tendsto (fun n => C / a n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hi.const_mul C
  have hlog := log_ratio_div_tendsto_zero ha hk
  have hlow : Tendsto (fun n =>
      (C - (5 / 2 : ℝ) * Real.log (a n / k n) + (k n - 1) * q) / a n)
      atTop (𝓝 0) := by
    convert (hc.sub (hlog.const_mul (5 / 2 : ℝ))).add ((hr.sub hi).mul_const q)
      using 1
    · ext n
      ring
    · norm_num
  have hup : Tendsto (fun n => k n / a n * U) atTop (𝓝 0) := by
    simpa using hr.mul_const U
  have hzero : Tendsto (fun n => H n - L) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
      (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
  simpa using hzero.add_const L

end CentralLimit

section MatrixBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_pow_nonneg (K : Matrix ι ι ℝ) (hK : ∀ i j, 0 ≤ K i j) :
    ∀ n : ℕ, ∀ i j, 0 ≤ (K ^ n) i j := by
  intro n
  induction n with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun t _ => mul_nonneg (ih i t) (hK t j)

/-- The constant-state path replaces the removed numerical certificate. -/
theorem matrix_diagonal_lower (K : Matrix ι ι ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (i : ι) (lam : ℝ)
    (hlam : 0 ≤ lam) (hdiag : lam ≤ K i i) (n : ℕ) : lam ^ n ≤ (K ^ n) i i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply]
    calc
      lam ^ n * lam ≤ (K ^ n) i i * K i i :=
        mul_le_mul ih hdiag hlam (matrix_pow_nonneg K hK n i i)
      _ ≤ ∑ j, (K ^ n) i j * K j i :=
        Finset.single_le_sum (fun j _ => mul_nonneg
          (matrix_pow_nonneg K hK n i j) (hK j i)) (Finset.mem_univ i)

theorem matrix_total_lower (K : Matrix ι ι ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (i : ι) (lam : ℝ)
    (hlam : 0 ≤ lam) (hdiag : lam ≤ K i i) (n : ℕ) :
    lam ^ n ≤ ∑ j, ∑ k, (K ^ n) j k := by
  calc
    lam ^ n ≤ (K ^ n) i i := matrix_diagonal_lower K hK i lam hlam hdiag n
    _ ≤ ∑ k, (K ^ n) i k :=
      Finset.single_le_sum (fun k _ => matrix_pow_nonneg K hK n i k) (Finset.mem_univ i)
    _ ≤ ∑ j, ∑ k, (K ^ n) j k :=
      Finset.single_le_sum (fun j _ => Finset.sum_nonneg
        (fun k _ => matrix_pow_nonneg K hK n j k)) (Finset.mem_univ i)

end MatrixBound

theorem matrix_entry_constant : (1 / 100 : ℝ) < 1 / Real.sqrt 6885 := by
  have hsq : (Real.sqrt (6885 : ℝ)) ^ 2 = 6885 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt (6885 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 100) hpos).mpr
  nlinarith

/-- Exact constants in the positive mixed-coordinate boundary evaluation.
This checks the substitution, not the wall-crossing identity or convergence. -/
theorem boundary_constants :
    let U : ℝ := 4 / 3
    let z : ℝ := 729 / 8192
    let A := U ^ 4 * (U - 1) * (1 + 2 * U)
    let B := U ^ 11 * (U - 1)
    A * z = 11 / 32 ∧ B * z ^ 2 = 1 / 16 ∧ U ^ 6 * z = 1 / 2 ∧
      1 + A * z + B * z ^ 2 = 45 / 32 ∧
      z / (45 / 32) ^ 3 = 4 / 125 ∧
      (3 / 2 : ℝ) ^ 3 / (45 / 32) ^ 3 = 4096 / 3375 := by
  norm_num

theorem normalization_transport {a b V : ℕ → ℝ} (r L : ℝ)
    (hb : ∀ᶠ n in atTop, b n ≠ 0)
    (hscale : Tendsto (fun n => b n / a n) atTop (𝓝 r))
    (hlimit : Tendsto (fun n => V n / b n) atTop (𝓝 L)) :
    Tendsto (fun n => V n / a n) atTop (𝓝 (r * L)) := by
  apply (hscale.mul hlimit).congr'
  filter_upwards [hb] with n hn
  field_simp

section Endpoints

def Q (m a b : ℝ) : ℝ := m * a * b - a ^ 2 - b ^ 2

theorem Q_exchange (m a b : ℝ) : Q m b a = Q m a b := by unfold Q; ring

theorem Q_reflection (m a b : ℝ) : Q m a (m * a - b) = Q m a b := by
  unfold Q
  ring

theorem endpoint_identity (m u v : ℝ) :
    (m + 2) * Q m u v - (m - 2) * (u + v) ^ 2 =
      (m * v - 2 * u) * (m * u - 2 * v) := by unfold Q; ring

theorem fundamental_sum_bound {m u v : ℝ} (hm : 2 < m)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : 2 * v ≤ m * u) :
    (m - 2) * (u + v) ^ 2 ≤ (m + 2) * Q m u v := by
  have hv0 : 0 ≤ v := hu.trans huv
  have h₁ : 0 ≤ m * v - 2 * u := by nlinarith
  have h₂ : 0 ≤ m * u - 2 * v := by linarith
  have hprod := mul_nonneg h₁ h₂
  rw [← endpoint_identity] at hprod
  linarith

/-- A finite endpoint bound suffices even if the reduced dimensions do
not diverge and the number of reflections is unbounded. -/
theorem endpoint_squeeze {a ρ H : ℕ → ℝ} (m r C D : ℝ)
    (ha : Tendsto a atTop atTop) (hρ : Tendsto ρ atTop (𝓝 r))
    (hroot : m * r - 1 - r ^ 2 = 0)
    (hbound : ∀ᶠ n in atTop, 0 ≤ H n ∧
      H n ≤ C * Real.sqrt (max (m * ρ n - 1 - (ρ n) ^ 2) 0) + D / a n) :
    Tendsto H atTop (𝓝 0) := by
  have hp : Tendsto (fun n => m * ρ n - 1 - (ρ n) ^ 2) atTop (𝓝 0) := by
    simpa only [hroot] using ((hρ.const_mul m).sub_const 1).sub (hρ.pow 2)
  have hs : Tendsto (fun n => Real.sqrt (max (m * ρ n - 1 - (ρ n) ^ 2) 0))
      atTop (𝓝 0) := by
    simpa using (hp.max (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))).sqrt
  have hd : Tendsto (fun n => D / a n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ha
  have hu : Tendsto (fun n =>
      C * Real.sqrt (max (m * ρ n - 1 - (ρ n) ^ 2) 0) + D / a n) atTop (𝓝 0) := by
    simpa using (hs.const_mul C).add hd
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)

end Endpoints

section Assembly

variable {X : Type*} (height : X → ℕ) (slope value : X → ℝ)

def Approaching (r : ℝ) :=
  {x : ℕ → X // Tendsto (fun n => height (x n)) atTop atTop ∧
    Tendsto (fun n => slope (x n)) atTop (𝓝 r)}

theorem approaching_nonempty {r : ℝ} (h : Approximable height slope r) :
    Nonempty (Approaching height slope r) := by
  classical
  have hex : ∀ n : ℕ, ∃ x : X, n ≤ height x ∧
      dist (slope x) r < 1 / ((n : ℝ) + 1) := by
    intro n
    exact h _ (by positivity) n
  choose x hx using hex
  refine ⟨⟨x, ?_, ?_⟩⟩
  · exact tendsto_atTop_mono (fun n => (hx n).1) tendsto_id
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) ε hε] with n hn
    have hnonneg : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hn
    exact (hx n).2.trans hn

/-- Assembly of the closed-interval limit. The interior comparisons, the
finite bound, and the existence of dimension vectors are explicit inputs.
They are NOT axioms about Euler characteristics and are NOT proved here. -/
theorem closed_interval_limit (m l u C D : ℝ) (_hlu : l < u)
    (hl : m * l - 1 - l ^ 2 = 0) (hu : m * u - 1 - u ^ 2 = 0)
    (hdense : ∀ r ∈ Set.Icc l u, Approximable height slope r)
    (hfinite : ∀ x : X, 0 ≤ value x ∧
      value x ≤ C * Real.sqrt (max (m * slope x - 1 - (slope x) ^ 2) 0) +
        D / (height x : ℝ))
    (hcompare : ∀ r ∈ Set.Ioo l u, ∀ ε > 0, ∃ lo hi : ℝ,
      hi - lo < ε ∧ ∀ x : Approaching height slope r,
        ∀ᶠ n in atTop, lo ≤ value (x.val n) ∧ value (x.val n) ≤ hi) :
    ∃ F : ℝ → ℝ, ContinuousOn F (Set.Icc l u) ∧ F l = 0 ∧ F u = 0 ∧
      ∀ r ∈ Set.Icc l u, JointLimit height slope value r (F r) := by
  classical
  have hend : ∀ r : ℝ, m * r - 1 - r ^ 2 = 0 →
      JointLimit height slope value r 0 := by
    intro r hroot
    apply jointLimit_of_sequences height slope value
    intro x ha hr
    exact endpoint_squeeze m r C D (tendsto_natCast_atTop_atTop.comp ha) hr hroot
      (Eventually.of_forall fun n => hfinite (x n))
  have hint : ∀ r ∈ Set.Ioo l u, ∃ L, JointLimit height slope value r L := by
    intro r hr
    haveI : Nonempty (Approaching height slope r) :=
      approaching_nonempty height slope (hdense r ⟨hr.1.le, hr.2.le⟩)
    obtain ⟨L, hL⟩ := common_intervals_limit
      (fun (x : Approaching height slope r) n => value (x.val n)) (hcompare r hr)
    refine ⟨L, jointLimit_of_sequences height slope value ?_⟩
    intro x ha hs
    exact hL ⟨x, ha, hs⟩
  have hex : ∀ r : ℝ, ∃ L : ℝ,
      (r = l ∨ r = u → L = 0) ∧
      (r ∈ Set.Icc l u → JointLimit height slope value r L) := by
    intro r
    by_cases hrl : r = l
    · subst r
      exact ⟨0, fun _ => rfl, fun _ => hend l hl⟩
    by_cases hru : r = u
    · subst r
      exact ⟨0, fun _ => rfl, fun _ => hend u hu⟩
    by_cases hr : r ∈ Set.Icc l u
    · obtain ⟨L, hL⟩ := hint r ⟨lt_of_le_of_ne hr.1 (Ne.symm hrl),
        lt_of_le_of_ne hr.2 hru⟩
      exact ⟨L, fun h => (h.elim hrl hru).elim, fun _ => hL⟩
    · exact ⟨0, fun _ => rfl, fun h => (hr h).elim⟩
  choose F hF using hex
  have hlim : ∀ r ∈ Set.Icc l u, JointLimit height slope value r (F r) :=
    fun r hr => (hF r).2 hr
  exact ⟨F, continuousOn_of_jointLimits height slope value hlim hdense,
    (hF l).1 (Or.inl rfl), (hF u).1 (Or.inr rfl), hlim⟩

end Assembly

#print axioms jointLimit_iff_sequences
#print axioms continuousOn_of_jointLimits
#print axioms common_intervals_limit
#print axioms central_squeeze
#print axioms matrix_total_lower
#print axioms matrix_entry_constant
#print axioms boundary_constants
#print axioms normalization_transport
#print axioms Q_reflection
#print axioms fundamental_sum_bound
#print axioms endpoint_squeeze
#print axioms closed_interval_limit

end KroneckerLogic
