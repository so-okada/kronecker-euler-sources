import KroneckerReductionIndexHelpers
import KroneckerEndpointFoldHelpers
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Finite words of exchange and central reflection, with their exact matrix
coefficients, positive scale factors and action on actual dimension pairs. -/
set_option autoImplicit false
noncomputable section
open Matrix Filter
open scoped Topology
namespace KroneckerReductionWordHelpers
open KroneckerEndpointRoots

inductive Step where | swap | central
  deriving DecidableEq

def stepMat {α : Type*} [Ring α] (m : α) : Step → Matrix (Fin 2) (Fin 2) α
  | .swap => !![0, 1; 1, 0]
  | .central => !![1, 0; m, -1]

def wordMat {α : Type*} [Ring α] (m : α) : List Step → Matrix (Fin 2) (Fin 2) α
  | [] => 1
  | s :: ws => wordMat m ws * stepMat m s

theorem wordMat_append {α : Type*} [Ring α] (m : α) (u v : List Step) :
    wordMat m (u++v) = wordMat m v * wordMat m u := by
  induction u with
  | nil => simp [wordMat]
  | cons s u ih => simp only [List.cons_append, wordMat, ih, mul_assoc]

theorem wordMat_cast (m : ℤ) (w : List Step) :
    (wordMat m w).map (Int.castRingHom ℝ) = wordMat (m : ℝ) w := by
  induction w with
  | nil => simp [wordMat]
  | cons s w ih =>
    rw [wordMat, Matrix.map_mul, ih, wordMat]
    congr 1
    cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [stepMat]

def pair (a b : ℝ) : Fin 2 → ℝ := ![a,b]

theorem swap_pair (m a b : ℝ) : stepMat m .swap *ᵥ pair a b = pair b a := by
  ext i; fin_cases i <;> simp [stepMat, pair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem central_pair (m a b : ℝ) :
    stepMat m .central *ᵥ pair a b = pair a (m*a-b) := by
  ext i; fin_cases i <;> simp [stepMat, pair, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

def Good (m : ℝ) (v : Fin 2 → ℝ) : Prop :=
  0 < v 0 ∧ v 1/v 0 ∈ Set.Ioo (lowerRoot m) (upperRoot m)

theorem good_step (m : ℝ) (hm : 2 < m) (s : Step) (v : Fin 2 → ℝ)
    (hv : Good m v) : Good m (stepMat m s *ᵥ v) := by
  have he : v = pair (v 0) (v 1) := by ext i; fin_cases i <;> rfl
  have hv0 := hv.1
  have hv1 : 0 < v 1 := (div_pos_iff.mp ((lowerRoot_positive hm).trans hv.2.1)).resolve_right
    (fun h => (not_lt_of_ge hv0.le h.2)) |>.1
  cases s
  · rw [he, swap_pair]
    refine ⟨hv1, ?_⟩
    simpa [pair, KroneckerSlopeSymmetry.exchange, one_div, inv_div] using
      KroneckerSlopeSymmetry.exchange_mem_interior hm hv.2
  · rw [he, central_pair]
    refine ⟨hv0, ?_⟩
    have h := KroneckerSlopeSymmetry.reflect_mem_interior hm hv.2
    convert h using 1
    simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one,
      KroneckerSlopeSymmetry.reflect]
    field_simp

theorem good_word (m : ℝ) (hm : 2 < m) (w : List Step) (v : Fin 2 → ℝ)
    (hv : Good m v) : Good m (wordMat m w *ᵥ v) := by
  induction w generalizing v with
  | nil => simpa [wordMat] using hv
  | cons s w ih =>
    rw [wordMat, ← Matrix.mulVec_mulVec]
    exact ih _ (good_step m hm s v hv)

def scale (m : ℝ) (w : List Step) (t : ℝ) : ℝ :=
  wordMat m w 0 0 + wordMat m w 0 1*t

def slope (m : ℝ) (w : List Step) (t : ℝ) : ℝ :=
  (wordMat m w 1 0 + wordMat m w 1 1*t)/scale m w t

theorem scale_slope (m : ℝ) (hm : 2 < m) (w : List Step) (t : ℝ)
    (ht : t ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    0 < scale m w t ∧ slope m w t ∈ Set.Ioo (lowerRoot m) (upperRoot m) := by
  have h := good_word m hm w (pair 1 t) ⟨by norm_num [pair], by simpa [pair] using ht⟩
  simpa [Good, scale, slope, pair, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

theorem continuous_scale (m : ℝ) (w : List Step) : Continuous (scale m w) := by
  unfold scale
  fun_prop

theorem continuous_slope (m : ℝ) (hm : 2 < m) (w : List Step) :
    ContinuousOn (slope m w) (Set.Ioo (lowerRoot m) (upperRoot m)) := by
  apply ContinuousOn.div
  · fun_prop
  · exact (continuous_scale m w).continuousOn
  · intro t ht
    exact ne_of_gt (scale_slope m hm w t ht).1


def stepSlope (m : ℝ) : Step → ℝ → ℝ
  | .swap, t => t⁻¹
  | .central, t => m-t

def wordSlope (m : ℝ) : List Step → ℝ → ℝ
  | [], t => t
  | s::w, t => wordSlope m w (stepSlope m s t)

theorem step_slope (m : ℝ) (s : Step) (v : Fin 2 → ℝ) (hv : v 0 ≠ 0) :
    (stepMat m s *ᵥ v) 1 / (stepMat m s *ᵥ v) 0 = stepSlope m s (v 1/v 0) := by
  have he : v = pair (v 0) (v 1) := by ext i; fin_cases i <;> rfl
  cases s
  · rw [he, swap_pair]
    simp [pair, stepSlope, inv_div]
  · rw [he, central_pair]
    simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, stepSlope]
    field_simp

theorem word_slope (m : ℝ) (hm : 2 < m) (w : List Step) (v : Fin 2 → ℝ)
    (hv : Good m v) :
    (wordMat m w *ᵥ v) 1 / (wordMat m w *ᵥ v) 0 = wordSlope m w (v 1/v 0) := by
  induction w generalizing v with
  | nil => simp [wordMat, wordSlope]
  | cons s w ih =>
    rw [wordMat, ← Matrix.mulVec_mulVec, ih _ (good_step m hm s v hv),
      step_slope m s v (ne_of_gt hv.1)]
    rfl

theorem slope_eq_wordSlope (m : ℝ) (hm : 2 < m) (w : List Step) (t : ℝ)
    (ht : t ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    slope m w t = wordSlope m w t := by
  have h := word_slope m hm w (pair 1 t) ⟨by norm_num [pair], by simpa [pair] using ht⟩
  simpa [scale, slope, pair, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

theorem wordSlope_append (m t : ℝ) (u v : List Step) :
    wordSlope m (u++v) t = wordSlope m v (wordSlope m u t) := by
  induction u generalizing t with
  | nil => rfl
  | cons s u ih => simp only [List.cons_append, wordSlope, ih]

def turns : ℕ → List Step
  | 0 => []
  | n+1 => turns n ++ [.central, .swap]

theorem matrix_turns {α : Type*} [Ring α] (m : α) (n : ℕ) :
    wordMat m (turns n) = (stepMat m .swap * stepMat m .central)^n := by
  induction n with
  | zero => simp [turns, wordMat]
  | succ n ih => simp [turns, wordMat_append, wordMat, ih, pow_succ']

theorem slope_turns (m t : ℝ) (n : ℕ) :
    wordSlope m (turns n) t = KroneckerRealReflectionIterates.orbit m t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [turns, wordSlope_append, wordSlope, stepSlope, ih,
      KroneckerRealReflectionIterates.orbit, KroneckerRealReflectionDynamics.step]

def specified (m r : ℝ) : List Step :=
  let s := KroneckerRealFundamentalRepresentative.orient r
  let n := KroneckerReductionIndexHelpers.stoppingIndex m s
  let x := KroneckerRealReflectionIterates.orbit m s n
  (if r < 1 then [.swap] else []) ++ turns n ++ (if m/2 < x then [.central] else [])

theorem specified_matrix {α : Type*} [Ring α] (m : α) (n : ℕ) (ν ε : Bool) :
    wordMat m ((if ν then [.swap] else []) ++ turns n ++ (if ε then [.central] else [])) =
      stepMat m .central^(if ε then 1 else 0) *
        (stepMat m .swap * stepMat m .central)^n * stepMat m .swap^(if ν then 1 else 0) := by
  cases ν <;> cases ε <;> simp [wordMat_append, wordMat, matrix_turns, mul_assoc]

theorem specified_slope (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    slope m (specified m r) r = KroneckerRealFundamentalRepresentative.representative hm hr := by
  rw [slope_eq_wordSlope m hm _ r hr]
  unfold specified KroneckerRealFundamentalRepresentative.representative
  rw [wordSlope_append, wordSlope_append]
  have ho : wordSlope m (if r < 1 then [.swap] else []) r =
      KroneckerRealFundamentalRepresentative.orient r := by
    by_cases h : r < 1
    · simp [h, wordSlope, stepSlope, KroneckerRealFundamentalRepresentative.orient, not_le.mpr h]
    · simp [h, wordSlope, KroneckerRealFundamentalRepresentative.orient, le_of_not_gt h]
  rw [ho, slope_turns, KroneckerReductionIndexHelpers.stopping_eq_firstHit m _ hm
    (KroneckerRealFundamentalRepresentative.orient_interior hm hr)]
  unfold KroneckerCentralStripFold.fold
  split_ifs <;> first | rfl | linarith

theorem specified_fundamental (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    slope m (specified m r) r ∈ Set.Icc 1 (m/2) := by
  rw [specified_slope m r hm hr]
  exact KroneckerRealFundamentalRepresentative.fundamental hm hr

theorem specified_identity (m r : ℝ) (hm : 2 < m)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) (hf : r ∈ Set.Icc 1 (m/2)) :
    specified m r = [] := by
  have ho : KroneckerRealFundamentalRepresentative.orient r = r := by
    simp [KroneckerRealFundamentalRepresentative.orient, hf.1]
  have hz := KroneckerReductionIndexHelpers.stopping_zero m r hm hr (by linarith [hf.2])
  simp [specified, not_lt.mpr hf.1, ho, hz, turns, KroneckerRealReflectionIterates.orbit,
    not_lt.mpr hf.2]

open KroneckerApproachingDimensionReduction KroneckerInteriorAllowedReflection
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
variable (H : ∀ m a b, Admissible (space m a b))

def applyStep (m : ℕ) (hm : 3 ≤ m) : Step → Interior H m → Interior H m
  | .swap => exchange H m hm
  | .central => central H m hm

def applyWord (m : ℕ) (hm : 3 ≤ m) : List Step → Interior H m → Interior H m
  | [], p => p
  | s::w, p => applyWord m hm w (applyStep H m hm s p)

def observed {m : ℕ} (p : Interior H m) : Fin 2 → ℝ :=
  pair (hgt H p) (hgt H p * slp H p)

theorem observed_step (m : ℕ) (hm : 3 ≤ m) (s : Step) (p : Interior H m) :
    observed H (applyStep H m hm s p) = stepMat (m : ℝ) s *ᵥ observed H p := by
  have hp := ne_of_gt (slp_pos H p)
  cases s
  · rw [applyStep, observed, observed, swap_pair]
    rw [exchange_slope, show hgt H (exchange H m hm p) = slp H p*hgt H p from
      KroneckerExchangeObservables.height_exchange H p.val]
    congr 1 <;> field_simp
  · rw [applyStep, observed, observed, central_pair, central_height, central_slope]
    congr 1
    ring

theorem observed_word (m : ℕ) (hm : 3 ≤ m) (w : List Step) (p : Interior H m) :
    observed H (applyWord H m hm w p) = wordMat (m : ℝ) w *ᵥ observed H p := by
  induction w generalizing p with
  | nil => simp [applyWord, wordMat]
  | cons s w ih => rw [applyWord, ih, observed_step, wordMat, Matrix.mulVec_mulVec]

theorem word_euler (m : ℕ) (hm : 3 ≤ m) (w : List Step) (p : Interior H m) :
    eu H (applyWord H m hm w p) = eu H p := by
  induction w generalizing p with
  | nil => rfl
  | cons s w ih =>
    rw [applyWord, ih]
    cases s
    · exact exchange_euler H m hm p
    · exact central_euler H m hm p

theorem word_ratios (m : ℕ) (hm : 3 ≤ m) (w : List Step) (p : Interior H m) :
    hgt H (applyWord H m hm w p)/hgt H p = scale m w (slp H p) ∧
    slp H (applyWord H m hm w p) = slope m w (slp H p) := by
  have h := observed_word H m hm w p
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [observed, pair, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hp := ne_of_gt (hgt_pos H p)
  have hq := ne_of_gt (hgt_pos H (applyWord H m hm w p))
  have hs := ne_of_gt (scale_slope m (by exact_mod_cast (show 2 < m by omega)) w
    (slp H p) p.property).1
  constructor
  · unfold scale
    apply (div_eq_iff hp).mpr
    nlinarith only [h0]
  · unfold slope
    apply (eq_div_iff hs).mpr
    have hh : hgt H (applyWord H m hm w p) = hgt H p * scale m w (slp H p) := by
      unfold scale
      nlinarith only [h0]
    rw [hh] at h1
    apply (mul_left_cancel₀ hp)
    nlinarith only [h1]


theorem word_limits (m : ℕ) (hm : 3 ≤ m) (w : List Step) (r : ℝ)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) (p : ℕ → Interior H m)
    (hp : Tendsto (fun n => slp H (p n)) atTop (𝓝 r)) :
    Tendsto (fun n => hgt H (applyWord H m hm w (p n))/hgt H (p n))
      atTop (𝓝 (scale m w r)) ∧
    Tendsto (fun n => slp H (applyWord H m hm w (p n))) atTop (𝓝 (slope m w r)) := by
  have hmR : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  constructor
  · have h := (continuous_scale m w).continuousAt.tendsto.comp hp
    simp only [(word_ratios H m hm w _).1]
    exact h
  · have h := ((continuous_slope m hmR w).continuousAt (isOpen_Ioo.mem_nhds hr)).tendsto.comp hp
    simp only [(word_ratios H m hm w _).2]
    exact h


/-- The approaching-pair reduction uses the fixed specified word, then the
explicit endpoint fold. The two choices depend only on `m` and `r`. -/
theorem specified_reduces (m : ℕ) (hm : 3 ≤ m) (r : ℝ)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) : Reduces H m r := by
  have hmR : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  let w := specified m r
  let ρ := slope m w r
  have hρ : ρ ∈ Set.Icc 1 ((m : ℝ)/2) := specified_fundamental m r hmR hr
  refine ⟨ρ, hρ, scale m w r, (scale_slope m hmR w r hr).1, ?_⟩
  intro p hp
  let q : ℕ → Interior H m := fun n => applyWord H m hm w (p n)
  obtain ⟨hh, hs⟩ := word_limits H m hm w r hr p hp
  change Tendsto (fun n => hgt H (q n)/hgt H (p n)) atTop (𝓝 (scale m w r)) at hh
  change Tendsto (fun n => slp H (q n)) atTop (𝓝 ρ) at hs
  have hδ := KroneckerEndpointFoldHelpers.radius_pos m ρ hmR hρ
  have hlate : ∀ᶠ n in atTop,
      |slp H (q n)-ρ| < KroneckerEndpointFoldHelpers.radius m ρ := by
    have h := hs.eventually (Metric.ball_mem_nhds ρ hδ)
    simpa only [Metric.mem_ball, Real.dist_eq] using h
  have hf : ∀ᶠ n in atTop,
      slp H (fold H m hm (q n)) ∈ Set.Icc 1 ((m : ℝ)/2) ∧
      eu H (fold H m hm (q n)) = eu H (q n) ∧
      hgt H (fold H m hm (q n))/hgt H (q n) =
        KroneckerEndpointFoldHelpers.scale ρ (slp H (q n)) ∧
      slp H (fold H m hm (q n)) =
        KroneckerEndpointFoldHelpers.foldedSlope m ρ (slp H (q n)) := by
    filter_upwards [hlate] with n hn
    exact KroneckerEndpointFoldHelpers.actual_fold_neighborhood H m hm ρ hρ (q n) hn
  obtain ⟨hhf, hsf⟩ := KroneckerEndpointFoldHelpers.fold_limits m ρ (fun n => slp H (q n)) hs
  have hhf' : Tendsto (fun n => hgt H (fold H m hm (q n))/hgt H (q n)) atTop (𝓝 1) :=
    (tendsto_congr' (hf.mono (fun _ h => h.2.2.1))).mpr hhf
  have hsf' : Tendsto (fun n => slp H (fold H m hm (q n))) atTop (𝓝 ρ) :=
    (tendsto_congr' (hf.mono (fun _ h => h.2.2.2))).mpr hsf
  refine ⟨fun n => fold H m hm (q n), hf.mono (fun _ h => h.1), ?_, ?_, hsf'⟩
  · intro n
    exact (fold_euler H m hm (q n)).trans (word_euler H m hm w (p n))
  · have hmul := hhf'.mul hh
    simp only [one_mul] at hmul
    convert hmul using 1
    funext n
    field_simp [ne_of_gt (hgt_pos H (q n))]

/-- Lemma 10.3, equations (10.4)--(10.6), with the original sequence index.
The constants precede the sequence. For `n ≥ N`, the reduced pair `q n`
has the Euler characteristic of `p n`; both limits use that same index. -/
theorem approaching_dimension_reduction_same_indices (m : ℕ) (hm : 3 ≤ m) (r : ℝ)
    (hr : r ∈ Set.Ioo (lowerRoot m) (upperRoot m)) :
    ∃ r' ∈ Set.Icc 1 ((m : ℝ)/2), ∃ c : ℝ, 0 < c ∧
    ∀ p : ℕ → KroneckerManuscriptTarget.Dimension (family H) m,
      Tendsto (fun n => KroneckerManuscriptTarget.height (p n)) atTop atTop →
      Tendsto (fun n => KroneckerManuscriptTarget.slope (p n)) atTop (𝓝 r) →
    ∃ N : ℕ, 1 ≤ N ∧
    ∃ q : ℕ → KroneckerManuscriptTarget.Dimension (family H) m,
      (∀ n, N ≤ n → KroneckerManuscriptTarget.slope (q n) ∈ Set.Icc 1 ((m : ℝ)/2)) ∧
      (∀ n, N ≤ n →
        KroneckerManuscriptTarget.euler (family H) m (q n).val.1 (q n).val.2 =
        KroneckerManuscriptTarget.euler (family H) m (p n).val.1 (p n).val.2) ∧
      Tendsto (fun n => (KroneckerManuscriptTarget.height (q n) : ℝ) /
        KroneckerManuscriptTarget.height (p n)) atTop (𝓝 c) ∧
      Tendsto (fun n => KroneckerManuscriptTarget.slope (q n)) atTop (𝓝 r') := by
  obtain ⟨r', hr', c, hc, hred⟩ := specified_reduces H m hm r hr
  refine ⟨r', hr', c, hc, ?_⟩
  intro p _hp_height hp
  have hi : ∀ᶠ n in atTop,
      KroneckerManuscriptTarget.slope (p n) ∈ Set.Ioo (lowerRoot m) (upperRoot m) :=
    hp.eventually (isOpen_Ioo.mem_nhds hr)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hi
  let p₀ : ℕ → Interior H m := fun k => ⟨p (k+N₀), hN₀ (k+N₀) (by omega)⟩
  have hp₀ : Tendsto (fun k => slp H (p₀ k)) atTop (𝓝 r) :=
    hp.comp (tendsto_add_atTop_nat N₀)
  obtain ⟨q₀, hq₀, he, hh, hs⟩ := hred p₀ hp₀
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hq₀
  let q : ℕ → KroneckerManuscriptTarget.Dimension (family H) m :=
    fun n => if N₀ ≤ n then (q₀ (n-N₀)).val else p n
  have hq (n : ℕ) (hn : N₀ ≤ n) : q n = (q₀ (n-N₀)).val := by
    simp only [q, ite_eq_left hn]
  refine ⟨max 1 (N₀+N₁), le_max_left _ _, q, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have hn₀ : N₀ ≤ n := by omega
    rw [hq n hn₀]
    exact hN₁ (n-N₀) (by omega)
  · intro n hn
    have hn₀ : N₀ ≤ n := by omega
    rw [hq n hn₀]
    simpa only [eu, p₀, Nat.sub_add_cancel hn₀] using he (n-N₀)
  · have heq : (fun n => (KroneckerManuscriptTarget.height (q n) : ℝ) /
          KroneckerManuscriptTarget.height (p n)) =ᶠ[atTop]
        (fun n => hgt H (q₀ (n-N₀)) / hgt H (p₀ (n-N₀))) := by
      filter_upwards [eventually_ge_atTop N₀] with n hn
      simp only [hq n hn, hgt, p₀, Nat.sub_add_cancel hn]
    exact (tendsto_congr' heq).mpr (hh.comp (tendsto_sub_atTop_nat N₀))
  · have heq : (fun n => KroneckerManuscriptTarget.slope (q n)) =ᶠ[atTop]
        (fun n => slp H (q₀ (n-N₀))) := by
      filter_upwards [eventually_ge_atTop N₀] with n hn
      simp only [hq n hn, slp]
    exact (tendsto_congr' heq).mpr (hs.comp (tendsto_sub_atTop_nat N₀))

end KroneckerReductionWordHelpers
