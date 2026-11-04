import KroneckerFractionalPartEstimates
import KroneckerIrrationalWordSubsequence

/-! Shared phase alignment and exact prefix-discrepancy bounds for the
mechanical run-edit and binary-factor lemmas. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerPhasePrefixHelpers
open KroneckerFractionalPartEstimates KroneckerBoundaryVisits
open KroneckerVisitsConcatenation KroneckerPrefixDiscrepancy
open KroneckerMechanicalRuns KroneckerAlignedOrbitError

theorem phase_exists (p q : ℕ) (σ w u η : ℝ) (hq : 0 < q)
    (hpq : p.Coprime q) (hσ : |σ-(p : ℝ)/q| < 2/(q : ℝ)^2)
    (hu : 0 ≤ u ∧ u < 1) (hη : 0 < η) (hη1 : η < 1/4)
    (hgap : 5/(q : ℝ) < η) :
    ∃ j : ℕ, j < q ∧ |u-Int.fract (w+(j : ℝ)*σ)| < η := by
  by_contra hn
  push Not at hn
  let a := max 0 (u-η)
  let b := min 1 (u+η)
  have ha : 0 ≤ a := le_max_left _ _
  have hb : b ≤ 1 := min_le_left _ _
  have hwide : η ≤ b-a := by
    dsimp [a,b]
    rcases le_total 0 (u-η) with h | h <;>
      rcases le_total 1 (u+η) with h' | h'
    · rw [max_eq_right h, min_eq_left h']; linarith
    · rw [max_eq_right h, min_eq_right h']; linarith
    · rw [max_eq_left h, min_eq_left h']; linarith
    · rw [max_eq_left h, min_eq_right h']; linarith [hu.1]
  have hbound := empty_gap_bound p q σ w a b hq hpq hσ (by
    intro j hj n hinside
    have hf := Int.fract_nonneg (w+(j : ℝ)*σ)
    have hf1 := Int.fract_lt_one (w+(j : ℝ)*σ)
    have hn0 : n = 0 := by
      have hnl : (-1 : ℝ) < n := by linarith [hinside.1]
      have hnu : (n : ℝ) < 1 := by linarith [hinside.2]
      have hnl' : (-1 : ℤ) < n := by exact_mod_cast hnl
      have hnu' : n < (1 : ℤ) := by exact_mod_cast hnu
      omega
    subst n
    simp only [Int.cast_zero, add_zero] at hinside
    have hal : u-η ≤ a := le_max_right _ _
    have hbu : b ≤ u+η := min_le_right _ _
    have hc : |u-Int.fract (w+(j : ℝ)*σ)| < η :=
      abs_lt.mpr ⟨by linarith [hinside.2], by linarith [hinside.1]⟩
    exact (not_lt_of_ge (hn j hj)) hc)
  linarith

def leastPhase (q : ℕ) (σ w u η : ℝ)
    (h : ∃ j : ℕ, j < q ∧ |u-Int.fract (w+(j : ℝ)*σ)| < η) : ℕ :=
  Nat.find h

theorem least_phase_spec (q : ℕ) (σ w u η : ℝ)
    (h : ∃ j : ℕ, j < q ∧ |u-Int.fract (w+(j : ℝ)*σ)| < η) :
    leastPhase q σ w u η h < q ∧
    |u-Int.fract (w+(leastPhase q σ w u η h : ℝ)*σ)| < η ∧
    ∀ j < leastPhase q σ w u η h,
      ¬ (j < q ∧ |u-Int.fract (w+(j : ℝ)*σ)| < η) := by
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun j hj => Nat.find_min h hj⟩

theorem rational_visits (p q : ℕ) (σ u η : ℝ) (hq : 0 < q)
    (hpq : p.Coprime q) (hσ : |σ-(p : ℝ)/q| < 2/(q : ℝ)^2)
    (hη : 0 ≤ η) : (visits σ u (2*η) q : ℝ) ≤ 4*η*q+10 := by
  classical
  have h := near_integer_count p q σ (u+σ) η hq hpq hσ hη
  apply le_trans _ h
  unfold visits nearIntegerIndices
  rw [Nat.cast_sum, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro j hj
  have he : u+((j+1 : ℕ) : ℝ)*σ = (u+σ)+(j : ℝ)*σ := by push_cast; ring
  rw [he]
  by_cases hb : NearBoundary ((u+σ)+(j : ℝ)*σ) (2*η)
  · have hm : (0 ≤ Int.fract ((u+σ)+(j : ℝ)*σ) ∧
        Int.fract ((u+σ)+(j : ℝ)*σ) ≤ 2*η) ∨
        (1-2*η ≤ Int.fract ((u+σ)+(j : ℝ)*σ) ∧
        Int.fract ((u+σ)+(j : ℝ)*σ) < 1) := by
      rcases hb with hl | hh
      · exact Or.inl ⟨Int.fract_nonneg _, hl.le⟩
      · exact Or.inr ⟨hh.le, Int.fract_lt_one _⟩
    simp only [ite_eq_left hb, ite_eq_left hm, Nat.cast_one, le_refl]
  · simp only [ite_eq_right hb, Nat.cast_zero]
    positivity

theorem visits_le_length (σ u ε : ℝ) (n : ℕ) : visits σ u ε n ≤ n := by
  classical
  unfold visits
  calc
    _ ≤ ∑ _i ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs <;> omega
    _ = n := by simp

theorem multiple_visits (σ ε B : ℝ) (q : ℕ)
    (hb : ∀ u : ℝ, (visits σ u ε q : ℝ) ≤ B) :
    ∀ h : ℕ, ∀ u : ℝ, (visits σ u ε (h*q) : ℝ) ≤ h*B := by
  intro h
  induction h with
  | zero => intro u; simp [visits]
  | succ h ih =>
    intro u
    rw [Nat.succ_mul, visits_add, Nat.cast_add, Nat.cast_add, Nat.cast_one]
    have h₁ := ih u
    have h₂ := hb (u+(h*q : ℕ)*σ)
    nlinarith

theorem rational_visits_total (p q L : ℕ) (σ u η : ℝ) (hq : 0 < q)
    (hpq : p.Coprime q) (hσ : |σ-(p : ℝ)/q| < 2/(q : ℝ)^2)
    (hη : 0 ≤ η) :
    (visits σ u (2*η) L : ℝ) ≤ (4*η+10/(q : ℝ))*L+q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hm := multiple_visits σ (2*η) (4*η*q+10) q
    (fun v => rational_visits p q σ v η hq hpq hσ hη) (L/q) u
  have hr := visits_le_length σ (u+((L/q*q : ℕ) : ℝ)*σ) (2*η) (L%q)
  have he : L/q*q+L%q = L := by simpa only [Nat.mul_comm] using Nat.div_add_mod L q
  have hv : visits σ u (2*η) L = visits σ u (2*η) (L/q*q) +
      visits σ (u+((L/q*q : ℕ) : ℝ)*σ) (2*η) (L%q) := by
    conv_lhs => rw [← he]
    exact visits_add σ u (2*η) (L/q*q) (L%q)
  have hdiv : ((L/q : ℕ) : ℝ)*(q : ℝ) ≤ L := by
    exact_mod_cast (Nat.div_mul_le_self L q)
  have hrem : ((L%q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt L hq
  have hrr : (visits σ (u+((L/q*q : ℕ) : ℝ)*σ) (2*η) (L%q) : ℝ) ≤ ((L%q : ℕ) : ℝ) := by
    exact_mod_cast hr
  rw [hv, Nat.cast_add]
  have hc : 0 ≤ 4*η+10/(q : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdiv hc
  have hcancel : (4*η+10/(q : ℝ))*(q : ℝ) = 4*η*q+10 := by
    field_simp
  have hprod : ((L/q : ℕ) : ℝ)*(4*η*q+10) ≤ (4*η+10/(q : ℝ))*L := by
    calc
      _ = (4*η+10/(q : ℝ))*(((L/q : ℕ) : ℝ)*q) := by rw [← hcancel]; ring
      _ ≤ _ := hmul
  linarith

theorem aligned_error (s u t v η : ℝ) (L : ℕ) (hL : 0 < L)
    (huv : |u-v| < η) (hst : |s-t| < η/(2*L)) :
    |u-v|+(L : ℝ)*|s-t| < 3*η/2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have h := (lt_div_iff₀ (show (0 : ℝ) < 2*L by positivity)).mp hst
  nlinarith

theorem prefix_mass_bound (p q L : ℕ) (s u t v η : ℝ) (hq : 0 < q) (hL : 0 < L)
    (hpq : p.Coprime q) (hs : |s-(p : ℝ)/q| < 2/(q : ℝ)^2)
    (hη : 0 < η) (hη1 : η < 1/4) (huv : |u-v| < η)
    (hst : |s-t| < η/(2*L)) (hbig : 20/η < q) (hsize : (q : ℝ) ≤ η*L) :
    (∑ i ∈ Finset.range L, |discrepancy s u t v (i+1)|) ≤ (11/2 : ℝ)*η*L := by
  have hclose := aligned_error s u t v η L hL huv hst
  have hm := discrepancy_mass_le_visits s u t v (2*η) L (by linarith)
    (fun i hi => (block_orbit_error s u t v (3*η/2) L (i+1) (by omega) hclose).trans
      (by linarith))
  have hv := rational_visits_total p q L s u η hq hpq hs hη.le
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h20 : 20 < (q : ℝ)*η := (div_lt_iff₀ hη).mp hbig
  have hsmall : 10/(q : ℝ) < η/2 := (div_lt_iff₀ hqR).mpr (by nlinarith)
  have hLR : (0 : ℝ) ≤ L := by positivity
  have hx := mul_le_mul_of_nonneg_right hsmall.le hLR
  nlinarith

theorem run_variation_bound (p q L : ℕ) (s u t v η : ℝ) (hq : 0 < q) (hL : 0 < L)
    (hpq : p.Coprime q) (hs : |s-(p : ℝ)/q| < 2/(q : ℝ)^2)
    (hη : 0 < η) (hη1 : η < 1/4) (huv : |u-v| < η)
    (hst : |s-t| < η/(2*L)) (hbig : 20/η < q) (hsize : (q : ℝ) ≤ η*L)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) :
    (∑ i ∈ Finset.range L, |(mechanicalRun s u i : ℝ)-(mechanicalRun t v i : ℝ)|) ≤
      11*η*L := by
  have hm := prefix_mass_bound p q L s u t v η hq hL hpq hs hη hη1 huv hst hbig hsize
  have ht := KroneckerMechanicalVariation.mechanical_variation s u t v L hu hv
  linarith

theorem run_variation_with_endpoint (s u t v : ℝ) (L : ℕ)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) :
    (∑ i ∈ Finset.range L, |(mechanicalRun s u i : ℝ)-(mechanicalRun t v i : ℝ)|) ≤
      2*(∑ i ∈ Finset.range L, |discrepancy s u t v (i+1)|) - |discrepancy s u t v L| := by
  simp_rw [run_discrepancy]
  have h := KroneckerDiscreteVariation.variation_with_endpoints (discrepancy s u t v) L
  rw [discrepancy_zero s u t v hu hv, abs_zero, zero_add] at h
  linarith

/-- The full common alignment contract. The offset is retained as an arbitrary
real intercept `w`, so it includes every `u₂ + b*σ₂` with an integer `b`. -/
theorem phase_alignment_bounds (p q L : ℕ) (s u t w η : ℝ) (hq : 0 < q) (hL : 0 < L)
    (hpq : p.Coprime q) (hs : |s-(p : ℝ)/q| < 2/(q : ℝ)^2)
    (ht : |t-(p : ℝ)/q| < 2/(q : ℝ)^2)
    (hu : 0 ≤ u ∧ u < 1) (hη : 0 < η) (hη1 : η < 1/4)
    (hst : |s-t| < η/(2*L)) (hbig : 20/η < q) (hsize : (q : ℝ) ≤ η*L) :
    ∃ j : ℕ, j < q ∧ |u-Int.fract (w+(j : ℝ)*t)| < η ∧
      (∀ i < j, ¬ (i < q ∧ |u-Int.fract (w+(i : ℝ)*t)| < η)) ∧
      (∑ i ∈ Finset.range L, |discrepancy s u t (Int.fract (w+(j : ℝ)*t)) (i+1)|) ≤
        (11/2 : ℝ)*η*L ∧
      (∑ i ∈ Finset.range L, |(mechanicalRun s u i : ℝ)-
        (mechanicalRun t (Int.fract (w+(j : ℝ)*t)) i : ℝ)|) ≤ 11*η*L := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h20 : 20 < (q : ℝ)*η := (div_lt_iff₀ hη).mp hbig
  have hgap : 5/(q : ℝ) < η := (div_lt_iff₀ hqR).mpr (by linarith)
  let he := phase_exists p q t w u η hq hpq ht hu hη hη1 hgap
  let j := leastPhase q t w u η he
  obtain ⟨hjq, hjclose, hjmin⟩ := least_phase_spec q t w u η he
  have hv : 0 ≤ Int.fract (w+(j : ℝ)*t) ∧ Int.fract (w+(j : ℝ)*t) < 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  refine ⟨j, hjq, hjclose, hjmin, ?_, ?_⟩
  · exact prefix_mass_bound p q L s u t _ η hq hL hpq hs hη hη1 hjclose hst hbig hsize
  · exact run_variation_bound p q L s u t _ η hq hL hpq hs hη hη1 hjclose hst hbig hsize hu hv

end KroneckerPhasePrefixHelpers
