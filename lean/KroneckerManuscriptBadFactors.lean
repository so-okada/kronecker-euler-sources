import KroneckerFrameWord
import KroneckerCurrentMechanicalNotation

/-! Definition 5.4 and Lemma 5.6: D_bad(U(a,b),p,q) counts alpha-bad run-factors.
The fixed numerator p is explicit in badWordWindows; its zero-based start
index is r-1 for the manuscript RunFactor_{r,q}. Specialize d to d1=a+t
from Definition 2.25 to obtain frameSlope a b d=Gamma(a,b). -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace KroneckerManuscriptBadFactors
open KroneckerCurrentMechanicalNotation
open KroneckerFiniteWindows KroneckerFrameBadDensity KroneckerFrameSlope
open KroneckerMechanicalWords KroneckerAppendedBadCount KroneckerBadWindowAbsolute

/-- The finite estimate under the weaker, sufficient discrepancy bound |qs-p| ≤ 1. -/
theorem finite_bound_of_discrepancy (a b d q : ℕ) (p : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hd : a < d) (hq : 0 < q) (hqa : q ≤ a)
    (hclose : |(q : ℝ)*frameSlope a b d-(p : ℝ)| ≤ 1) :
    (Dbad (frameWord a b d) p q : ℝ) ≤
      |(q : ℝ)*b-(p : ℝ)*a|+(q : ℝ)+2 := by
  have hs : 0 ≤ frameSlope a b d := frameSlope_nonnegative a b d ha hb (by omega)
  have happ := badWordWindows_append_one (mechanicalWord (frameSlope a b d) 0 0 a) 1 p q
  rw [badWordWindows_mechanical _ _ _ _ _ hs] at happ
  have hbase := bad_windows_absolute (frameSlope a b d) 0 p q (a+1-q) hclose
  have hlen : ((a+1-q : ℕ) : ℝ) ≤ (a : ℝ) := by
    exact_mod_cast (show a+1-q ≤ a by omega)
  have hmul := mul_le_mul_of_nonneg_right hlen
    (abs_nonneg ((q : ℝ)*frameSlope a b d-(p : ℝ)))
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqd : (q : ℝ) / d ≤ 1 := by
    apply (div_le_iff₀ hdR).mpr
    norm_cast
    omega
  have hid : (a : ℝ)*((q : ℝ)*frameSlope a b d-(p : ℝ)) =
      (q : ℝ)*b-(p : ℝ)*a-(q : ℝ)/d := by
    unfold frameSlope
    field_simp
    <;> ring
  have herror : (a : ℝ)*|(q : ℝ)*frameSlope a b d-(p : ℝ)| ≤
      |(q : ℝ)*b-(p : ℝ)*a|+(q : ℝ)/d := by
    have habs : (a : ℝ)*|(q : ℝ)*frameSlope a b d-(p : ℝ)| =
        |(a : ℝ)*((q : ℝ)*frameSlope a b d-(p : ℝ))| := by
      rw [abs_mul, abs_of_pos haR]
    rw [habs, hid]
    simpa only [abs_of_nonneg (show (0 : ℝ) ≤ (q : ℝ)/d by positivity)] using
      abs_sub ((q : ℝ)*b-(p : ℝ)*a) ((q : ℝ)/d)
  have happR : (Dbad (frameWord a b d) p q : ℝ) ≤
      (KroneckerBadWindowBounds.badWindows (frameSlope a b d) 0 p q (a+1-q) : ℝ)+1 := by
    exact_mod_cast happ
  linarith

/-- Claim 1 of Lemma 5.6 with the manuscript's q^(-2) hypothesis. -/
theorem finite_bound (a b d q : ℕ) (p : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hd : a < d) (hq : 2 ≤ q) (hqa : q ≤ a)
    (hclose : |frameSlope a b d-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    (Dbad (frameWord a b d) p q : ℝ) ≤
      |(q : ℝ)*b-(p : ℝ)*a|+(q : ℝ)+2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hmul := mul_lt_mul_of_pos_left hclose hqR
  have heq : (q : ℝ)*(frameSlope a b d-(p : ℝ)/(q : ℝ)) =
      (q : ℝ)*frameSlope a b d-(p : ℝ) := by field_simp
  have hrec : (q : ℝ)*(1/(q : ℝ)^2) = 1/(q : ℝ) := by field_simp
  have habs : (q : ℝ)*|frameSlope a b d-(p : ℝ)/(q : ℝ)| =
      |(q : ℝ)*frameSlope a b d-(p : ℝ)| := by
    rw [← abs_of_pos hqR, ← abs_mul, abs_of_pos hqR, heq]
  rw [habs, hrec] at hmul
  have hle : (1 : ℝ)/(q : ℝ) ≤ 1 := (div_le_one hqR).mpr hq1
  exact finite_bound_of_discrepancy a b d q p ha hb hd (by omega) hqa (hmul.le.trans hle)

/-- Claim 2 of Lemma 5.6, as convergence of D_bad/a to zero. -/
theorem density_zero (a b d : ℕ → ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    Tendsto (fun n => (Dbad (frameWord (a n) (b n) (d n)) p q : ℝ)/(a n : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
  frame_bad_window_density a b d p q hq ha ha0 hb hd hr

end KroneckerManuscriptBadFactors

