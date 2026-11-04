import KroneckerManuscriptLimitStatements
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup

/-! The central liminf/limsup domain is a -> infinity, r/a -> 0, r >= 2,
gcd(a,r)=1. These wrappers expose exactly those conditions for any filter.
The rational/integer/irrational limit statements specify their domains. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerCurrentLimitStatements
open Filter KroneckerUpperEntropyKernel KroneckerLowerEntropyTransfer
open KroneckerScopedWeistCentralLowerLimit
open scoped Topology

theorem central_upper {α : Type*} {l : Filter α} (a r : α → ℕ)
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i : ℝ)/(a i : ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l, 2 ≤ r i ∧ (a i).Coprime (r i)) :
    UpperLimit l (fun i => Real.log (E KroneckerReadableMain.geometry (a i) (r i)) /
      (a i : ℝ)) (Real.log (256/27 : ℝ)) :=
  KroneckerScopedDeleteActualCentral.central_upper a r KroneckerReadableMain.geometry
    KroneckerReadableMain.counting KroneckerReadableMain.adjacent ha hr
    (hp.mono fun i hi => ⟨by omega, hi.2⟩)

theorem central_lower {α : Type*} {l : Filter α} (a k : α → ℕ)
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hk : Tendsto (fun i => (k i : ℝ)/(a i : ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l, 2 ≤ k i ∧ (a i).Coprime (k i)) :
    LowerLimit l (fun i => Real.log (E KroneckerReadableMain.geometry (a i) (k i)) /
      (a i : ℝ)) (Real.log (256/27 : ℝ)) :=
  central_lower_limit a k KroneckerReadableMain.geometry KroneckerReadableMain.localization
    ha hk hp

/-- The eventual upper bounds give the literal extended-real limsup inequality. -/
theorem upperLimit_limsup {α : Type*} {l : Filter α} {f : α → ℝ} {L : ℝ}
    (h : UpperLimit l f L) :
    Filter.limsup (fun i => (f i : EReal)) l ≤ (L : EReal) := by
  apply (Filter.limsup_le_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro y hy
  obtain ⟨c, hLc, hcy⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  filter_upwards [h c (EReal.coe_lt_coe_iff.mp hLc)] with i hi
  exact (EReal.coe_le_coe hi).trans_lt hcy

/-- The eventual lower bounds give the literal extended-real liminf inequality. -/
theorem lowerLimit_liminf {α : Type*} {l : Filter α} {f : α → ℝ} {L : ℝ}
    (h : LowerLimit l f L) :
    (L : EReal) ≤ Filter.liminf (fun i => (f i : EReal)) l := by
  apply (Filter.le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro y hy
  obtain ⟨c, hyc, hcL⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  filter_upwards [h c (EReal.coe_lt_coe_iff.mp hcL)] with i hi
  exact hyc.trans_le (EReal.coe_le_coe hi)

/-- Theorem 7.59(2), with the PDF's positive indices and positivity conclusion.
The value at index zero is immaterial. The liminf is taken in `EReal`, so the
statement does not assume a finite limit or an upper bound. -/
theorem central_lower_sequence (a k : ℕ → ℕ)
    (_ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hk_two : ∀ n : ℕ, 1 ≤ n → 2 ≤ k n)
    (hcoprime : ∀ n : ℕ, 1 ≤ n → (a n).Coprime (k n))
    (ha : Tendsto (fun n => (a n : ℝ)) atTop atTop)
    (hk : Tendsto (fun n => (k n : ℝ) / (a n : ℝ)) atTop (𝓝 0)) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < E KroneckerReadableMain.geometry (a n) (k n)) ∧
    (Real.log (256 / 27 : ℝ) : EReal) ≤
      Filter.liminf (fun n =>
        (Real.log (E KroneckerReadableMain.geometry (a n) (k n)) /
          (a n : ℝ) : EReal)) atTop := by
  have hp : ∀ᶠ n : ℕ in atTop, 2 ≤ k n ∧ (a n).Coprime (k n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ⟨hk_two n hn, hcoprime n hn⟩
  have hpositive := euler_eventually_positive a k KroneckerReadableMain.geometry
    KroneckerReadableMain.localization ha hk hp
  exact ⟨eventually_atTop.mp hpositive,
    lowerLimit_liminf (central_lower a k ha hk hp)⟩

/-- Corollary 8.4, with the PDF's named sequence and explicit positive tail. -/
theorem central_upper_sequence (a r : ℕ → ℕ)
    (_ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (hr_two : ∀ n : ℕ, 1 ≤ n → 2 ≤ r n)
    (hcoprime : ∀ n : ℕ, 1 ≤ n → (a n).Coprime (r n))
    (ha : Tendsto (fun n => (a n : ℝ)) atTop atTop)
    (hr : Tendsto (fun n => (r n : ℝ) / (a n : ℝ)) atTop (𝓝 0)) :
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < E KroneckerReadableMain.geometry (a n) (r n)) ∧
    Filter.limsup (fun n =>
      (Real.log (E KroneckerReadableMain.geometry (a n) (r n)) /
        (a n : ℝ) : EReal)) atTop ≤ (Real.log (256 / 27 : ℝ) : EReal) := by
  have hp : ∀ᶠ n : ℕ in atTop, 2 ≤ r n ∧ (a n).Coprime (r n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ⟨hr_two n hn, hcoprime n hn⟩
  have hpositive := KroneckerScopedDeleteActualCentral.eventually_positive a r
    KroneckerReadableMain.geometry KroneckerReadableMain.counting ha hr
    (hp.mono fun n hn => ⟨by omega, hn.2⟩)
  exact ⟨eventually_atTop.mp hpositive,
    upperLimit_limsup (central_upper a r ha hr hp)⟩

end KroneckerCurrentLimitStatements
