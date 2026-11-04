import KroneckerPeriodicLimit
import KroneckerExplicitFiniteBound
import KroneckerFrameWord

/-! Three extracted manuscript arguments: shifted growth, dimension reduction,
and the finite count of exceptional floor differences. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace KroneckerFurtherIntermediateLemmas

theorem shifted_growth (A : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ n, 1 ≤ n → 1 ≤ A n)
    (hmul : ∀ i j, 1 ≤ i → 1 ≤ j → A i * A j ≤ A (i+j+2))
    (hbound : ∀ n, 1 ≤ n → Real.log (A n) ≤ C*n) :
    ∃ L : ℝ, 0 ≤ L ∧ L ≤ C ∧
      L = sSup ((fun n : ℕ => Real.log (A n) / ((n : ℝ)+2)) '' Set.Ici 1) ∧
      Tendsto (fun n : ℕ => Real.log (A n)/(n : ℝ)) atTop (𝓝 L) ∧
      ∀ n, 1 ≤ n → A n ≤ Real.exp (((n : ℝ)+2)*L) := by
  let u : ℕ → ℝ := fun n => Real.log (A (n-2))
  let S := (fun n : ℕ => Real.log (A n)/((n : ℝ)+2)) '' Set.Ici 1
  have hpos : ∀ n, 3 ≤ n → 0 ≤ u n := by
    intro n hn
    exact Real.log_nonneg (hA (n-2) (by omega))
  have hu : KroneckerAsymptotics.TailSuperadditive u := by
    intro i hi j hj
    have hp : 0 < A (i-2) := lt_of_lt_of_le (by norm_num) (hA _ (by omega))
    have hq : 0 < A (j-2) := lt_of_lt_of_le (by norm_num) (hA _ (by omega))
    have h := Real.log_le_log (mul_pos hp hq) (hmul (i-2) (j-2) (by omega) (by omega))
    rw [Real.log_mul hp.ne' hq.ne'] at h
    simpa only [u, show i-2+(j-2)+2 = i+j-2 by omega] using h
  have hub : ∀ n, 3 ≤ n → u n ≤ C*n := by
    intro n hn
    exact (hbound (n-2) (by omega)).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le n 2) hC)
  have hset : (fun n : ℕ => u n/(n : ℝ)) '' Set.Ici 3 = S := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hn' : 3 ≤ n := hn
      refine ⟨n-2, by change 1 ≤ n-2; omega, ?_⟩
      have he : ((n-2 : ℕ) : ℝ)+2 = (n : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      simp only [u, he]
    · rintro ⟨n, hn, rfl⟩
      refine ⟨n+2, by change 3 ≤ n+2; have : 1 ≤ n := hn; omega, ?_⟩
      simp [u]
  have hSC : ∀ x ∈ S, x ≤ C := by
    rintro x ⟨n, hn, rfl⟩
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+2)).mpr
    have hh := hbound n hn
    nlinarith
  have hb : BddAbove S := ⟨C, hSC⟩
  have hnS : S.Nonempty := ⟨Real.log (A 1)/3, 1, (by change (1 : ℕ) ≤ 1; rfl), by norm_num⟩
  have hl0 : 0 ≤ sSup S := by
    have hh : Real.log (A 1)/3 ≤ sSup S := le_csSup hb ⟨1, (by change (1 : ℕ) ≤ 1; rfl), by norm_num⟩
    exact (div_nonneg (Real.log_nonneg (hA 1 le_rfl)) (by norm_num)).trans hh
  have hlC : sSup S ≤ C := csSup_le hnS hSC
  have ht := KroneckerAsymptotics.tail_fekete hu hpos C hub
  rw [hset] at ht
  have ht' : Tendsto (fun n : ℕ => Real.log (A n)/((n : ℝ)+2)) atTop (𝓝 (sSup S)) := by
    simpa [u, Function.comp_def] using ht.comp (tendsto_add_atTop_nat 2)
  have hlim := KroneckerLogic.normalization_transport
    (a := fun n : ℕ => (n : ℝ)) (b := fun n : ℕ => (n : ℝ)+2)
    (V := fun n => Real.log (A n)) 1 (sSup S)
    (Eventually.of_forall (fun n => by positivity))
    KroneckerPeriodicLimit.denominator_ratio_limit ht'
  refine ⟨sSup S, hl0, hlC, rfl, by simpa only [one_mul] using hlim, ?_⟩
  intro n hn
  have hsup := le_csSup hb (show Real.log (A n)/((n : ℝ)+2) ∈ S from ⟨n, hn, rfl⟩)
  have hlog : Real.log (A n) ≤ ((n : ℝ)+2)*sSup S := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)+2)).mp hsup
    simpa only [mul_comm] using h
  rw [← Real.exp_log (lt_of_lt_of_le (by norm_num) (hA n hn))]
  exact Real.exp_le_exp.mpr hlog

open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerNegativeTitsSymmetry KroneckerManuscriptTarget

theorem reduced_dimensions (m a b : ℕ) (hm : 3 ≤ m) (hc : a.Coprime b)
    (ht : tits m a b < 0) :
    ∃ u v : ℕ, 0 < u ∧ u ≤ v ∧ 2*v ≤ m*u ∧ u.Coprime v ∧
      tits m u v = tits m a b ∧
      euler (family KroneckerReadableMain.geometry) m u v =
        euler (family KroneckerReadableMain.geometry) m a b ∧
      (u : ℝ)+v ≤ Real.sqrt (((m : ℝ)+2)/((m : ℝ)-2))*Real.sqrt (-(tits m a b : ℝ)) := by
  obtain ⟨u,v,hu,huv,hv,hq,hg,he⟩ :=
    KroneckerFundamentalEulerReduction.reduction
      (finiteHomology KroneckerReadableMain.geometry) m a b ht
  refine ⟨u,v,hu,huv,hv,?_,hq,he.symm,?_⟩
  · change Nat.gcd u v = 1
    rw [hg]
    exact hc
  · have h := KroneckerFundamentalSqrtBound.sum_sqrt_bound m u v hm huv hv (by rw [hq]; exact ht)
    simpa only [hq] using h

theorem exceptional_floor_differences (q N : ℕ) (p : ℤ) (s u : ℝ)
    (hclose : |(q : ℝ)*s-(p : ℝ)| < 1) :
    (((Finset.range N).filter (fun i : ℕ =>
      (⌊u+((i : ℝ)+(q : ℝ))*s⌋ : ℤ)-⌊u+(i : ℝ)*s⌋ ≠ p)).card : ℝ) ≤
      (N : ℝ)*|(q : ℝ)*s-(p : ℝ)|+(q : ℝ) := by
  classical
  have h := KroneckerBadWindowAbsolute.bad_windows_absolute s u p q N hclose.le
  have hw : ∀ i, KroneckerMechanicalWindows.windowSum s u q i =
      (⌊u+((i : ℝ)+(q : ℝ))*s⌋ : ℤ)-⌊u+(i : ℝ)*s⌋ := by
    intro i
    rw [KroneckerMechanicalWindows.window_floor]
    congr 2
    ring
  simpa only [KroneckerBadWindowBounds.badWindows, KroneckerBadWindowCount.nonzeroCount,
    KroneckerWindowDiscrepancy.discrepancy, hw, sub_ne_zero] using h

end KroneckerFurtherIntermediateLemmas
