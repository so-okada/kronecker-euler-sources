import KroneckerScopedOtherFundamental

/-! Lemma 10.3: dimension reduction along sequences, including crossings
of the two boundary slopes of the closed fundamental interval. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerApproachingDimensionReduction
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
open KroneckerManuscriptTarget KroneckerInteriorAllowedReflection
open KroneckerEndpointRoots KroneckerRealReflectionIterates
variable (H : ∀ m a b, Admissible (space m a b))

def hgt {m : ℕ} (p : Interior H m) : ℝ := height p.val
def slp {m : ℕ} (p : Interior H m) : ℝ := slope p.val
def eu {m : ℕ} (p : Interior H m) : ℤ := euler (family H) m p.val.val.1 p.val.val.2

theorem hgt_pos {m : ℕ} (p : Interior H m) : 0 < hgt H p :=
  Nat.cast_pos.mpr p.val.property.1
theorem slp_pos {m : ℕ} (p : Interior H m) : 0 < slp H p :=
  KroneckerExchangeObservables.slope_positive H p.val

theorem exchange_slope (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    slp H (exchange H m hm p) = (slp H p)⁻¹ :=
  KroneckerExchangeObservables.slope_exchange H p.val
theorem exchange_ratio (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    hgt H (exchange H m hm p) / hgt H p = slp H p := by
  rw [show hgt H (exchange H m hm p) = slp H p * hgt H p from
    KroneckerExchangeObservables.height_exchange H p.val]
  exact mul_div_cancel_right₀ _ (ne_of_gt (hgt_pos H p))
theorem exchange_euler (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    eu H (exchange H m hm p) = eu H p :=
  (KroneckerExchangeEuler.euler_eq m p.val.val.1 p.val.val.2 (H _ _ _) (H _ _ _)).symm

theorem reflect_ratio (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    hgt H (reflect H m hm p) / hgt H p = (m : ℝ) - slp H p := by
  have hb := (KroneckerCanonicalDimensionBounds.dimension_bounds m _ _
    p.val.property.1 p.val.property.2.1 p.val.property.2.2.2).1
  have ha : (p.val.val.1 : ℝ) ≠ 0 := ne_of_gt (hgt_pos H p)
  change ((m*p.val.val.1-p.val.val.2 : ℕ) : ℝ) / p.val.val.1 =
    (m : ℝ) - (p.val.val.2 : ℝ) / p.val.val.1
  rw [Nat.cast_sub hb, Nat.cast_mul]
  field_simp

theorem reflect_slope (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    slp H (reflect H m hm p) = ((m : ℝ) - slp H p)⁻¹ := by
  rw [← reflect_ratio H m hm p]
  change (p.val.val.1 : ℝ) / (m*p.val.val.1-p.val.val.2 : ℕ) =
    (((m*p.val.val.1-p.val.val.2 : ℕ) : ℝ) / p.val.val.1)⁻¹
  rw [inv_div]

theorem reflect_euler (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    eu H (reflect H m hm p) = eu H p :=
  KroneckerInteriorReflectionEuler.euler H m hm p

def central (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) : Interior H m :=
  exchange H m hm (reflect H m hm p)
theorem central_height (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    hgt H (central H m hm p) = hgt H p := rfl
theorem central_slope (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    slp H (central H m hm p) = (m : ℝ) - slp H p := by
  simp only [central, exchange_slope, reflect_slope, inv_inv]
theorem central_euler (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    eu H (central H m hm p) = eu H p :=
  (exchange_euler H m hm _).trans (reflect_euler H m hm p)

def lowerFold (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) : Interior H m :=
  if slp H p < 1 then exchange H m hm p else p
def fold (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) : Interior H m :=
  let q := lowerFold H m hm p
  if (m : ℝ)/2 < slp H q then central H m hm q else q

theorem lower_slope (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    slp H (lowerFold H m hm p) = max (slp H p) (slp H p)⁻¹ := by
  unfold lowerFold
  split_ifs with h
  · rw [exchange_slope, max_eq_right]
    exact le_trans h.le ((one_le_inv₀ (slp_pos H p)).mpr h.le)
  · rw [max_eq_left]
    have hp : 1 ≤ slp H p := le_of_not_gt h
    exact ((inv_le_one₀ (slp_pos H p)).mpr hp).trans hp
theorem lower_ratio (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    hgt H (lowerFold H m hm p) / hgt H p = min (slp H p) 1 := by
  unfold lowerFold
  split_ifs with h
  · rw [exchange_ratio, min_eq_left h.le]
  · rw [div_self (ne_of_gt (hgt_pos H p)), min_eq_right (le_of_not_gt h)]
theorem lower_ge_one (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    1 ≤ slp H (lowerFold H m hm p) := by
  unfold lowerFold
  split_ifs with h
  · rw [exchange_slope]
    exact (one_le_inv₀ (slp_pos H p)).mpr h.le
  · exact le_of_not_gt h
theorem lower_euler (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    eu H (lowerFold H m hm p) = eu H p := by
  unfold lowerFold
  split_ifs
  · exact exchange_euler H m hm p
  · rfl
theorem fold_height (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    hgt H (fold H m hm p) = hgt H (lowerFold H m hm p) := by
  dsimp only [fold]
  split_ifs
  · exact central_height H m hm _
  · rfl
theorem fold_slope (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    slp H (fold H m hm p) = min (slp H (lowerFold H m hm p))
      ((m : ℝ) - slp H (lowerFold H m hm p)) := by
  dsimp only [fold]
  split_ifs with h
  · rw [central_slope, min_eq_right (by linarith)]
  · rw [min_eq_left (by linarith)]
theorem fold_euler (m : ℕ) (hm : 3 ≤ m) (p : Interior H m) :
    eu H (fold H m hm p) = eu H p := by
  dsimp only [fold]
  split_ifs
  · exact (central_euler H m hm _).trans (lower_euler H m hm p)
  · exact lower_euler H m hm p

def Reduces (m : ℕ) (r : ℝ) : Prop :=
  ∃ r' ∈ Set.Icc 1 ((m : ℝ)/2), ∃ c : ℝ, 0 < c ∧
    ∀ p : ℕ → Interior H m, Tendsto (fun n => slp H (p n)) atTop (𝓝 r) →
    ∃ q : ℕ → Interior H m,
      (∀ᶠ n in atTop, slp H (q n) ∈ Set.Icc 1 ((m : ℝ)/2)) ∧
      (∀ n, eu H (q n) = eu H (p n)) ∧
      Tendsto (fun n => hgt H (q n) / hgt H (p n)) atTop (𝓝 c) ∧
      Tendsto (fun n => slp H (q n)) atTop (𝓝 r')

theorem fundamental_reduces (m : ℕ) (hm : 3 ≤ m) (r : ℝ)
    (hr : r ∈ Set.Icc 1 ((m : ℝ)/2)) : Reduces H m r := by
  refine ⟨r, hr, 1, by norm_num, ?_⟩
  intro p hp
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr.1
  have hmax : max r r⁻¹ = r := max_eq_left
    (((inv_le_one₀ hr0).mpr hr.1).trans hr.1)
  have hlo : Tendsto (fun n => slp H (lowerFold H m hm (p n))) atTop (𝓝 r) := by
    simpa only [lower_slope, hmax] using hp.max (hp.inv₀ (ne_of_gt hr0))
  have hmin : min r ((m : ℝ)-r) = r := min_eq_left (by linarith [hr.2])
  have hsl : Tendsto (fun n => slp H (fold H m hm (p n))) atTop (𝓝 r) := by
    simpa only [fold_slope, hmin] using hlo.min
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (m : ℝ)) atTop (𝓝 (m : ℝ))).sub hlo)
  have hh : Tendsto (fun n => hgt H (fold H m hm (p n)) / hgt H (p n)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [fold_height, lower_ratio, min_eq_right hr.1] using hp.min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hmR : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  have hlate := hlo.eventually (eventually_lt_nhds (show r < (m : ℝ)-1 by linarith [hr.2]))
  refine ⟨fun n => fold H m hm (p n), ?_, fun n => fold_euler H m hm (p n), hh, hsl⟩
  filter_upwards [hlate] with n hn
  rw [fold_slope]
  have h1 := lower_ge_one H m hm (p n)
  constructor
  · exact le_min h1 (by linarith)
  · by_cases h : slp H (lowerFold H m hm (p n)) ≤ (m : ℝ)/2
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)

theorem pullback (m : ℕ) (r s d : ℝ) (hd : 0 < d)
    (φ : Interior H m → Interior H m)
    (he : ∀ p, eu H (φ p) = eu H p)
    (hs : ∀ p : ℕ → Interior H m, Tendsto (fun n => slp H (p n)) atTop (𝓝 r) →
      Tendsto (fun n => slp H (φ (p n))) atTop (𝓝 s))
    (hh : ∀ p : ℕ → Interior H m, Tendsto (fun n => slp H (p n)) atTop (𝓝 r) →
      Tendsto (fun n => hgt H (φ (p n)) / hgt H (p n)) atTop (𝓝 d))
    (h : Reduces H m s) : Reduces H m r := by
  obtain ⟨r', hr', c, hc, hq⟩ := h
  refine ⟨r', hr', c*d, mul_pos hc hd, ?_⟩
  intro p hp
  obtain ⟨q, hbounds, heq, hratio, hslope⟩ := hq (fun n => φ (p n)) (hs p hp)
  refine ⟨q, hbounds, fun n => (heq n).trans (he (p n)), ?_, hslope⟩
  have hmul := hratio.mul (hh p hp)
  convert hmul using 1
  funext n
  field_simp [ne_of_gt (hgt_pos H (φ (p n)))]

theorem exchange_pullback (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : 0 < r)
    (h : Reduces H m r⁻¹) : Reduces H m r := by
  apply pullback H m r r⁻¹ r hr (exchange H m hm) (exchange_euler H m hm) _ _ h
  · intro p hp
    simpa only [exchange_slope] using hp.inv₀ (ne_of_gt hr)
  · intro p hp
    simpa only [exchange_ratio] using hp

theorem reflection_pullback (m : ℕ) (hm : 3 ≤ m) (r : ℝ)
    (hr : r ∈ interior m) (h : Reduces H m ((m : ℝ)-r)⁻¹) : Reduces H m r := by
  have hd := KroneckerInteriorReflectionObservables.denominator_positive m hm r hr
  apply pullback H m r _ ((m : ℝ)-r) hd (reflect H m hm) (reflect_euler H m hm) _ _ h
  · intro p hp
    simpa only [reflect_slope] using (tendsto_const_nhds.sub hp).inv₀ (ne_of_gt hd)
  · intro p hp
    simpa only [reflect_ratio] using tendsto_const_nhds.sub hp

theorem central_pullback (m : ℕ) (hm : 3 ≤ m) (r : ℝ)
    (h : Reduces H m ((m : ℝ)-r)) : Reduces H m r := by
  apply pullback H m r _ 1 (by norm_num) (central H m hm) (central_euler H m hm) _ _ h
  · intro p hp
    simpa only [central_slope] using tendsto_const_nhds.sub hp
  · intro p hp
    simpa only [central_height, div_self (ne_of_gt (hgt_pos H _))] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

theorem orbit_pullback (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interior m)
    (n : ℕ) (h : Reduces H m (orbit (m : ℝ) r n)) : Reduces H m r := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply ih
    apply reflection_pullback H m hm _
      (KroneckerRealReflectionIterates.interior (by exact_mod_cast (show 2 < m by omega)) hr n)
    exact h

theorem interior_reduces (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    Reduces H m r := by
  have hmR : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  let a := KroneckerRealFundamentalRepresentative.orient r
  have ha := KroneckerRealFundamentalRepresentative.orient_interior hmR hr
  let n := KroneckerRealReflectionFiniteHit.firstHit hmR ha
  let b := orbit (m : ℝ) a n
  have hb : b ∈ Set.Icc 1 ((m : ℝ)-1) :=
    KroneckerRealReflectionEntryStrip.strip hmR ha
      (KroneckerRealFundamentalRepresentative.orient_ge_one hmR hr)
  have hfold := fundamental_reduces H m hm (KroneckerCentralStripFold.fold (m : ℝ) b)
    (KroneckerCentralStripFold.bounds hb)
  have hred : Reduces H m b := by
    unfold KroneckerCentralStripFold.fold at hfold
    split_ifs at hfold with h
    · exact hfold
    · exact central_pullback H m hm b hfold
  have hor := orbit_pullback H m hm a ha n hred
  dsimp [a, KroneckerRealFundamentalRepresentative.orient] at hor
  split_ifs at hor with h
  · exact hor
  · exact exchange_pullback H m hm r
      ((lowerRoot_positive hmR).trans hr.1) hor

theorem approaching_dimension_reduction (m : ℕ) (hm : 3 ≤ m) (r : ℝ)
    (hr : r ∈ interior m) :
    ∃ r' ∈ Set.Icc 1 ((m : ℝ)/2), ∃ c : ℝ, 0 < c ∧
    ∀ p : ℕ → Dimension (family H) m,
      Tendsto (fun n => slope (p n)) atTop (𝓝 r) →
    ∃ N : ℕ, ∃ q : ℕ → Dimension (family H) m,
      (∀ n, slope (q n) ∈ Set.Icc 1 ((m : ℝ)/2)) ∧
      (∀ n, euler (family H) m (q n).val.1 (q n).val.2 =
        euler (family H) m (p (n+N)).val.1 (p (n+N)).val.2) ∧
      Tendsto (fun n => (height (q n) : ℝ) / height (p (n+N))) atTop (𝓝 c) ∧
      Tendsto (fun n => slope (q n)) atTop (𝓝 r') := by
  obtain ⟨r', hr', c, hc, hred⟩ := interior_reduces H m hm r hr
  refine ⟨r', hr', c, hc, ?_⟩
  intro p hp
  have hi : ∀ᶠ n in atTop, slope (p n) ∈ interior m :=
    hp.eventually (isOpen_Ioo.mem_nhds hr)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hi
  let p' : ℕ → Interior H m := fun n => ⟨p (n+N), hN (n+N) (by omega)⟩
  have hp' : Tendsto (fun n => slp H (p' n)) atTop (𝓝 r) :=
    hp.comp (tendsto_add_atTop_nat N)
  obtain ⟨q, hq, he, hh, hs⟩ := hred p' hp'
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hq
  refine ⟨N+N', fun n => (q (n+N')).val, fun n => hN' (n+N') (by omega), ?_, ?_, ?_⟩
  · intro n
    simpa only [eu, p', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he (n+N')
  · have hh' := hh.comp (tendsto_add_atTop_nat N')
    simp only [hgt, p', Nat.add_comm, Nat.add_left_comm] at hh' ⊢
    exact hh'
  · exact hs.comp (tendsto_add_atTop_nat N')

end KroneckerApproachingDimensionReduction
