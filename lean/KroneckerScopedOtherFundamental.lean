import KroneckerScopedActualFrameJointTransfer
import KroneckerCentralSortedDimensions
import KroneckerRootCrossRatioOrbit
import KroneckerPositiveLimitReflection
import KroneckerEnvelopeTitsNormalization
import KroneckerCanonicalLimitEnvelope
import KroneckerCanonicalInteriorBoundExtension
import KroneckerFundamentalNonemptyProved

section

/- Original module: KroneckerFourFoldArithmetic -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerFourFoldArithmetic
open Filter
open scoped Topology

def fold (a b : ℕ) := min b (4*a-b)

theorem fold_upper (a b : ℕ) : fold a b ≤ 2*a := by unfold fold; omega

theorem fold_increasing {a b : ℕ} (h₁ : a < b) (h₃ : b < 3*a) : a < fold a b := by
  unfold fold
  omega

theorem fold_primitive {a b : ℕ} (hc : a.Coprime b) (hb : b ≤ 4*a) : a.Coprime (fold a b) := by
  unfold fold
  rcases le_total b (4*a-b) with h | h
  · simpa only [min_eq_left h] using hc
  · rw [min_eq_right h]
    exact ((KroneckerReflectionPrimitive.coprime_iff 4 a b hb).mpr hc).symm

theorem fold_ratio {a b : ℕ} (ha : 0 < a) (hb : b ≤ 4*a) :
    (fold a b : ℝ)/a = min ((b : ℝ)/a) (4-(b : ℝ)/a) := by
  have hap : (0:ℝ) < a := by exact_mod_cast ha
  have hcast : ((4*a-b : ℕ):ℝ)/a = 4-(b : ℝ)/a := by
    rw [Nat.cast_sub hb]
    push_cast
    field_simp
  rw [← hcast]
  simp only [fold, Nat.cast_min, min_div_div_right hap.le]

theorem fold_ratio_upper {a b : ℕ} (ha : 0 < a) : (fold a b : ℝ)/a ≤ 2 := by
  have hap : (0:ℝ) < a := by exact_mod_cast ha
  apply (div_le_iff₀ hap).mpr
  exact_mod_cast fold_upper a b

variable {α : Type*} {l : Filter α} (a b : α → ℕ)

theorem eventually_region (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 2)) :
    ∀ᶠ i in l, 0 < a i ∧ a i < b i ∧ b i < 3*a i := by
  filter_upwards [KroneckerLowerEntropyKernel.eventually_positive a ha,
    hs.eventually (lt_mem_nhds (by norm_num : (1:ℝ)<2)),
    hs.eventually (gt_mem_nhds (by norm_num : (2:ℝ)<3))] with i hai h₁ h₃
  have hap : (0:ℝ) < a i := by exact_mod_cast hai
  refine ⟨hai, ?_, ?_⟩
  · have h := (lt_div_iff₀ hap).mp h₁
    simp only [one_mul] at h
    exact_mod_cast h
  · exact_mod_cast (div_lt_iff₀ hap).mp h₃

theorem fold_tendsto (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 2)) :
    Tendsto (fun i => (fold (a i) (b i) : ℝ)/a i) l (𝓝 2) := by
  have h := hs.min (hs.const_sub 4)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_region a b ha hs] with i hi
  exact (fold_ratio hi.1 (by omega)).symm

theorem eventually_fold_input (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 2))
    (hc : ∀ᶠ i in l, (a i).Coprime (b i)) :
    ∀ᶠ i in l, 2 ≤ a i ∧ a i < fold (a i) (b i) ∧
      (a i).Coprime (fold (a i) (b i)) ∧ (fold (a i) (b i) : ℝ)/a i ≤ 2 := by
  filter_upwards [ha.eventually_ge_atTop 2, eventually_region a b ha hs, hc] with i hai hi hci
  exact ⟨by exact_mod_cast hai, fold_increasing hi.2.1 hi.2.2,
    fold_primitive hci (by omega), fold_ratio_upper hi.1⟩

end KroneckerFourFoldArithmetic
end
end

/- Original module: KroneckerScopedActualFourBoundary -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedActualFourBoundary
open Filter KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerScopedActualFrameApplication
open KroneckerScopedActualFrameJointTransfer KroneckerFourFoldArithmetic KroneckerLogic
open scoped Topology

theorem euler_reflect_fixed_height (G : Geometry) (m a b : ℕ) (ha : 0 < a) (hb : b ≤ m*a) :
    euler (family G) m a b = euler (family G) m a (m*a-b) :=
  (KroneckerCanonicalReflectionEuler.euler_eq m a b ha hb
    (finiteHomology G m a b) (finiteHomology G m (m*a-b) a)).trans
    (KroneckerExchangeEuler.euler_eq m (m*a-b) a
      (finiteHomology G m (m*a-b) a) (finiteHomology G m a (m*a-b)))

theorem euler_fold (G : Geometry) (a b : ℕ) (ha : 0 < a) (hb : b ≤ 4*a) :
    euler (family G) 4 a b = euler (family G) 4 a (fold a b) := by
  rcases le_total b (4*a-b) with h | h
  · simp only [fold, min_eq_left h]
  · simp only [fold, min_eq_right h]
    exact euler_reflect_fixed_height G 4 a b ha hb

theorem four_pairs {α : Type*} {l : Filter α} (G : Geometry) (A : Application G)
    (a b : α → ℕ) (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 2))
    (hc : ∀ᶠ i in l, (a i).Coprime (b i)) :
    Tendsto (fun i => Real.log (euler (family G) 4 (a i) (b i) : ℝ)/(a i : ℝ)) l
      (𝓝 (KroneckerClosedAlphabetEntropy.entropy 4 2)) := by
  have h := below_sequence G A 4 (by decide) 2 (by norm_num [KroneckerClosedAlphabetEntropy.interval])
    a (fun i => fold (a i) (b i)) (tendsto_natCast_atTop_iff.mp ha)
    (fold_tendsto a b ha hs) (eventually_fold_input a b ha hs hc)
  apply h.congr'
  filter_upwards [eventually_region a b ha hs] with i hi
  rw [euler_fold G (a i) (b i) hi.1 (by omega)]

theorem four_joint (G : Geometry) (A : Application G) :
    JointLimit (height (M:=family G) (m:=4)) slope value 2
      (KroneckerClosedAlphabetEntropy.entropy 4 2) := by
  apply jointLimit_of_sequences
  intro p ha hs
  exact four_pairs G A (fun n => (p n).val.1) (fun n => (p n).val.2)
    (tendsto_natCast_atTop_atTop.comp ha) hs
    (Eventually.of_forall fun n => (p n).property.2.2.1)

theorem four_positive (G : Geometry) (A : Application G) :
    KroneckerPositiveLimitExchange.PositiveLimit (finiteHomology G) 4 2 :=
  ⟨_, KroneckerClosedAlphabetBounds.closed_entropy_positive 4 (by decide) 2
    (by norm_num [KroneckerClosedAlphabetEntropy.interval]), four_joint G A⟩

end KroneckerScopedActualFourBoundary
end
end
end

section

noncomputable section
set_option autoImplicit false
namespace KroneckerScopedAllMCentralFrameTransfer
open Filter KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerScopedActualFrameApplication
open KroneckerScopedActualFrameJointTransfer KroneckerCentralSortedDimensions KroneckerLogic
open scoped Topology

theorem euler_sorted (G : Geometry) (m a b : ℕ) :
    euler (family G) m a b = euler (family G) m (lo a b) (max a b) := by
  rcases le_total a b with h | h
  · simp only [lo, min_eq_left h, max_eq_right h]
  · simp only [lo, min_eq_right h, max_eq_left h]
    exact KroneckerExchangeEuler.euler_eq m a b (finiteHomology G m a b) (finiteHomology G m b a)

theorem entropy_sorted (G : Geometry) (m a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (euler (family G) m a b : ℝ)/(a : ℝ) =
      (Real.log (euler (family G) m (lo a b) (max a b) : ℝ)/(lo a b : ℝ))*
        ((lo a b : ℝ)/a) := by
  rw [euler_sorted G m a b]
  have hlo : (lo a b : ℝ) ≠ 0 := by exact_mod_cast (lo_pos ha hb).ne'
  field_simp

variable {α : Type*} {l : Filter α} (a b : α → ℕ)

theorem sorted_slope_tendsto (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 1)) (hb : ∀ᶠ i in l, 0 < b i) :
    Tendsto (fun i => ((max (a i) (b i) : ℕ) : ℝ)/lo (a i) (b i)) l (𝓝 1) := by
  have h := (gap_ratio_tendsto a b ha hs hb).const_add 1
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [KroneckerLowerEntropyKernel.eventually_positive a ha, hb] with i hai hbi
  have hlo : (lo (a i) (b i) : ℝ) ≠ 0 := by exact_mod_cast (lo_pos hai hbi).ne'
  rw [← gap_add]
  push_cast
  field_simp

theorem sorted_eventually_input (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 1))
    (hc : ∀ᶠ i in l, (a i).Coprime (b i)) :
    ∀ᶠ i in l, 2 ≤ lo (a i) (b i) ∧ lo (a i) (b i) < max (a i) (b i) ∧
      (lo (a i) (b i)).Coprime (max (a i) (b i)) := by
  filter_upwards [(lo_tendsto a b ha hs).eventually_ge_atTop 2,
    eventually_primitive a b ha hc, hc] with i hi hp hci
  exact ⟨by exact_mod_cast hi, by have h := gap_add (a i) (b i); omega, coprime_sorted hci⟩

theorem central_pairs (G : Geometry) (A : Application G) (m : ℕ) (hm : 4 ≤ m)
    (ha : Tendsto (fun i => (a i : ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i : ℝ)/a i) l (𝓝 1))
    (hb : ∀ᶠ i in l, 0 < b i) (hc : ∀ᶠ i in l, (a i).Coprime (b i)) :
    Tendsto (fun i => Real.log (euler (family G) m (a i) (b i) : ℝ)/(a i : ℝ)) l
      (𝓝 (KroneckerClosedAlphabetEntropy.entropy m 1)) := by
  have h := input_sequence G m 1 _ (central_input_joint G A m hm)
    (fun i => lo (a i) (b i)) (fun i => max (a i) (b i))
    (tendsto_natCast_atTop_iff.mp (lo_tendsto a b ha hs))
    (sorted_slope_tendsto a b ha hs hb) (sorted_eventually_input a b ha hs hc)
  have ht := h.mul (lo_ratio_tendsto a b ha hs)
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [KroneckerLowerEntropyKernel.eventually_positive a ha, hb] with i hai hbi
  exact (entropy_sorted G m (a i) (b i) hai hbi).symm

theorem central_joint (G : Geometry) (A : Application G) (m : ℕ) (hm : 4 ≤ m) :
    JointLimit (height (M:=family G) (m:=m)) slope value 1
      (KroneckerClosedAlphabetEntropy.entropy m 1) := by
  apply jointLimit_of_sequences
  intro p ha hs
  exact central_pairs (fun n => (p n).val.1) (fun n => (p n).val.2) G A m hm
    (tendsto_natCast_atTop_atTop.comp ha) hs
    (Eventually.of_forall fun n => (p n).property.2.1)
    (Eventually.of_forall fun n => (p n).property.2.2.1)

theorem central_positive (G : Geometry) (A : Application G) (m : ℕ) (hm : 4 ≤ m) :
    KroneckerPositiveLimitExchange.PositiveLimit (finiteHomology G) m 1 :=
  ⟨_, KroneckerClosedAlphabetBounds.closed_entropy_positive m hm 1
    ⟨le_rfl, by exact_mod_cast (show 1 ≤ m-2 by omega)⟩, central_joint G A m hm⟩

end KroneckerScopedAllMCentralFrameTransfer
end
end

section

/- Original module: KroneckerRootCrossRatioDecay -/
section
/-! The reflection cross-ratio multiplier lies strictly between zero and
one, so every interior orbit has cross ratio tending to zero geometrically. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootCrossRatioDecay
open Filter
open scoped Topology
open KroneckerEndpointRoots KroneckerRootCrossRatio KroneckerRealReflectionIterates
theorem multiplier {m : ℝ} (hm : 2<m) : 0<lowerRoot m/upperRoot m ∧ lowerRoot m/upperRoot m<1 :=
  ⟨div_pos (lowerRoot_positive hm) (upperRoot_positive hm),
    (div_lt_one (upperRoot_positive hm)).mpr (lower_lt_upper hm)⟩
theorem tendsto {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    Tendsto (fun n => ratio m (orbit m r n)) atTop (𝓝 0) := by
  simp only [KroneckerRootCrossRatioOrbit.formula hm hr]
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (multiplier hm).1.le (multiplier hm).2
  simpa using h.mul_const (ratio m r)
end KroneckerRootCrossRatioDecay
end
end

/- Original module: KroneckerRealReflectionConvergence -/
section
/-! Every real interior reflection orbit converges to the lower endpoint,
proved from the exact cross-ratio formula rather than only monotonicity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealReflectionConvergence
open Filter
open scoped Topology
open KroneckerEndpointRoots KroneckerRootCrossRatio KroneckerRealReflectionIterates
theorem tendsto {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    Tendsto (orbit m r) atTop (𝓝 (lowerRoot m)) := by
  have h := KroneckerRootCrossRatioDecay.tendsto hm hr
  have hn := (tendsto_const_nhds (x := lowerRoot m)).add (h.const_mul (upperRoot m))
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).add h
  have hh := hn.div hd (by norm_num : (1 : ℝ)+0≠0)
  simp only [mul_zero,add_zero,div_one] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall fun n => (solve (interior hm hr n)).symm
end KroneckerRealReflectionConvergence
end
end

/- Original module: KroneckerRealReflectionFiniteHit -/
section
/-! Every interior real slope enters the strip r≤m-1 after finitely many
sink reflections; convergence to the lower endpoint supplies an actual finite index. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealReflectionFiniteHit
open Filter
open scoped Topology
open KroneckerEndpointRoots KroneckerRealReflectionIterates
theorem exists_hit {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    ∃ n : ℕ,orbit m r n≤m-1 := by
  have hl : lowerRoot m<m-1 := by linarith [lowerRoot_lt_one hm]
  have he := (KroneckerRealReflectionConvergence.tendsto hm hr).eventually (eventually_lt_nhds hl)
  obtain ⟨n,hn⟩ := he.exists
  exact ⟨n,hn.le⟩
def firstHit {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) : ℕ :=
  Nat.find (exists_hit hm hr)
theorem at_first {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    orbit m r (firstHit hm hr)≤m-1 := Nat.find_spec (exists_hit hm hr)
theorem before_first {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m))
    (n : ℕ) (hn : n<firstHit hm hr) : m-1<orbit m r n :=
  lt_of_not_ge (Nat.find_min (exists_hit hm hr) hn)
end KroneckerRealReflectionFiniteHit
end
end

/- Original module: KroneckerRealReflectionEntryStrip -/
section
/-! Starting at r≥1, the first entry into r≤m-1 still has r≥1, so finite
reflection reaches the full central strip without overshooting below it. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealReflectionEntryStrip
open KroneckerEndpointRoots KroneckerRealReflectionIterates KroneckerRealReflectionFiniteHit
theorem lower {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) (h1 : 1≤r) :
    1≤orbit m r (firstHit hm hr) := by
  generalize hn : firstHit hm hr=n
  cases n with
  | zero => exact h1
  | succ k =>
    have hk : k<firstHit hm hr := by omega
    have he := before_first hm hr k hk
    have hd := KroneckerRealReflectionDynamics.denominator hm (interior hm hr k)
    change 1≤(m-orbit m r k)⁻¹
    exact (one_le_inv₀ hd).mpr (by linarith)
theorem strip {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) (h1 : 1≤r) :
    orbit m r (firstHit hm hr)∈Set.Icc 1 (m-1) := ⟨lower hm hr h1,at_first hm hr⟩
end KroneckerRealReflectionEntryStrip
end
end

/- Original module: KroneckerCentralStripFold -/
section
/-! A single exchange-after-reflection folds the central strip [1,m-1]
into the fundamental interval [1,m/2], preserving the root interval. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCentralStripFold
open KroneckerEndpointRoots
def fold (m r : ℝ) : ℝ := if r≤m/2 then r else m-r
theorem bounds {m r : ℝ} (hr : r∈Set.Icc 1 (m-1)) : fold m r∈Set.Icc 1 (m/2) := by
  unfold fold
  split_ifs with h
  · exact ⟨hr.1,h⟩
  · constructor <;> linarith [hr.2]
theorem interior {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    fold m r∈Set.Ioo (lowerRoot m) (upperRoot m) := by
  unfold fold
  split_ifs
  · exact hr
  · exact KroneckerSlopeSymmetry.reflect_mem_interior hm hr
end KroneckerCentralStripFold
end
end

/- Original module: KroneckerPositiveLimitCentralFold -/
section
/-! Folding r to m-r preserves positive joint-limit existence, as the
composition of geometric reflection with exchange; the central fold therefore does too. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPositiveLimitCentralFold
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange
variable (H : ∀ m a b,Admissible (space m a b))
theorem reflected (m : ℕ) (hm : 3≤m) (r : ℝ) (hr : r∈interior m) :
    PositiveLimit H m r ↔ PositiveLimit H m ((m : ℝ)-r) := by
  have hd := KroneckerInteriorReflectionObservables.denominator_positive m hm r hr
  have he := (KroneckerPositiveLimitReflection.iff H m hm r hr).trans
    (KroneckerPositiveLimitExchange.iff H m ((m : ℝ)-r)⁻¹ (inv_pos.mpr hd))
  simpa only [inv_inv] using he
theorem folded (m : ℕ) (hm : 3≤m) (r : ℝ) (hr : r∈interior m) :
    PositiveLimit H m r ↔ PositiveLimit H m (KroneckerCentralStripFold.fold (m : ℝ) r) := by
  unfold KroneckerCentralStripFold.fold
  split_ifs
  · rfl
  · exact reflected H m hm r hr
end KroneckerPositiveLimitCentralFold
end
end

/- Original module: KroneckerPositiveLimitIteration -/
section
/-! Any finite number of real reflection steps preserves existence of a
positive actual joint entropy limit, with interval membership checked at every step. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPositiveLimitIteration
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange KroneckerRealReflectionIterates
variable (H : ∀ m a b,Admissible (space m a b))
theorem iff (m : ℕ) (hm : 3≤m) (r : ℝ) (hr : r∈KroneckerManuscriptTarget.interior m) (n : ℕ) :
    PositiveLimit H m r ↔ PositiveLimit H m (orbit (m : ℝ) r n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
    exact ih.trans (KroneckerPositiveLimitReflection.iff H m hm _ (interior hm' hr n))
end KroneckerPositiveLimitIteration
end
end

/- Original module: KroneckerRealFundamentalRepresentative -/
section
/-! Every real interior slope has a fundamental representative obtained by
one optional exchange, finitely many reflections, and one central fold. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRealFundamentalRepresentative
open KroneckerEndpointRoots KroneckerRealReflectionIterates KroneckerRealReflectionFiniteHit
def orient (r : ℝ) : ℝ := if 1≤r then r else r⁻¹
theorem orient_interior {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    orient r∈Set.Ioo (lowerRoot m) (upperRoot m) := by
  unfold orient
  split_ifs
  · exact hr
  · simpa [KroneckerSlopeSymmetry.exchange] using KroneckerSlopeSymmetry.exchange_mem_interior hm hr
theorem orient_ge_one {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) : 1≤orient r := by
  unfold orient
  split_ifs with h
  · exact h
  · exact (one_le_inv₀ ((lowerRoot_positive hm).trans hr.1)).mpr (by linarith)
def representative {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) : ℝ :=
  KroneckerCentralStripFold.fold m (orbit m (orient r) (firstHit hm (orient_interior hm hr)))
theorem fundamental {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    representative hm hr∈Set.Icc 1 (m/2) :=
  KroneckerCentralStripFold.bounds (KroneckerRealReflectionEntryStrip.strip hm (orient_interior hm hr) (orient_ge_one hm hr))
end KroneckerRealFundamentalRepresentative
end
end

/- Original module: KroneckerPositiveLimitFundamentalRepresentative -/
section
/-! Positive joint-limit existence at any real interior slope is equivalent
to existence at its explicit finite-reflection fundamental representative. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPositiveLimitFundamentalRepresentative
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange KroneckerRealFundamentalRepresentative
variable (H : ∀ m a b,Admissible (space m a b))
theorem iff (m : ℕ) (hm : 3≤m) (r : ℝ) (hr : r∈interior m)
    (hm' : (2 : ℝ)<m) : PositiveLimit H m r ↔ PositiveLimit H m (representative hm' hr) := by
  have ho : PositiveLimit H m r ↔ PositiveLimit H m (orient r) := by
    unfold orient
    split_ifs
    · rfl
    · exact KroneckerPositiveLimitExchange.iff H m r ((KroneckerEndpointRoots.lowerRoot_positive hm').trans hr.1)
  have hi := orient_interior hm' hr
  exact ho.trans ((KroneckerPositiveLimitIteration.iff H m hm (orient r) hi _).trans
    (KroneckerPositiveLimitCentralFold.folded H m hm _
      (KroneckerRealReflectionIterates.interior hm' hi _)))
end KroneckerPositiveLimitFundamentalRepresentative
end
end

/- Original module: KroneckerCanonicalInteriorLimitsFromFundamental -/
section
/-! Positive actual joint limits on the closed fundamental interval imply
positive actual joint limits at every strict interior slope for all m≥3. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalInteriorLimitsFromFundamental
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange
variable (H : ∀ m a b,Admissible (space m a b))
theorem transfer (m : ℕ) (hm : 3≤m)
    (h : ∀ r : ℝ,r∈Set.Icc 1 ((m : ℝ)/2) → PositiveLimit H m r)
    (r : ℝ) (hr : r∈interior m) : PositiveLimit H m r := by
  have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
  apply (KroneckerPositiveLimitFundamentalRepresentative.iff H m hm r hr hm').mpr
  exact h _ (KroneckerRealFundamentalRepresentative.fundamental hm' hr)
end KroneckerCanonicalInteriorLimitsFromFundamental
end
end

/- Original module: KroneckerCanonicalEntropyProfileChoice -/
section
/-! Positive interior joint limits define a real entropy profile with zero
outside the open interval. Its endpoint values and interior positivity are exact. -/
noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
namespace KroneckerCanonicalEntropyProfileChoice
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b)) (m : ℕ)
  (h : ∀ r : ℝ,r∈interior m → PositiveLimit H m r)
def profile (r : ℝ) : ℝ := if hr : r∈interior m then Classical.choose (h r hr) else 0
theorem joint (r : ℝ) (hr : r∈interior m) :
    JointLimit (height (M:=family H) (m:=m)) slope value r (profile H m h r) := by
  simpa only [profile,dite_eq_left hr] using (Classical.choose_spec (h r hr)).2
theorem positive (r : ℝ) (hr : r∈interior m) : 0<profile H m h r := by
  simpa only [profile,dite_eq_left hr] using (Classical.choose_spec (h r hr)).1
theorem lower : profile H m h (lowerRoot m)=0 := by simp [profile,KroneckerManuscriptTarget.interior]
theorem upper : profile H m h (upperRoot m)=0 := by simp [profile,KroneckerManuscriptTarget.interior]
end KroneckerCanonicalEntropyProfileChoice
end
end

/- Original module: KroneckerEntropyTitsInequality -/
section
/-! For actual dimensions, the desired finite entropy envelope is equivalent
to the unnormalized log-Euler bound C_m*sqrt(-Tits), with positivity separate. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEntropyTitsInequality
open KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
theorem iff (m : ℕ) (hm : 3≤m) (p : Dimension (family H) m) :
    value p≤bound m (slope p) ↔
      Real.log (euler (family H) m p.val.1 p.val.2 : ℝ)≤
        KroneckerEnvelopeTitsNormalization.coefficient m * Real.sqrt (-(tits m p.val.1 p.val.2 : ℝ)) := by
  rw [show slope p=(p.val.2 : ℝ)/p.val.1 from rfl,
    KroneckerEnvelopeTitsNormalization.identity m _ _ hm p.property.1]
  exact div_le_div_iff_of_pos_right (Nat.cast_pos.mpr p.property.1)
end KroneckerEntropyTitsInequality
end
end

/- Original module: KroneckerFundamentalLogEnvelopeReduction -/
section
/-! A uniform log-Euler estimate in the fundamental region transfers to
every negative-Tits pair with no loss, because both Euler and Tits are preserved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFundamentalLogEnvelopeReduction
open KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
variable (H : ∀ m a b,Admissible (space m a b))
theorem transfer (m : ℕ) (C : ℝ)
    (h : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 →
      Real.log (ordinaryEuler (space m c d) (H m c d) : ℝ)≤C*Real.sqrt (-(tits m c d : ℝ)))
    (a b : ℕ) (hp : Nat.Coprime a b) (ht : tits m a b<0) :
    Real.log (ordinaryEuler (space m a b) (H m a b) : ℝ)≤C*Real.sqrt (-(tits m a b : ℝ)) := by
  obtain ⟨c,d,hc,hcd,hd,hq,hg,he⟩ := KroneckerFundamentalEulerReduction.reduction H m a b ht
  rw [he,← hq]
  apply h c d hc hcd hd
  · change Nat.gcd c d=1;rw [hg];exact hp
  · rw [hq];exact ht
end KroneckerFundamentalLogEnvelopeReduction
end
end

/- Original module: KroneckerFundamentalFiniteEnvelope -/
section
/-! The manuscript finite entropy envelope on the entire actual domain
reduces to a uniform log-Euler inequality only in the fundamental region. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFundamentalFiniteEnvelope
open KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
theorem transfer (m : ℕ) (hm : 3≤m)
    (h : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 →
      Real.log (ordinaryEuler (space m c d) (H m c d) : ℝ)≤
        KroneckerEnvelopeTitsNormalization.coefficient m*Real.sqrt (-(tits m c d : ℝ)))
    (p : Dimension (family H) m) : 0≤value p ∧ value p≤bound m (slope p) := by
  refine ⟨KroneckerCanonicalEntropyNonnegative.nonnegative H m p,?_⟩
  by_cases hi : slope p∈interior m
  · apply (KroneckerEntropyTitsInequality.iff H m hm p).mpr
    exact KroneckerFundamentalLogEnvelopeReduction.transfer H m _ h _ _ p.property.2.2.1
      ((KroneckerIntegralInteriorCriterion.criterion m hm _ _ p.property.1).mp hi)
  · have he : slope p∉interval m := by
      intro hh
      have hn := KroneckerIntegralEndpointExclusion.endpoints m hm p.val.1 p.val.2 p.property.1
      exact hi ⟨lt_of_le_of_ne hh.1 hn.1.symm,lt_of_le_of_ne hh.2 hn.2⟩
    rw [KroneckerExteriorEntropyZero.value_zero H m hm p he]
    exact mul_nonneg (KroneckerEnvelopeTitsNormalization.positive m hm).le (Real.sqrt_nonneg _)
end KroneckerFundamentalFiniteEnvelope
end
end

/- Original module: KroneckerCanonicalEnvelopeEndpointLimits -/
section
/-! A finite canonical entropy envelope gives both full-domain endpoint
joint limits, including exterior real-root sequences, by a uniform squeeze. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalEnvelopeEndpointLimits
open Filter KroneckerLogic
open scoped Topology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))
theorem at_root (m : ℕ) (hm : 3≤m)
    (h : ∀ p : Dimension (family H) m,0≤value p ∧ value p≤bound m (slope p))
    (r : ℝ) (hr : (m : ℝ)*r-1-r^2=0) :
    JointLimit (height (M:=family H) (m:=m)) slope value r 0 := by
  apply jointLimit_of_sequences
  intro p ha hs
  have hb := KroneckerCanonicalInteriorBoundExtension.extend_bound H m hm
    (KroneckerEnvelopeTitsNormalization.coefficient m) 0
    (KroneckerEnvelopeTitsNormalization.positive m hm).le (le_refl _) (by
      intro q _;simpa [bound,KroneckerEnvelopeTitsNormalization.coefficient] using h q)
  exact endpoint_squeeze (m : ℝ) r (KroneckerEnvelopeTitsNormalization.coefficient m) 0
    (tendsto_natCast_atTop_atTop.comp ha) hs hr (Filter.Eventually.of_forall fun n => hb (p n))
end KroneckerCanonicalEnvelopeEndpointLimits
end
end

/- Original module: KroneckerCanonicalProfileClosedJointLimits -/
section
/-! Interior positive limits and a finite entropy envelope supply the
chosen profile's joint limits on the entire closed root interval, including both endpoints. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalProfileClosedJointLimits
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange KroneckerEndpointRoots KroneckerCanonicalEntropyProfileChoice
variable (H : ∀ m a b,Admissible (space m a b))
theorem joint (m : ℕ) (hm : 3≤m) (h : ∀ r : ℝ,r∈interior m → PositiveLimit H m r)
    (hb : ∀ p : Dimension (family H) m,0≤value p ∧ value p≤bound m (slope p))
    (r : ℝ) (hr : r∈interval m) :
    JointLimit (height (M:=family H) (m:=m)) slope value r (profile H m h r) := by
  have hm' : (2 : ℝ)≤m := by exact_mod_cast (show 2≤m by omega)
  by_cases hl : r=lowerRoot m
  · subst r
    rw [KroneckerCanonicalEntropyProfileChoice.lower]
    exact KroneckerCanonicalEnvelopeEndpointLimits.at_root H m hm hb _ (lowerRoot_quadratic hm')
  by_cases hu : r=upperRoot m
  · subst r
    rw [KroneckerCanonicalEntropyProfileChoice.upper]
    exact KroneckerCanonicalEnvelopeEndpointLimits.at_root H m hm hb _ (upperRoot_quadratic hm')
  exact KroneckerCanonicalEntropyProfileChoice.joint H m h r ⟨lt_of_le_of_ne hr.1 (Ne.symm hl),lt_of_le_of_ne hr.2 hu⟩
end KroneckerCanonicalProfileClosedJointLimits
end
end

/- Original module: KroneckerCanonicalProfileContinuity -/
section
/-! The chosen actual entropy profile is continuous on the closed interval
once every slope is nonvacuous, using genuine full-domain joint limits. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalProfileContinuity
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange KroneckerCanonicalEntropyProfileChoice
variable (H : ∀ m a b,Admissible (space m a b))
theorem continuous (m : ℕ) (hm : 3≤m) (h : ∀ r : ℝ,r∈interior m → PositiveLimit H m r)
    (hb : ∀ p : Dimension (family H) m,0≤value p ∧ value p≤bound m (slope p))
    (hn : ∀ r∈interval m,Approximable (height (M:=family H) (m:=m)) slope r) :
    ContinuousOn (profile H m h) (interval m) :=
  continuousOn_of_jointLimits _ _ _ (KroneckerCanonicalProfileClosedJointLimits.joint H m hm h hb) hn
end KroneckerCanonicalProfileContinuity
end
end

/- Original module: KroneckerCanonicalProfileEnvelope -/
section
/-! The chosen actual profile is nonnegative and obeys the exact manuscript
envelope everywhere on the closed interval, by nonvacuous limit transfer. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalProfileEnvelope
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange KroneckerCanonicalEntropyProfileChoice
variable (H : ∀ m a b,Admissible (space m a b))
theorem bounds (m : ℕ) (hm : 3≤m) (h : ∀ r : ℝ,r∈interior m → PositiveLimit H m r)
    (hb : ∀ p : Dimension (family H) m,0≤value p ∧ value p≤bound m (slope p))
    (hn : ∀ r∈interval m,Approximable (height (M:=family H) (m:=m)) slope r)
    (r : ℝ) (hr : r∈interval m) : 0≤profile H m h r ∧ profile H m h r≤bound m r :=
  KroneckerCanonicalLimitEnvelope.limit_bounds H m hb r _ (hn r hr)
    (KroneckerCanonicalProfileClosedJointLimits.joint H m hm h hb r hr)
end KroneckerCanonicalProfileEnvelope
end
end

/- Original module: KroneckerCanonicalMainFromFundamental -/
section
/-! The exact manuscript MainConclusion for canonical quotient spaces follows
from three explicit fundamental-region inputs. Those inputs are not asserted proved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalMainFromFundamental
open KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange KroneckerCanonicalEntropyProfileChoice
variable (H : ∀ m a b,Admissible (space m a b))
theorem main (m : ℕ) (hm : 3≤m)
    (hN : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 → Nonempty (space m c d))
    (hU : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 →
      Real.log (ordinaryEuler (space m c d) (H m c d) : ℝ)≤
        KroneckerEnvelopeTitsNormalization.coefficient m*Real.sqrt (-(tits m c d : ℝ)))
    (hL : ∀ r : ℝ,r∈Set.Icc 1 ((m : ℝ)/2) → PositiveLimit H m r) : MainConclusion (family H) m := by
  let h := KroneckerCanonicalInteriorLimitsFromFundamental.transfer H m hm hL
  have hb := KroneckerFundamentalFiniteEnvelope.transfer H m hm hU
  have hn := KroneckerCanonicalClosedApproximableFromFundamental.approximable H m hm hN
  refine ⟨profile H m h,KroneckerCanonicalProfileContinuity.continuous H m hm h hb hn,
    KroneckerCanonicalEntropyProfileChoice.lower H m h,KroneckerCanonicalEntropyProfileChoice.upper H m h,
    KroneckerCanonicalEntropyProfileChoice.positive H m h,?_⟩
  intro r hr
  exact ⟨(KroneckerCanonicalProfileEnvelope.bounds H m hm h hb hn r hr).1,
    KroneckerCanonicalProfileClosedJointLimits.joint H m hm h hb r hr⟩
end KroneckerCanonicalMainFromFundamental
end
end

/- Original module: KroneckerCanonicalMainTwoInputs -/
section
/-! Only two fundamental analytic inputs remain in the exact main-conclusion reduction; nonemptiness is discharged. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalMainTwoInputs
open KroneckerLogic KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
open KroneckerPositiveLimitExchange
theorem main (m : ℕ) (hm : 3≤m)
 (hU : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 →
 Real.log (ordinaryEuler (space m c d) (H m c d):ℝ)≤KroneckerEnvelopeTitsNormalization.coefficient m*Real.sqrt (-(tits m c d:ℝ)))
 (hL : ∀ r : ℝ,r∈Set.Icc 1 ((m:ℝ)/2) → PositiveLimit H m r) : MainConclusion (family H) m :=
 KroneckerCanonicalMainFromFundamental.main H m hm
  (fun c d hc hcd hu hp _ => KroneckerFundamentalNonemptyProved.nonempty m hm c d hc hcd hu hp) hU hL
end KroneckerCanonicalMainTwoInputs
end
end

/- Original module: KroneckerCanonicalAllMTwoInputs -/
section
/-! The all-m target now reduces to uniform fundamental upper estimates and positive central joint limits, plus finite homology. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalAllMTwoInputs
open KroneckerLogic KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
open KroneckerPositiveLimitExchange
structure AnalyticInputs (m : ℕ) : Prop where
 upper : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 →
  Real.log (ordinaryEuler (space m c d) (H m c d):ℝ)≤KroneckerEnvelopeTitsNormalization.coefficient m*Real.sqrt (-(tits m c d:ℝ))
 positiveLimit : ∀ r : ℝ,r∈Set.Icc 1 ((m:ℝ)/2) → PositiveLimit H m r
end KroneckerCanonicalAllMTwoInputs
end
end

/- Original module: KroneckerScopedOtherFundamental -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedOtherFundamental
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerScopedActualFrameApplication
open KroneckerPositiveLimitExchange KroneckerNegativeTitsSymmetry

theorem fundamental_four (G : Geometry) (A : Application G)
    (r : ℝ) (hr : r ∈ Set.Icc 1 ((4:ℝ)/2)) : PositiveLimit (finiteHomology G) 4 r := by
  by_cases h₁ : r = 1
  · subst r
    exact KroneckerScopedAllMCentralFrameTransfer.central_positive G A 4 (by decide)
  by_cases h₂ : r = 2
  · subst r
    exact KroneckerScopedActualFourBoundary.four_positive G A
  exact KroneckerScopedActualFrameJointTransfer.interior_positive G A 4 (by decide) r
    ⟨lt_of_le_of_ne hr.1 (Ne.symm h₁), by norm_num; have := hr.2; norm_num at this; exact lt_of_le_of_ne this h₂⟩

theorem fundamental_large (G : Geometry) (A : Application G) (m : ℕ) (hm : 5 ≤ m)
    (r : ℝ) (hr : r ∈ Set.Icc 1 ((m:ℝ)/2)) : PositiveLimit (finiteHomology G) m r := by
  by_cases h₁ : r = 1
  · subst r
    exact KroneckerScopedAllMCentralFrameTransfer.central_positive G A m (by omega)
  have hcast : ((m-2 : ℕ):ℝ) = (m:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hmR : (5:ℝ) ≤ m := by exact_mod_cast hm
  exact KroneckerScopedActualFrameJointTransfer.interior_positive G A m (by omega) r
    ⟨lt_of_le_of_ne hr.1 (Ne.symm h₁), by rw [hcast]; linarith [hr.2]⟩

end KroneckerScopedOtherFundamental
end
end
end

