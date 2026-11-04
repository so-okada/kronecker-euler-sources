import KroneckerApproximableSequenceCriterion
import KroneckerRootPairAllowed
import KroneckerSlopeSymmetry
import KroneckerPrimitiveApproximation
import KroneckerFundamentalEulerReduction

section

/- Original module: KroneckerExchangeAllowedDimensions -/
section
/-! The actual admissible dimension domain, including moduli nonemptiness, is
invariant under exchange. This is an equivalence on the manuscript domain. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeAllowedDimensions
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
open KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))

theorem allowed_iff (m a b : ℕ) : Allowed (family H) m a b ↔ Allowed (family H) m b a := by
  change (0<a ∧ 0<b ∧ a.Coprime b ∧ Nonempty (space m a b)) ↔
    (0<b ∧ 0<a ∧ b.Coprime a ∧ Nonempty (space m b a))
  rw [KroneckerExchangeEuler.nonempty_iff m a b,Nat.coprime_comm]
  tauto

def exchange {m : ℕ} (p : Dimension (family H) m) : Dimension (family H) m :=
  ⟨(p.val.2,p.val.1),(allowed_iff H _ _ _).mp p.property⟩

theorem exchange_involutive {m : ℕ} : Function.Involutive (@exchange H m) := fun _ => Subtype.ext rfl

def dimensionEquiv (m : ℕ) : Dimension (family H) m ≃ Dimension (family H) m :=
  ⟨exchange H,exchange H,exchange_involutive H,exchange_involutive H⟩
end KroneckerExchangeAllowedDimensions
end
end

/- Original module: KroneckerExchangeObservables -/
section
/-! Exact normalization laws for the manuscript observables on actual moduli.
Exchange divides entropy-per-source-dimension by the old slope. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeObservables
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerExchangeAllowedDimensions
variable (H : ∀ m a b,Admissible (space m a b)) {m : ℕ}

theorem slope_positive (p : Dimension (family H) m) : 0<slope p := by
  exact div_pos (Nat.cast_pos.mpr p.property.2.1) (Nat.cast_pos.mpr p.property.1)

theorem slope_exchange (p : Dimension (family H) m) : slope (exchange H p)=(slope p)⁻¹ := by
  simp [KroneckerManuscriptTarget.slope,exchange]

theorem height_exchange (p : Dimension (family H) m) :
    (height (exchange H p) : ℝ)=slope p*(height p : ℝ) := by
  have ha : (p.val.1 : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr p.property.1)
  simp [height,KroneckerManuscriptTarget.slope,exchange,ha]

theorem value_exchange (p : Dimension (family H) m) : value (exchange H p)=value p/slope p := by
  have ha : (p.val.1 : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr p.property.1)
  have hb : (p.val.2 : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr p.property.2.1)
  have he := KroneckerExchangeEuler.euler_eq m p.val.1 p.val.2 (H _ _ _) (H _ _ _)
  change Real.log (ordinaryEuler (space m p.val.2 p.val.1) (H _ _ _) : ℝ)/p.val.2 =
    (Real.log (ordinaryEuler (space m p.val.1 p.val.2) (H _ _ _) : ℝ)/p.val.1)/(p.val.2/p.val.1)
  rw [he]
  field_simp
end KroneckerExchangeObservables
end
end
end

section

/-! Along every actual admissible sequence approaching a positive slope,
source and sink heights tend to infinity together. This controls the changed
normalization in exchange of joint limits, including endpoint approaches. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeHeightGrowth
open Filter
open scoped Topology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerExchangeAllowedDimensions KroneckerExchangeObservables
variable (H : ∀ m a b,Admissible (space m a b)) {m : ℕ}

theorem height_tendsto (p : ℕ → Dimension (family H) m) {r : ℝ} (hr : 0<r)
    (ha : Tendsto (fun n => height (p n)) atTop atTop)
    (hs : Tendsto (fun n => slope (p n)) atTop (𝓝 r)) :
    Tendsto (fun n => height (exchange H (p n))) atTop atTop := by
  have hs' : ∀ᶠ n in atTop,r/2≤slope (p n) :=
    (hs.eventually (eventually_gt_nhds (by linarith : r/2<r))).mono (fun _ h => h.le)
  apply tendsto_atTop.mpr
  intro N
  obtain ⟨K,hK⟩ := exists_nat_gt ((N : ℝ)/(r/2))
  filter_upwards [hs',ha.eventually (eventually_ge_atTop K)] with n hn hk
  have hK' : (K : ℝ)≤height (p n) := by exact_mod_cast hk
  have hmul : (N : ℝ) < (r/2)*(K : ℝ) := by
    have hh := (div_lt_iff₀ (by linarith : 0<r/2)).mp hK
    nlinarith
  have hge : (N : ℝ)≤height (exchange H (p n)) := by
    rw [height_exchange]
    have ha0 : (0 : ℝ)≤height (p n) := Nat.cast_nonneg _
    nlinarith
  exact_mod_cast hge
end KroneckerExchangeHeightGrowth
end
end

section

/-! Actual nonempty admissible dimension vectors approximate a positive slope
if and only if they approximate its reciprocal. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeApproximable
open Filter KroneckerLogic
open scoped Topology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerExchangeAllowedDimensions KroneckerExchangeObservables
variable (H : ∀ m a b,Admissible (space m a b)) {m : ℕ}

theorem exchange {r : ℝ} (hr : 0<r)
    (h : Approximable (height (M:=family H) (m:=m)) slope r) :
    Approximable (height (M:=family H) (m:=m)) slope r⁻¹ := by
  obtain ⟨p⟩ := approaching_nonempty _ _ h
  apply KroneckerApproximableSequenceCriterion.of_sequence _ _
    (fun n => KroneckerExchangeAllowedDimensions.exchange H (p.val n))
  · exact KroneckerExchangeHeightGrowth.height_tendsto H _ hr p.property.1 p.property.2
  · simpa only [slope_exchange] using p.property.2.inv₀ (ne_of_gt hr)
end KroneckerExchangeApproximable
end
end

section

/- Original module: KroneckerRootPairSlopeLower -/
section
/-! Successive root ratios lie above m-1, so the positive branch of the
quadratic formula is forced rather than chosen as an asymptotic assumption. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootPairSlopeLower
open KroneckerRootPairRecurrence

theorem lower (m : ℕ) (hm : 3≤m) (n : ℕ) :
    (m : ℝ)-1<((pair m (n+1)).2 : ℝ)/(pair m (n+1)).1 := by
  have hg : ((pair m n).1 : ℝ)<(pair m n).2 := by exact_mod_cast growth m hm n
  have hb : (0 : ℝ)<(pair m n).2 := lt_of_le_of_lt (Nat.cast_nonneg _) hg
  have he : ((pair m n).1 : ℝ)+(pair m (n+1)).2=(m : ℝ)*(pair m n).2 := by
    exact_mod_cast untruncated m hm n
  change (m : ℝ)-1<((pair m (n+1)).2 : ℝ)/(pair m n).2
  apply (lt_div_iff₀ hb).mpr
  nlinarith

theorem above_half (m : ℕ) (hm : 3≤m) (n : ℕ) :
    (m : ℝ)/2<((pair m (n+1)).2 : ℝ)/(pair m (n+1)).1 := by
  have h := lower m hm n
  have hm' : (3 : ℝ)≤m := by exact_mod_cast hm
  linarith
end KroneckerRootPairSlopeLower
end
end

/- Original module: KroneckerRootPairQuadraticFormula -/
section
/-! Exact square-root formula for every positive root ratio. The correction
term is the reciprocal square of the actual source dimension. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootPairQuadraticFormula
open KroneckerRootPairRecurrence

theorem formula (m : ℕ) (hm : 3≤m) (n : ℕ) :
    ((pair m (n+1)).2 : ℝ)/(pair m (n+1)).1 =
      ((m : ℝ)+Real.sqrt ((m : ℝ)^2-4+4/((pair m (n+1)).1 : ℝ)^2))/2 := by
  let a : ℝ := (pair m (n+1)).1
  let b : ℝ := (pair m (n+1)).2
  have ha : 0<a := by
    have hn := source_ge_index m hm (n+1)
    dsimp [a]
    exact_mod_cast (show 0<(pair m (n+1)).1 by omega)
  have ht : a^2+b^2-(m : ℝ)*a*b=1 := by
    dsimp [a,b]
    exact_mod_cast KroneckerRootPairHeightGrowth.tits_one m hm (n+1)
  have hh : (m : ℝ)/2<b/a := KroneckerRootPairSlopeLower.above_half m hm n
  have he : (2*(b/a)-(m : ℝ))^2=(m : ℝ)^2-4+4/a^2 := by
    field_simp
    nlinarith
  have hs : Real.sqrt ((m : ℝ)^2-4+4/a^2)=2*(b/a)-(m : ℝ) := by
    rw [←he,Real.sqrt_sq (by linarith)]
  change b/a=((m : ℝ)+Real.sqrt ((m : ℝ)^2-4+4/a^2))/2
  rw [hs]
  ring
end KroneckerRootPairQuadraticFormula
end
end

/- Original module: KroneckerRootPairSlopeConvergence -/
section
/-! The actual integer root sequence converges in slope to the upper endpoint.
The proof uses its diverging source dimensions and exact quadratic formula. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootPairSlopeConvergence
open Filter KroneckerRootPairRecurrence KroneckerEndpointRoots
open scoped Topology

theorem height (m : ℕ) (hm : 3≤m) :
    Tendsto (fun n => (pair m (n+1)).1) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro n
  change n≤(pair m (n+1)).1
  have h := source_ge_index m hm (n+1)
  omega

theorem slope (m : ℕ) (hm : 3≤m) :
    Tendsto (fun n => ((pair m (n+1)).2 : ℝ)/(pair m (n+1)).1) atTop (𝓝 (upperRoot m)) := by
  have ha : Tendsto (fun n => ((pair m (n+1)).1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (height m hm)
  have hi := tendsto_inv_atTop_zero.comp ha
  have hc : Tendsto (fun n => (4 : ℝ)/((pair m (n+1)).1 : ℝ)^2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,inv_pow] using (tendsto_const_nhds.mul (hi.pow 2))
  have hs := ((tendsto_const_nhds (x:=((m : ℝ)^2-4))).add hc).sqrt
  have hf := ((tendsto_const_nhds (x:=(m : ℝ))).add hs).div_const 2
  convert hf using 1
  · funext n
    exact KroneckerRootPairQuadraticFormula.formula m hm n
  · simp [upperRoot,discriminant]
end KroneckerRootPairSlopeConvergence
end
end

/- Original module: KroneckerCanonicalEndpointApproximable -/
section
/-! Both endpoints are nonvacuously approximated by actual positive coprime
stable dimension vectors of unbounded height. No nonemptiness oracle is used. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalEndpointApproximable
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
open KroneckerManuscriptTarget KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))

theorem upper (m : ℕ) (hm : 3≤m) :
    Approximable (height (M:=family H) (m:=m)) slope (upperRoot m) :=
  KroneckerApproximableSequenceCriterion.of_sequence _ _ (KroneckerRootPairAllowed.dimension H m hm)
    (KroneckerRootPairSlopeConvergence.height m hm) (KroneckerRootPairSlopeConvergence.slope m hm)

theorem lower (m : ℕ) (hm : 3≤m) :
    Approximable (height (M:=family H) (m:=m)) slope (lowerRoot m) := by
  have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
  have h := KroneckerExchangeApproximable.exchange H (upperRoot_positive hm') (upper H m hm)
  simpa [←KroneckerSlopeSymmetry.exchange_upperRoot hm',KroneckerSlopeSymmetry.exchange] using h
end KroneckerCanonicalEndpointApproximable
end
end
end

section

/- Original module: KroneckerArrowPadding -/
section
/-! Adding zero arrows preserves and reflects stability for all subspaces.
The original arrows are retained exactly, for any finite arrow-count inclusion. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerArrowPadding
open KroneckerReflectionPairModel
variable {m n a b : ℕ}

def pad (_hmn : m≤n) (R : PairRep m a b) : PairRep n a b := fun j => if h : j.val<m then R ⟨j.val,h⟩ else 0

variable (hmn : m≤n) (R : PairRep m a b)

theorem retained (i : Fin m) : pad hmn R (Fin.castLE hmn i)=R i := by
  simp [pad,i.isLt]

theorem invariant_iff (U : Submodule ℂ (KroneckerFiniteQuiverHom.Space a))
    (W : Submodule ℂ (KroneckerFiniteQuiverHom.Space b)) :
    PairInvariant (pad hmn R) U W ↔ PairInvariant R U W := by
  constructor
  · intro h i x hx
    simpa only [retained] using h (Fin.castLE hmn i) x hx
  · intro h j x hx
    unfold pad
    split_ifs with hj
    · exact h ⟨j.val,hj⟩ x hx
    · simpa using W.zero_mem

theorem stable_iff : PairStable (pad hmn R) ↔ PairStable R := by
  unfold PairStable
  simp only [invariant_iff]
end KroneckerArrowPadding
end
end

/- Original module: KroneckerArrowCountNonemptyMonotonicity -/
section
/-! Nonemptiness of actual canonical stable moduli is monotone in the number
of arrows, via a concrete stable representation with zero extra arrows. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerArrowCountNonemptyMonotonicity
open KroneckerReflectionPairModel KroneckerCanonicalKroneckerModuli

theorem nonempty (m n a b : ℕ) (hmn : m≤n) (h : Nonempty (space m a b)) :
    Nonempty (space n a b) := by
  obtain ⟨R,hR⟩ := (space_nonempty_iff m a b).mp h
  let P := fromRepresentation R
  have hp : PairStable P := (KroneckerReflectionPairStability.stable_iff P).mp hR
  have hpad := (KroneckerArrowPadding.stable_iff hmn P).mpr hp
  exact (space_nonempty_iff n a b).mpr
    ⟨toRepresentation (KroneckerArrowPadding.pad hmn P),
      (KroneckerReflectionPairStability.stable_iff _).mpr hpad⟩
end KroneckerArrowCountNonemptyMonotonicity
end
end

/- Original module: KroneckerCanonicalTwoArrowRoots -/
section
/-! Concrete two-arrow real roots supply stable adjacent dimension pairs;
zero-arrow padding realizes them for every larger arrow count. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalTwoArrowRoots
open KroneckerCanonicalKroneckerModuli

theorem two_arrow (n : ℕ) : Nonempty (space 2 n (n+1)) := by
  induction n with
  | zero => exact KroneckerCanonicalSimpleRoots.sink_nonempty 2
  | succ n ih =>
    have h := KroneckerCanonicalRootNonemptiness.successor_nonempty 2 n (n+1) (by omega) ih
    have he : 2*(n+1)-n=n+2 := by omega
    simpa only [he] using h

theorem all_arrows (m : ℕ) (hm : 2≤m) (n : ℕ) : Nonempty (space m n (n+1)) :=
  KroneckerArrowCountNonemptyMonotonicity.nonempty 2 m n (n+1) hm (two_arrow n)
end KroneckerCanonicalTwoArrowRoots
end
end

/- Original module: KroneckerCanonicalUnitSlopeSequence -/
section
/-! Adjacent dimensions provide an actual stable, positive, coprime sequence
of unbounded height approaching the interior slope one for every m≥2. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalUnitSlopeSequence
open Filter KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerLogic
open scoped Topology
variable (H : ∀ m a b,Admissible (space m a b))

def dimension (m : ℕ) (hm : 2≤m) (n : ℕ) : Dimension (family H) m :=
  ⟨(n+1,n+2),by omega,by omega,KroneckerTitsOnePrimitive.coprime 2 (n+1) (n+2) (by push_cast;ring),
    KroneckerCanonicalTwoArrowRoots.all_arrows m hm (n+1)⟩

theorem height_tendsto (m : ℕ) (hm : 2≤m) :
    Tendsto (fun n => height (dimension H m hm n)) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro n
  change n≤n+1
  omega

theorem slope_tendsto (m : ℕ) (hm : 2≤m) :
    Tendsto (fun n => slope (dimension H m hm n)) atTop (𝓝 1) := by
  have ha : Tendsto (fun n => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (height_tendsto H m hm)
  have hi := tendsto_inv_atTop_zero.comp ha
  have ht := (tendsto_const_nhds (x:=(1 : ℝ))).add hi
  convert ht using 1
  · funext n
    change ((n+2 : ℕ) : ℝ)/(n+1 : ℕ)=1+((n+1 : ℕ) : ℝ)⁻¹
    have hn : ((n+1 : ℕ) : ℝ)≠0 := by positivity
    push_cast
    field_simp
    ring
  · norm_num

theorem approximable (m : ℕ) (hm : 2≤m) :
    Approximable (height (M:=family H) (m:=m)) slope 1 :=
  KroneckerApproximableSequenceCriterion.of_sequence _ _ (dimension H m hm)
    (height_tendsto H m hm) (slope_tendsto H m hm)
end KroneckerCanonicalUnitSlopeSequence
end
end

/- Original module: KroneckerPrimitiveInteriorApproximation -/
section
/-! Strictly interior slopes above one admit arbitrarily tall positive
primitive approximants that remain inside the root interval, with explicit error control. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPrimitiveInteriorApproximation
open KroneckerEndpointRoots KroneckerManuscriptTarget
theorem approximation (m : ℕ) (r : ℝ) (hr : 1<r) (hi : r∈interior m) (δ : ℝ) (hδ : 0<δ) (N : ℕ) :
    ∃ a b : ℕ,N≤a ∧ 0<a ∧ 0<b ∧ a.Coprime b ∧ (b : ℝ)/a∈interior m ∧ dist ((b : ℝ)/a) r<δ := by
  let ε := min δ (min (r-lowerRoot m) (upperRoot m-r))
  have hε : 0<ε := lt_min hδ (lt_min (sub_pos.mpr hi.1) (sub_pos.mpr hi.2))
  obtain ⟨K,hK⟩ := exists_nat_gt (2/ε)
  obtain ⟨a,b,hNa,ha,hb,hp,he⟩ := KroneckerPrimitiveApproximation.primitive_approximation r hr (max N K)
  have ha' : (0 : ℝ)<a := by exact_mod_cast (show 0<a by omega)
  have hKa : (K : ℝ)≤a := by exact_mod_cast (show K≤a by omega)
  have hsmall : 2/(a : ℝ)<ε := by
    apply (div_lt_iff₀ ha').mpr
    have hh := (div_lt_iff₀ hε).mp hK
    nlinarith
  have hh := he.trans_lt hsmall
  have hl := hh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hu := hh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a,b,by omega,by omega,by omega,hp,?_,hh.trans_le (min_le_left _ _)⟩
  rw [Real.dist_eq,abs_lt] at hl hu
  exact ⟨by linarith [hl.1],by linarith [hu.2]⟩
end KroneckerPrimitiveInteriorApproximation
end
end

/- Original module: KroneckerCanonicalUpperInteriorApproximable -/
section
/-! Fundamental-region nonemptiness supplies actual nonvacuity at every
strictly interior slope above one, using primitive integer approximants. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalUpperInteriorApproximable
open KroneckerLogic KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
theorem approximable (m : ℕ) (hm : 3≤m)
    (h : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 → Nonempty (space m c d))
    (r : ℝ) (hr : 1<r) (hi : r∈interior m) :
    Approximable (height (M:=family H) (m:=m)) slope r := by
  intro δ hδ N
  obtain ⟨a,b,hN,ha,hb,hp,hri,he⟩ := KroneckerPrimitiveInteriorApproximation.approximation m r hr hi δ hδ N
  have hn := KroneckerFundamentalNonemptyReduction.transfer m h a b hp
    ((KroneckerIntegralInteriorCriterion.criterion m hm a b ha).mp hri)
  exact ⟨⟨(a,b),ha,hb,hp,hn⟩,hN,he⟩
end KroneckerCanonicalUpperInteriorApproximable
end
end

/- Original module: KroneckerCanonicalInteriorApproximableFromFundamental -/
section
/-! Fundamental-region nonemptiness implies actual nonvacuity at every
interior slope, with the unit slope supplied unconditionally and lower slopes exchanged. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalInteriorApproximableFromFundamental
open KroneckerLogic KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli
open KroneckerOrdinarySingularEuler KroneckerManuscriptTarget KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))
theorem approximable (m : ℕ) (hm : 3≤m)
    (h : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 → Nonempty (space m c d))
    (r : ℝ) (hi : r∈interior m) : Approximable (height (M:=family H) (m:=m)) slope r := by
  rcases lt_trichotomy r 1 with hr | rfl | hr
  · have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
    have hp : 0<r := (lowerRoot_positive hm').trans hi.1
    have hri : r⁻¹∈interior m := by
      change r⁻¹ ∈ Set.Ioo (lowerRoot m) (upperRoot m)
      simpa only [KroneckerSlopeSymmetry.exchange,one_div] using
        KroneckerSlopeSymmetry.exchange_mem_interior hm' hi
    have hgt : 1<r⁻¹ := (one_lt_inv₀ hp).mpr hr
    have hh := KroneckerCanonicalUpperInteriorApproximable.approximable H m hm h _ hgt hri
    simpa only [inv_inv] using KroneckerExchangeApproximable.exchange H (inv_pos.mpr hp) hh
  · exact KroneckerCanonicalUnitSlopeSequence.approximable H m (by omega)
  · exact KroneckerCanonicalUpperInteriorApproximable.approximable H m hm h r hr hi
end KroneckerCanonicalInteriorApproximableFromFundamental
end
end

/- Original module: KroneckerCanonicalClosedApproximableFromFundamental -/
section
/-! The complete closed-root-interval nonvacuity gate is reduced to actual
fundamental-region nonemptiness; endpoint sequences were already constructed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalClosedApproximableFromFundamental
open KroneckerLogic KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli
open KroneckerOrdinarySingularEuler KroneckerManuscriptTarget KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))
theorem approximable (m : ℕ) (hm : 3≤m)
    (h : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 → Nonempty (space m c d))
    (r : ℝ) (hi : r∈interval m) : Approximable (height (M:=family H) (m:=m)) slope r := by
  by_cases hl : r=lowerRoot m
  · subst r;exact KroneckerCanonicalEndpointApproximable.lower H m hm
  by_cases hu : r=upperRoot m
  · subst r;exact KroneckerCanonicalEndpointApproximable.upper H m hm
  exact KroneckerCanonicalInteriorApproximableFromFundamental.approximable H m hm h r
    ⟨lt_of_le_of_ne hi.1 (Ne.symm hl),lt_of_le_of_ne hi.2 hu⟩
end KroneckerCanonicalClosedApproximableFromFundamental
end
end
end

section

/-! Actual-Euler joint limits transform under source/sink exchange with the
correct slope-dependent height normalization, for all admissible sequences. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerExchangeJointLimit
open Filter
open scoped Topology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerExchangeAllowedDimensions KroneckerExchangeObservables KroneckerLogic
variable (H : ∀ m a b,Admissible (space m a b)) {m : ℕ}

theorem joint_exchange {r L : ℝ} (hr : 0<r)
    (h : JointLimit (height (M:=family H) (m:=m)) slope value r L) :
    JointLimit (height (M:=family H) (m:=m)) slope value r⁻¹ (L/r) := by
  apply jointLimit_of_sequences
  intro p ha hs
  have hinv : 0<r⁻¹ := inv_pos.mpr hr
  have heigh := KroneckerExchangeHeightGrowth.height_tendsto H p hinv ha hs
  have hsl : Tendsto (fun n => slope (exchange H (p n))) atTop (𝓝 r) := by
    simpa only [slope_exchange,inv_inv] using hs.inv₀ (ne_of_gt hinv)
  have hv := jointLimit_sequence _ _ _ h (fun n => exchange H (p n)) heigh hsl
  have hv' := hv.mul hs
  have he : ∀ n,value (p n)=value (exchange H (p n))*slope (p n) := by
    intro n
    rw [value_exchange]
    exact (div_mul_cancel₀ _ (ne_of_gt (slope_positive H (p n)))).symm
  simp_rw [←he] at hv'
  simpa only [div_eq_mul_inv] using hv'
end KroneckerExchangeJointLimit
end
end

