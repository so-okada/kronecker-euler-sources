import KroneckerScopedDeleteActualCentral
import KroneckerScopedOtherFundamental

section

/- Original module: KroneckerCanonicalNonemptyFundamentalCriterion -/
section
/-! The full primitive nonempty-domain theorem follows from nonemptiness in
the fundamental region; real roots and null-root exclusion are already proved. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalNonemptyFundamentalCriterion
open KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli
theorem criterion (m : ℕ) (hm : 3≤m)
    (h : ∀ c d : ℕ,0<c → c≤d → 2*d≤m*c → Nat.Coprime c d → tits m c d<0 → Nonempty (space m c d))
    (a b : ℕ) (ha : 0<a) (hp : Nat.Coprime a b) :
    Nonempty (space m a b) ↔ tits m a b≤1 := by
  constructor
  · exact KroneckerCanonicalTitsNecessary.tits_le_one m a b ha
  · intro ht
    by_cases hn : tits m a b<0
    · exact KroneckerFundamentalNonemptyReduction.transfer m h a b hp hn
    · have hz : tits m a b≠0 := by
        intro he
        have hh := KroneckerNullRootExclusion.zero m hm a b he
        omega
      have he : tits m a b=1 := by omega
      exact KroneckerRealRootRealization.nonempty m hm a b he
end KroneckerCanonicalNonemptyFundamentalCriterion
end
end

/- Original module: KroneckerPrimitiveNonemptyCriterionProved -/
section
/-! The exact primitive Tits nonemptiness criterion is proved for actual canonical quotient spaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPrimitiveNonemptyCriterionProved
open KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli
theorem criterion (m : ℕ) (hm : 3≤m) (a b : ℕ) (ha : 0<a) (hp : Nat.Coprime a b) :
 Nonempty (space m a b) ↔ tits m a b≤1 :=
 KroneckerCanonicalNonemptyFundamentalCriterion.criterion m hm
  (fun c d hc hcd hu hp _ => KroneckerFundamentalNonemptyProved.nonempty m hm c d hc hcd hu hp) a b ha hp
end KroneckerPrimitiveNonemptyCriterionProved
end
end

/- Original module: KroneckerCanonicalAllowedArithmetic -/
section
/-! The actual admissible dimension domain is now characterized exactly by positivity, primitivity and the Tits inequality. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalAllowedArithmetic
open KroneckerLogic KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
theorem criterion (m : ℕ) (hm : 3≤m) (a b : ℕ) :
 Allowed (family H) m a b ↔ 0<a ∧ 0<b ∧ Nat.Coprime a b ∧ tits m a b≤1 := by
 constructor
 · rintro ⟨ha,hb,hp,hn⟩
   exact ⟨ha,hb,hp,(KroneckerPrimitiveNonemptyCriterionProved.criterion m hm a b ha hp).mp hn⟩
 · rintro ⟨ha,hb,hp,ht⟩
   exact ⟨ha,hb,hp,(KroneckerPrimitiveNonemptyCriterionProved.criterion m hm a b ha hp).mpr ht⟩
end KroneckerCanonicalAllowedArithmetic
end
end

/- Original module: KroneckerCanonicalNonemptyDomainProved -/
section
/-! The exact manuscript companion NonemptyDomain gate is discharged for canonical quotient spaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalNonemptyDomainProved
open KroneckerLogic KroneckerNegativeTitsSymmetry KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
variable (H : ∀ m a b,Admissible (space m a b))
theorem domain : NonemptyDomain (family H) := by
 intro m hm a b ha _ hp
 exact KroneckerPrimitiveNonemptyCriterionProved.criterion m hm a b ha hp
end KroneckerCanonicalNonemptyDomainProved
end
end

/- Original module: KroneckerFilterPartition -/
section
/-! Join limit proofs on a region and its complement. Neither restricted
filter is required to be nontrivial: sequences may switch regions infinitely. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFilterPartition
open Filter
open scoped Topology
variable {α β : Type*} {l : Filter α} {g : Filter β} {f : α → β}

theorem partition (s : Set α) : (l ⊓ 𝓟 s) ⊔ (l ⊓ 𝓟 sᶜ) = l := by
  rw [← inf_sup_left, sup_principal, Set.union_compl_self, principal_univ, inf_top_eq]

theorem tendsto_of_partition (s : Set α)
    (hs : Tendsto f (l ⊓ 𝓟 s) g) (hc : Tendsto f (l ⊓ 𝓟 sᶜ) g) :
    Tendsto f l g := by
  have h := tendsto_sup.mpr ⟨hs, hc⟩
  simpa only [partition] using h


end KroneckerFilterPartition
end
end

/- Original module: KroneckerScopedCentralSorting -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedCentralSorting
open Filter KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerScopedPublishedAdjacent KroneckerScopedWeistCentralLowerLimit
open KroneckerCentralSortedDimensions KroneckerManuscriptTarget KroneckerLogic
open scoped Topology

theorem euler_sort (G : Geometry) (a b : ℕ) :
    (euler (family G) 3 a b : ℝ) = E G (lo a b) (gap a b) := by
  rw [central_euler_eq, gap_add]
  rcases le_total a b with h | h
  · simp only [lo, min_eq_left h, max_eq_right h]
  · simp only [lo, min_eq_right h, max_eq_left h]
    exact_mod_cast KroneckerExchangeEuler.euler_eq 3 a b
      (finiteHomology G 3 a b) (finiteHomology G 3 b a)

theorem entropy_sort (G : Geometry) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (euler (family G) 3 a b : ℝ)/(a : ℝ) =
      (Real.log (E G (lo a b) (gap a b))/(lo a b : ℝ))*((lo a b : ℝ)/a) := by
  rw [euler_sort]
  have hlo : (lo a b : ℝ) ≠ 0 := by exact_mod_cast (lo_pos ha hb).ne'
  field_simp

theorem adjacent_allowed (G : Geometry) (a : ℕ) (ha : 0 < a) :
    Allowed (family G) 3 a (a+1) := by
  have hc : a.Coprime (a+1) := by simp
  refine ⟨ha, by omega, hc, ?_⟩
  apply (KroneckerCanonicalNonemptyDomainProved.domain (finiteHomology G) 3
    (by decide) a (a+1) ha (by omega) hc).mpr
  push_cast
  nlinarith [sq_nonneg (a : ℤ), Nat.cast_nonneg (α := ℤ) a]

def adjacent (G : Geometry) (n : ℕ) : Dimension (family G) 3 :=
  ⟨(n+1,n+2), by simpa [Nat.add_assoc] using adjacent_allowed G (n+1) (by omega)⟩


end KroneckerScopedCentralSorting
end
end

/- Original module: KroneckerScopedDeleteCentralPositive -/
section
/-! Adjacent and nonadjacent offsets are joined without the old upper dictionaries. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedDeleteCentralPositive
open Filter KroneckerScopedModuli KroneckerScopedActualFrameApplication
open KroneckerScopedPublishedAdjacent KroneckerScopedWeistCentralLowerLimit KroneckerFilterPartition
open scoped Topology
variable {α : Type*} {l : Filter α} (a r : α→ℕ)

theorem central_limit (G : Geometry) (A : Application G) (F : Formula G) (W : Weist G)
    (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hr : Tendsto (fun i => (r i:ℝ)/(a i:ℝ)) l (𝓝 0))
    (hp : ∀ᶠ i in l,0<r i ∧ (a i).Coprime (r i)) :
    Tendsto (fun i => Real.log (E G (a i) (r i))/(a i:ℝ)) l (𝓝 (Real.log (256/27:ℝ))) := by
  apply tendsto_of_partition {i | r i=1}
  · apply (three_adjacent_limit G F a (ha.mono_left inf_le_left)).congr'
    apply eventually_inf_principal.mpr
    exact Eventually.of_forall fun i hi => by simp only [Set.mem_ofPred_eq] at hi; simp [hi]
  · apply KroneckerScopedDeleteActualCentral.central_limit a r G A F W
      (ha.mono_left inf_le_left) (hr.mono_left inf_le_left)
    apply eventually_inf_principal.mpr
    exact hp.mono fun i hi hn => by
      simp only [Set.mem_compl_iff,Set.mem_ofPred_eq] at hn
      exact ⟨by omega,hi.2⟩


end KroneckerScopedDeleteCentralPositive
end
end

/- Original module: KroneckerScopedDeleteCentralJoint -/
section
/-! Both sides of slope one, with the new upper-bound dependencies. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedDeleteCentralJoint
open Filter KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerScopedActualFrameApplication KroneckerScopedPublishedAdjacent KroneckerScopedWeistCentralLowerLimit
open KroneckerCentralSortedDimensions KroneckerScopedCentralSorting
open KroneckerManuscriptTarget KroneckerLogic
open scoped Topology
variable {α : Type*} {l : Filter α} (a b : α→ℕ)

theorem central_pair_limit (G : Geometry) (A : Application G) (F : Formula G) (W : Weist G)
    (ha : Tendsto (fun i => (a i:ℝ)) l atTop)
    (hs : Tendsto (fun i => (b i:ℝ)/(a i:ℝ)) l (𝓝 1))
    (hb : ∀ᶠ i in l,0<b i) (hc : ∀ᶠ i in l,(a i).Coprime (b i)) :
    Tendsto (fun i => Real.log (euler (family G) 3 (a i) (b i):ℝ)/(a i:ℝ)) l
      (𝓝 (Real.log (256/27:ℝ))) := by
  have ht := KroneckerScopedDeleteCentralPositive.central_limit
    (fun i => lo (a i) (b i)) (fun i => gap (a i) (b i)) G A F W
    (lo_tendsto a b ha hs) (gap_ratio_tendsto a b ha hs hb) (eventually_primitive a b ha hc)
  have ht' := ht.mul (lo_ratio_tendsto a b ha hs)
  simp only [mul_one] at ht'
  apply ht'.congr'
  filter_upwards [KroneckerLowerEntropyKernel.eventually_positive a ha,hb] with i hai hbi
  exact (entropy_sort G (a i) (b i) hai hbi).symm


theorem central_joint (G : Geometry) (A : Application G) (F : Formula G) (W : Weist G) :
    JointLimit (height (M:=family G) (m:=3)) slope value 1 (Real.log (256/27:ℝ)) := by
  apply jointLimit_of_sequences
  intro p ha hs
  exact central_pair_limit (fun i => (p i).val.1) (fun i => (p i).val.2) G A F W
    (tendsto_natCast_atTop_atTop.comp ha) hs
    (Eventually.of_forall fun i => (p i).property.2.1)
    (Eventually.of_forall fun i => (p i).property.2.2.1)

theorem positive_central (G : Geometry) (A : Application G) (F : Formula G) (W : Weist G) :
    KroneckerPositiveLimitExchange.PositiveLimit (finiteHomology G) 3 1 :=
  ⟨Real.log (256/27:ℝ),Real.log_pos (by norm_num),central_joint G A F W⟩


end KroneckerScopedDeleteCentralJoint
end
end

/- Original module: KroneckerScopedDeleteFundamental -/
section
/-! The all-m fundamental interval now uses the deletion central limit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedDeleteFundamental
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerScopedActualFrameApplication KroneckerScopedPublishedAdjacent KroneckerPositiveLimitExchange

theorem fundamental_three (G : Geometry) (A : Application G) (F : Formula G) (W : Weist G)
    (r : ℝ) (hr : r∈Set.Icc 1 ((3:ℝ)/2)) : PositiveLimit (finiteHomology G) 3 r := by
  by_cases he : r=1
  · subst r
    exact KroneckerScopedDeleteCentralJoint.positive_central G A F W
  · exact KroneckerScopedActualFrameJointTransfer.three_positive G A r
      ⟨lt_of_le_of_ne hr.1 (Ne.symm he),by linarith [hr.2]⟩

theorem fundamental (G : Geometry) (A : Application G) (F : Formula G) (W : Weist G)
    (m : ℕ) (hm : 3≤m) (r : ℝ) (hr : r∈Set.Icc 1 ((m:ℝ)/2)) :
    PositiveLimit (finiteHomology G) m r := by
  rcases (show m=3 ∨ m=4 ∨ 5≤m by omega) with h | h | h
  · subst m; exact fundamental_three G A F W r hr
  · subst m; exact KroneckerScopedOtherFundamental.fundamental_four G A r hr
  · exact KroneckerScopedOtherFundamental.fundamental_large G A m h r hr

end KroneckerScopedDeleteFundamental
end
end
end

section

/- Original module: KroneckerCanonicalEndpointJointLimits -/
section
/-! The finite interior envelope implies both actual-Euler endpoint joint
limits, including sequences alternating between interior and exterior slopes. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalEndpointJointLimits
open Filter KroneckerLogic
open scoped Topology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))

theorem joint_at_root (m : ℕ) (hm : 3≤m) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (h : ∀ p : Dimension (family H) m,slope p ∈ interval m →
      0≤value p ∧ value p≤C*Real.sqrt ((upperRoot m-slope p)*(slope p-lowerRoot m))+D/height p)
    (r : ℝ) (hr : (m : ℝ)*r-1-r^2=0) :
    JointLimit (height (M:=family H) (m:=m)) slope value r 0 := by
  apply jointLimit_of_sequences
  intro p ha hs
  apply endpoint_squeeze (m : ℝ) r C D
    (tendsto_natCast_atTop_atTop.comp ha) hs hr
  exact Filter.Eventually.of_forall (fun n =>
    KroneckerCanonicalInteriorBoundExtension.extend_bound H m hm C D hC hD h (p n))

theorem both_endpoints (m : ℕ) (hm : 3≤m) (C D : ℝ) (hC : 0≤C) (hD : 0≤D)
    (h : ∀ p : Dimension (family H) m,slope p ∈ interval m →
      0≤value p ∧ value p≤C*Real.sqrt ((upperRoot m-slope p)*(slope p-lowerRoot m))+D/height p) :
    JointLimit (height (M:=family H) (m:=m)) slope value (lowerRoot m) 0 ∧
    JointLimit (height (M:=family H) (m:=m)) slope value (upperRoot m) 0 := by
  have hm' : (2 : ℝ)≤m := by exact_mod_cast (show 2≤m by omega)
  exact ⟨joint_at_root H m hm C D hC hD h _ (lowerRoot_quadratic hm'),
    joint_at_root H m hm C D hC hD h _ (upperRoot_quadratic hm')⟩
end KroneckerCanonicalEndpointJointLimits
end
end

/- Original module: KroneckerFundamentalSqrtBound -/
section
/-! The exact square-root coefficient follows from the manuscript's
fundamental sum-of-dimensions identity. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerFundamentalSqrtBound
open KroneckerNegativeTitsSymmetry KroneckerLogic

theorem Q_eq_negative_tits (m a b : ℕ) :
    Q (m:ℝ) a b = -(tits m a b : ℝ) := by
  unfold Q tits
  push_cast
  ring

theorem negative_tits_nonnegative (m a b : ℕ) (ht : tits m a b < 0) :
    0 ≤ -(tits m a b : ℝ) := by exact_mod_cast (show 0 ≤ -tits m a b by omega)

theorem sum_squared_bound (m a b : ℕ) (hm : 3 ≤ m) (hab : a ≤ b) (hb : 2*b ≤ m*a) :
    ((a:ℝ)+(b:ℝ))^2 ≤ ((m:ℝ)+2)/((m:ℝ)-2)*(-(tits m a b:ℝ)) := by
  have hmR : (2:ℝ) < m := by exact_mod_cast (show 2<m by omega)
  have h := fundamental_sum_bound (m:=(m:ℝ)) (u:=(a:ℝ)) (v:=(b:ℝ)) hmR (Nat.cast_nonneg a)
    (by exact_mod_cast hab) (by exact_mod_cast hb)
  rw [Q_eq_negative_tits] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hmR)).mpr
  nlinarith [h]

theorem sum_sqrt_bound (m a b : ℕ) (hm : 3 ≤ m) (hab : a ≤ b) (hb : 2*b ≤ m*a)
    (ht : tits m a b < 0) :
    (a:ℝ)+(b:ℝ) ≤ Real.sqrt (((m:ℝ)+2)/((m:ℝ)-2))*Real.sqrt (-(tits m a b:ℝ)) := by
  have hmR : (2:ℝ) < m := by exact_mod_cast (show 2<m by omega)
  have hC : 0 ≤ ((m:ℝ)+2)/((m:ℝ)-2) := div_nonneg (by linarith) (by linarith)
  have hQ := negative_tits_nonnegative m a b ht
  have hsq := sum_squared_bound m a b hm hab hb
  have hsC := Real.sq_sqrt hC
  have hsQ := Real.sq_sqrt hQ
  have hp := mul_nonneg (Real.sqrt_nonneg (((m:ℝ)+2)/((m:ℝ)-2)))
    (Real.sqrt_nonneg (-(tits m a b:ℝ)))
  have he : (Real.sqrt (((m:ℝ)+2)/((m:ℝ)-2))*Real.sqrt (-(tits m a b:ℝ)))^2 =
      ((m:ℝ)+2)/((m:ℝ)-2)*(-(tits m a b:ℝ)) := by rw [mul_pow,hsC,hsQ]
  nlinarith [Nat.cast_nonneg (α:=ℝ) a,Nat.cast_nonneg (α:=ℝ) b]

theorem linear_log_bound (m a b : ℕ) (hm : 3 ≤ m) (hab : a ≤ b) (hb : 2*b ≤ m*a)
    (ht : tits m a b < 0) :
    (m:ℝ)*((a:ℝ)+b)*Real.log 2 ≤
      KroneckerEnvelopeTitsNormalization.coefficient m*Real.sqrt (-(tits m a b:ℝ)) := by
  have h := mul_le_mul_of_nonneg_left (sum_sqrt_bound m a b hm hab hb ht)
    (mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg (by norm_num : (1:ℝ)≤2)))
  simpa only [KroneckerEnvelopeTitsNormalization.coefficient,mul_assoc,mul_comm,mul_left_comm] using h

end KroneckerFundamentalSqrtBound
end
end

/- Original module: KroneckerLimitEnvelopeWithError -/
section
/-! Additive finite log-errors vanish; the final envelope has no error term. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerLimitEnvelopeWithError
open Filter KroneckerLogic
open KroneckerManuscriptTarget
open scoped Topology
variable (M : ModuliFamily) (m : ℕ)

theorem error_tendsto (D : ℝ) (p : ℕ → Dimension M m)
    (ha : Tendsto (fun n => height (p n)) atTop atTop) :
    Tendsto (fun n => D/(height (p n):ℝ)) atTop (𝓝 0) :=
  KroneckerLowerEntropyKernel.constant_over_height _ (tendsto_natCast_atTop_atTop.comp ha) D

theorem bound_plus_error_tendsto (D r : ℝ) (p : ℕ → Dimension M m)
    (ha : Tendsto (fun n => height (p n)) atTop atTop)
    (hs : Tendsto (fun n => slope (p n)) atTop (𝓝 r)) :
    Tendsto (fun n => bound m (slope (p n))+D/(height (p n):ℝ)) atTop (𝓝 (bound m r)) := by
  have hb := ((KroneckerCanonicalLimitEnvelope.continuous_bound m).tendsto r).comp hs
  have h := hb.add (error_tendsto M m D p ha)
  rw [add_zero] at h
  exact h

theorem limit_bounds (D : ℝ)
    (hb : ∀ p : Dimension M m, 0 ≤ value p ∧ value p ≤ bound m (slope p)+D/(height p:ℝ))
    (r L : ℝ) (hn : Approximable (height (M:=M) (m:=m)) slope r)
    (hl : JointLimit (height (M:=M) (m:=m)) slope value r L) :
    0 ≤ L ∧ L ≤ bound m r := by
  obtain ⟨p⟩ := approaching_nonempty _ _ hn
  have hv := jointLimit_sequence _ _ _ hl p.val p.property.1 p.property.2
  have hb' := bound_plus_error_tendsto M m D r p.val p.property.1 p.property.2
  exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hv (fun n => (hb (p.val n)).1),
    le_of_tendsto_of_tendsto' hv hb' (fun n => (hb (p.val n)).2)⟩

end KroneckerLimitEnvelopeWithError
end
end

/- Original module: KroneckerScopedActualFrameUpper -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedActualFrameUpper
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerFrameIdentity KroneckerScopedActualFrameApplication
open KroneckerScopedActualFrameChoice KroneckerColoring KroneckerStack
open KroneckerNegativeTitsSymmetry

theorem connected_card_upper (p : Parameters) :
    Nat.card {g : Coloring p.m (frameLength p) // Connected p.m (word (frameShape p) g) 0} ≤
      2^(p.m*(p.a+p.b+1)) := by
  classical
  rw [Nat.card_eq_fintype_card, pow_mul, ← KroneckerWeights.coloring_card]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

theorem parameter_euler_upper (G : Geometry) (A : Application G) (p : Parameters) :
    euler (family G) p.m p.a p.b ≤ (2:ℤ)^(p.m*(p.a+p.b+1)) := by
  have hc : (Nat.card {g : Coloring p.m (frameLength p) //
      Connected p.m (word (frameShape p) g) 0} : ℤ) ≤ (2:ℤ)^(p.m*(p.a+p.b+1)) :=
    by exact_mod_cast connected_card_upper p
  rw [finite_coloring_identity G A p] at hc
  apply le_trans ?_ hc
  exact le_mul_of_one_le_left (euler_nonnegative G A p)
    (by exact_mod_cast (show 1 ≤ p.m by have := p.hm; omega))

theorem parameter_log_upper (G : Geometry) (A : Application G) (p : Parameters) :
    Real.log (euler (family G) p.m p.a p.b : ℝ) ≤
      (p.m:ℝ)*((p.a:ℝ)+p.b+1)*Real.log 2 := by
  have he := euler_nonnegative G A p
  by_cases hp : 0 < euler (family G) p.m p.a p.b
  · have hl := Real.log_le_log (by exact_mod_cast hp : (0:ℝ)<euler (family G) p.m p.a p.b)
      (by exact_mod_cast parameter_euler_upper G A p :
        (euler (family G) p.m p.a p.b : ℝ) ≤ (2:ℝ)^(p.m*(p.a+p.b+1)))
    rw [Real.log_pow] at hl
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using hl
  · have hz : euler (family G) p.m p.a p.b = 0 := by omega
    rw [hz,Int.cast_zero,Real.log_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
      (Real.log_nonneg (by norm_num : (1:ℝ)≤2))

theorem input_log_upper (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) (x : Input m) :
    Real.log (euler (family G) m x.a x.b : ℝ) ≤
      (m:ℝ)*((x.a:ℝ)+x.b+1)*Real.log 2 := by
  have h := parameter_log_upper G A (parameters m hm x)
  simpa only [(parameters_spec m hm x).1,(parameters_spec m hm x).2.1,
    (parameters_spec m hm x).2.2] using h

theorem fundamental_log_upper_error (G : Geometry) (A : Application G) (m a b : ℕ)
    (hm : 3 ≤ m) (ha : 2 ≤ a) (hab : a < b) (hc : a.Coprime b)
    (hb : 2*b ≤ m*a) (ht : tits m a b < 0) :
    Real.log (euler (family G) m a b : ℝ) ≤
      KroneckerEnvelopeTitsNormalization.coefficient m*Real.sqrt (-(tits m a b:ℝ))+
        (m:ℝ)*Real.log 2 := by
  have h₁ := input_log_upper G A m hm ⟨a,b,ha,hab,hc⟩
  have h₂ := KroneckerFundamentalSqrtBound.linear_log_bound m a b hm hab.le hb ht
  dsimp only at h₁
  nlinarith

end KroneckerScopedActualFrameUpper
end
end

/- Original module: KroneckerScopedActualUniformError -/
section
/-! Finitely many source-height-one dimensions are absorbed in a constant.
No formula, finite lookup, or upper-bound hypothesis for their Euler numbers
is assumed. The resulting additive constant vanishes in the entropy limit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedActualUniformError
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerScopedActualFrameApplication
open KroneckerScopedActualFrameUpper KroneckerNegativeTitsSymmetry
open scoped BigOperators

def error (G : Geometry) (m : ℕ) : ℝ :=
  (m:ℝ)*Real.log 2 + ∑ b ∈ Finset.range (m+1), |Real.log (euler (family G) m 1 b : ℝ)|

theorem error_nonnegative (G : Geometry) (m : ℕ) : 0 ≤ error G m :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem edge_error_le (G : Geometry) (m : ℕ) : (m:ℝ)*Real.log 2 ≤ error G m :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem unit_log_le_error (G : Geometry) (m b : ℕ) (hb : b ≤ m) :
    Real.log (euler (family G) m 1 b : ℝ) ≤ error G m := by
  have hsum : |Real.log (euler (family G) m 1 b : ℝ)| ≤
      ∑ j ∈ Finset.range (m+1), |Real.log (euler (family G) m 1 j : ℝ)| :=
    Finset.single_le_sum (s := Finset.range (m+1))
      (f := fun j => |Real.log (euler (family G) m 1 j : ℝ)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))
  exact (le_abs_self _).trans (hsum.trans (le_add_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))))

theorem fundamental_log_error (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (hb : 2*b ≤ m*a)
    (hc : a.Coprime b) (ht : tits m a b < 0) :
    Real.log (euler (family G) m a b : ℝ) ≤
      KroneckerEnvelopeTitsNormalization.coefficient m*Real.sqrt (-(tits m a b:ℝ))+error G m := by
  by_cases h₁ : a = 1
  · subst a
    have hu := unit_log_le_error G m b (by omega)
    exact hu.trans (le_add_of_nonneg_left
      (mul_nonneg (KroneckerEnvelopeTitsNormalization.positive m hm).le (Real.sqrt_nonneg _)))
  · have hab' : a < b := by
      by_contra hn
      have he : a = b := by omega
      subst b
      have : a=1 := by simpa using hc
      exact h₁ this
    exact (fundamental_log_upper_error G A m a b hm (by omega) hab' hc hb ht).trans
      (add_le_add le_rfl (edge_error_le G m))

theorem global_log_error (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m)
    (a b : ℕ) (hc : a.Coprime b) (ht : tits m a b < 0) :
    Real.log (euler (family G) m a b : ℝ) ≤
      KroneckerEnvelopeTitsNormalization.coefficient m*Real.sqrt (-(tits m a b:ℝ))+error G m := by
  obtain ⟨c,d,hcpos,hcd,hd,hq,hg,he⟩ :=
    KroneckerFundamentalEulerReduction.reduction (finiteHomology G) m a b ht
  change Real.log (KroneckerOrdinarySingularEuler.ordinaryEuler
    (KroneckerCanonicalKroneckerModuli.space m a b) (finiteHomology G m a b):ℝ) ≤ _
  rw [he,← hq]
  apply fundamental_log_error G A m hm c d hcpos hcd hd
  · change Nat.gcd c d=1
    rw [hg]
    exact hc
  · rw [hq]
    exact ht

end KroneckerScopedActualUniformError
end
end

/- Original module: KroneckerScopedActualFiniteEnvelope -/
section
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedActualFiniteEnvelope
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerScopedActualFrameApplication
open KroneckerScopedActualUniformError KroneckerNegativeTitsSymmetry KroneckerEndpointRoots

theorem interior_upper (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m)
    (p : Dimension (family G) m) (hp : slope p ∈ interior m) :
    value p ≤ bound m (slope p)+error G m/(height p:ℝ) := by
  have hneg := (KroneckerIntegralInteriorCriterion.criterion m hm p.val.1 p.val.2 p.property.1).mp hp
  have h := global_log_error G A m hm p.val.1 p.val.2 p.property.2.2.1 hneg
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg p.val.1)
  rw [add_div] at hd
  dsimp only [KroneckerManuscriptTarget.value, KroneckerManuscriptTarget.slope,
    KroneckerManuscriptTarget.height]
  rw [KroneckerEnvelopeTitsNormalization.identity m p.val.1 p.val.2 hm p.property.1]
  exact hd

theorem outside_zero (G : Geometry) (m : ℕ) (hm : 3 ≤ m)
    (p : Dimension (family G) m) (hp : slope p ∉ interior m) : value p = 0 := by
  apply KroneckerExteriorEntropyZero.value_zero (finiteHomology G) m hm p
  intro hh
  have hn := KroneckerIntegralEndpointExclusion.endpoints m hm p.val.1 p.val.2 p.property.1
  exact hp ⟨lt_of_le_of_ne hh.1 hn.1.symm,lt_of_le_of_ne hh.2 hn.2⟩

theorem bound_nonnegative (m : ℕ) (hm : 3 ≤ m) (r : ℝ) : 0 ≤ bound m r := by
  change 0 ≤ KroneckerEnvelopeTitsNormalization.coefficient m*
    Real.sqrt ((upperRoot m-r)*(r-lowerRoot m))
  exact mul_nonneg (KroneckerEnvelopeTitsNormalization.positive m hm).le (Real.sqrt_nonneg _)

theorem finite_envelope (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m)
    (p : Dimension (family G) m) :
    0 ≤ value p ∧ value p ≤ bound m (slope p)+error G m/(height p:ℝ) := by
  refine ⟨KroneckerCanonicalEntropyNonnegative.nonnegative (finiteHomology G) m p, ?_⟩
  by_cases hp : slope p ∈ interior m
  · exact interior_upper G A m hm p hp
  · rw [outside_zero G m hm p hp]
    exact add_nonneg (bound_nonnegative m hm _) (div_nonneg (error_nonnegative G m) (Nat.cast_nonneg _))

theorem endpoints (G : Geometry) (A : Application G) (m : ℕ) (hm : 3 ≤ m) :
    KroneckerLogic.JointLimit (height (M:=family G) (m:=m)) slope value (lowerRoot m) 0 ∧
    KroneckerLogic.JointLimit (height (M:=family G) (m:=m)) slope value (upperRoot m) 0 := by
  apply KroneckerCanonicalEndpointJointLimits.both_endpoints (finiteHomology G) m hm
    (KroneckerEnvelopeTitsNormalization.coefficient m) (error G m)
    (KroneckerEnvelopeTitsNormalization.positive m hm).le (error_nonnegative G m)
  intro p _
  exact finite_envelope G A m hm p

end KroneckerScopedActualFiniteEnvelope
end
end

/- Original module: KroneckerScopedDeleteMainAssembly -/
section
/-! Assemble the literal manuscript target without an independent finite
upper estimate or a PositiveLimit hypothesis. The unresolved inputs are the
actual geometric realization and the explicitly cited source inputs. The
deletion map supplies the central upper estimate internally. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerScopedDeleteMainAssembly
open KroneckerScopedModuli KroneckerScopedCanonicalPublishedEuler
open KroneckerManuscriptTarget KroneckerScopedActualFrameApplication
open KroneckerScopedPublishedAdjacent
open KroneckerPositiveLimitExchange KroneckerEndpointRoots KroneckerLogic

variable (G : Geometry) (W : Weist G) (F : Formula G) (A : Application G)

def interiorLimits (m : ℕ) (hm : 3 ≤ m) : ∀ r ∈ interior m, PositiveLimit (finiteHomology G) m r :=
  KroneckerCanonicalInteriorLimitsFromFundamental.transfer (finiteHomology G) m hm
    (KroneckerScopedDeleteFundamental.fundamental G A F W m hm)

def profile (m : ℕ) (hm : 3 ≤ m) : ℝ → ℝ :=
  KroneckerCanonicalEntropyProfileChoice.profile (finiteHomology G) m (interiorLimits G W F A m hm)

theorem lower (m : ℕ) (hm : 3 ≤ m) : profile G W F A m hm (lowerRoot m) = 0 :=
  KroneckerCanonicalEntropyProfileChoice.lower _ _ _

theorem upper (m : ℕ) (hm : 3 ≤ m) : profile G W F A m hm (upperRoot m) = 0 :=
  KroneckerCanonicalEntropyProfileChoice.upper _ _ _

theorem positive (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interior m) :
    0 < profile G W F A m hm r :=
  KroneckerCanonicalEntropyProfileChoice.positive _ _ _ r hr

theorem joint (m : ℕ) (hm : 3 ≤ m) (r : ℝ) (hr : r ∈ interval m) :
    JointLimit (height (M:=family G) (m:=m)) slope value r (profile G W F A m hm r) := by
  by_cases hl : r=lowerRoot m
  · subst r
    rw [lower]
    exact (KroneckerScopedActualFiniteEnvelope.endpoints G A m hm).1
  by_cases hu : r=upperRoot m
  · subst r
    rw [upper]
    exact (KroneckerScopedActualFiniteEnvelope.endpoints G A m hm).2
  exact KroneckerCanonicalEntropyProfileChoice.joint _ _ _ r
    ⟨lt_of_le_of_ne hr.1 (Ne.symm hl),lt_of_le_of_ne hr.2 hu⟩

end KroneckerScopedDeleteMainAssembly
end
end
end

