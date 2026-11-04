import KroneckerInteriorAllowedReflection
import KroneckerCanonicalReflectionEuler
import KroneckerPositiveLimitExchange
import KroneckerRealReflectionIterates

/- Original module: KroneckerRootPairEntropy -/
section
/-! Every actual positive root-sequence moduli space has Euler one, so its
manuscript observable is exactly zero before passage to any limit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootPairEntropy
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerRootPairRecurrence KroneckerRootPairAllowed
variable (H : ∀ m a b,Admissible (space m a b))

theorem euler_one (m : ℕ) (hm : 3≤m) (n : ℕ) :
    ordinaryEuler (space m (pair m (n+1)).1 (pair m (n+1)).2) (H _ _ _)=1 :=
  KroneckerCanonicalTitsOneEuler.euler_one _ _ _
    (KroneckerCanonicalRootNonemptiness.pair_nonempty m hm (n+1))
    (KroneckerRootPairHeightGrowth.tits_one m hm (n+1)) _

theorem value_zero (m : ℕ) (hm : 3≤m) (n : ℕ) : value (dimension H m hm n)=0 := by
  change Real.log (ordinaryEuler (space m (pair m (n+1)).1 (pair m (n+1)).2) (H _ _ _) : ℝ)/_=0
  rw [euler_one H m hm n]
  simp
end KroneckerRootPairEntropy
end
end

/- Original module: KroneckerEndpointLimitForced -/
section
/-! Any joint limit at an endpoint on the actual manuscript domain is forced
to be zero by the constructed root sequence; no endpoint estimate is assumed. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerEndpointLimitForced
open Filter KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
open KroneckerManuscriptTarget KroneckerEndpointRoots
open scoped Topology
variable (H : ∀ m a b,Admissible (space m a b))

theorem upper (m : ℕ) (hm : 3≤m) (L : ℝ)
    (h : JointLimit (height (M:=family H) (m:=m)) slope value (upperRoot m) L) : L=0 := by
  have ht := jointLimit_sequence _ _ _ h (KroneckerRootPairAllowed.dimension H m hm)
    (KroneckerRootPairSlopeConvergence.height m hm) (KroneckerRootPairSlopeConvergence.slope m hm)
  have hz : Tendsto (fun n => value (KroneckerRootPairAllowed.dimension H m hm n)) atTop (𝓝 0) := by
    simpa only [KroneckerRootPairEntropy.value_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hz

theorem lower (m : ℕ) (hm : 3≤m) (L : ℝ)
    (h : JointLimit (height (M:=family H) (m:=m)) slope value (lowerRoot m) L) : L=0 := by
  have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
  have hx := KroneckerExchangeJointLimit.joint_exchange H (lowerRoot_positive hm') h
  have hroot : (lowerRoot (m : ℝ))⁻¹=upperRoot m := by
    simpa [KroneckerSlopeSymmetry.exchange] using KroneckerSlopeSymmetry.exchange_lowerRoot hm'
  rw [hroot] at hx
  have hz := upper H m hm _ hx
  exact (div_eq_zero_iff.mp hz).resolve_right (ne_of_gt (lowerRoot_positive hm'))
end KroneckerEndpointLimitForced
end
end

/- Original module: KroneckerInteriorApproximableRestriction -/
section
/-! At a strictly interior slope, actual-domain nonvacuity is equivalent to
nonvacuity using only dimensions with strictly interior slopes. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorApproximableRestriction
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerLogic KroneckerInteriorAllowedReflection KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))


theorem restrict (m : ℕ) (r : ℝ) (hr : r∈interior m)
    (h : Approximable (height (M:=family H) (m:=m)) slope r) :
    Approximable (fun p : Interior H m => height p.val) (fun p => slope p.val) r := by
  intro δ hδ N
  let ε := min δ (min (r-lowerRoot m) (upperRoot m-r))
  have hε : 0<ε := lt_min hδ (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2))
  obtain ⟨p,hp,hs⟩ := h ε hε N
  have hδ' : dist (slope p) r<δ := lt_of_lt_of_le hs (min_le_left _ _)
  have hl : dist (slope p) r<r-lowerRoot m := lt_of_lt_of_le hs
    ((min_le_right _ _).trans (min_le_left _ _))
  have hu : dist (slope p) r<upperRoot m-r := lt_of_lt_of_le hs
    ((min_le_right _ _).trans (min_le_right _ _))
  have hi : slope p∈interior m := by
    rw [Real.dist_eq,abs_lt] at hl hu
    exact ⟨by linarith [hl.1],by linarith [hu.2]⟩
  exact ⟨⟨p,hi⟩,hp,hδ'⟩
end KroneckerInteriorApproximableRestriction
end
end

/- Original module: KroneckerCanonicalEndpointReductionExact -/
section
/-! Exact endpoint reduction: a full-domain endpoint joint limit exists with
value L precisely when L=0 and the strictly interior domain has joint limit zero. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalEndpointReductionExact
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerLogic KroneckerInteriorAllowedReflection KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))

theorem restrict (m : ℕ) (r L : ℝ)
    (h : JointLimit (height (M:=family H) (m:=m)) slope value r L) :
    JointLimit (fun p : Interior H m => height p.val) (fun p => slope p.val) (fun p => value p.val) r L := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := h ε hε
  exact ⟨δ,hδ,N,fun p hp hs => hN p.val hp hs⟩

theorem extend_zero (m : ℕ) (hm : 3≤m) (r : ℝ)
    (h : JointLimit (fun p : Interior H m => height p.val) (fun p => slope p.val) (fun p => value p.val) r 0) :
    JointLimit (height (M:=family H) (m:=m)) slope value r 0 := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := h ε hε
  refine ⟨δ,hδ,N,?_⟩
  intro p hp hs
  by_cases hi : slope p∈interior m
  · exact hN ⟨p,hi⟩ hp hs
  · have he : slope p∉interval m := by
      intro hh
      have hn := KroneckerIntegralEndpointExclusion.endpoints m hm p.val.1 p.val.2 p.property.1
      exact hi ⟨lt_of_le_of_ne hh.1 hn.1.symm,lt_of_le_of_ne hh.2 hn.2⟩
    rw [KroneckerExteriorEntropyZero.value_zero H m hm p he]
    simpa using hε

theorem criterion (m : ℕ) (hm : 3≤m) (r L : ℝ) (hr : r=lowerRoot m ∨ r=upperRoot m) :
    JointLimit (height (M:=family H) (m:=m)) slope value r L ↔
      L=0 ∧ JointLimit (fun p : Interior H m => height p.val) (fun p => slope p.val) (fun p => value p.val) r 0 := by
  constructor
  · intro h
    have hL : L=0 := by
      rcases hr with rfl | rfl
      · exact KroneckerEndpointLimitForced.lower H m hm L h
      · exact KroneckerEndpointLimitForced.upper H m hm L h
    exact ⟨hL,by rw [←hL];exact restrict H m r L h⟩
  · rintro ⟨rfl,h⟩
    exact extend_zero H m hm r h
end KroneckerCanonicalEndpointReductionExact
end
end

/- Original module: KroneckerCanonicalReflectionSlopeGeometry -/
section
/-! The geometric reflection slope is the exchange-reflection composite;
it preserves the open root interval and has the explicit inverse m-1/r. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionSlopeGeometry
open KroneckerEndpointRoots KroneckerManuscriptTarget
theorem interior (m : ℕ) (hm : 3≤m) (r : ℝ) (hr : r∈KroneckerManuscriptTarget.interior m) :
    ((m : ℝ)-r)⁻¹∈KroneckerManuscriptTarget.interior m := by
  have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
  simpa [KroneckerManuscriptTarget.interior,KroneckerSlopeSymmetry.exchange,KroneckerSlopeSymmetry.reflect] using
    KroneckerSlopeSymmetry.exchange_mem_interior hm' (KroneckerSlopeSymmetry.reflect_mem_interior hm' hr)
theorem inverse (m : ℕ) (r : ℝ) : (m : ℝ)-(((m : ℝ)-r)⁻¹)⁻¹=r := by simp
theorem gap (m : ℕ) (hm : 3≤m) (r : ℝ) (hd : (m : ℝ)-r≠0) :
    (upperRoot m-((m : ℝ)-r)⁻¹)*(((m : ℝ)-r)⁻¹-lowerRoot m)=
      ((upperRoot m-r)*(r-lowerRoot m))/((m : ℝ)-r)^2 := by
  have hm' : (2 : ℝ)≤m := by exact_mod_cast (show 2≤m by omega)
  rw [KroneckerSlopeSymmetry.root_gap_product hm',KroneckerSlopeSymmetry.root_gap_product hm']
  have he := KroneckerSlopeSymmetry.slopeQuadratic_exchange (m := (m : ℝ)) hd
  simpa [KroneckerSlopeSymmetry.exchange,KroneckerSlopeSymmetry.reflect,
    KroneckerSlopeSymmetry.slopeQuadratic] using he.trans
    (congrArg (fun x : ℝ => x / ((m : ℝ)-r)^2)
      (KroneckerSlopeSymmetry.slopeQuadratic_reflect (m : ℝ) r))
end KroneckerCanonicalReflectionSlopeGeometry
end
end

/- Original module: KroneckerInteriorJointRestriction -/
section
/-! At a strict interior slope, joint limits on the full actual dimension
domain are equivalent to joint limits restricted to interior dimensions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorJointRestriction
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
open KroneckerManuscriptTarget KroneckerInteriorAllowedReflection KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))
theorem extend (m : ℕ) (r L : ℝ) (hr : r∈interior m)
    (h : JointLimit (fun p : Interior H m => height p.val) (fun p => slope p.val)
      (fun p => value p.val) r L) : JointLimit (height (M:=family H) (m:=m)) slope value r L := by
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := h ε hε
  refine ⟨min δ (min (r-lowerRoot m) (upperRoot m-r)),
    lt_min hδ (lt_min (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)),N,?_⟩
  intro p hp hs
  have hδ' := lt_of_lt_of_le hs (min_le_left _ _)
  have hl := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
  have hu := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _))
  have hi : slope p∈interior m := by
    rw [Real.dist_eq,abs_lt] at hl hu
    exact ⟨by linarith [hl.1],by linarith [hu.2]⟩
  exact hN ⟨p,hi⟩ hp hδ'
theorem iff (m : ℕ) (r L : ℝ) (hr : r∈interior m) :
    JointLimit (height (M:=family H) (m:=m)) slope value r L ↔
      JointLimit (fun p : Interior H m => height p.val) (fun p => slope p.val) (fun p => value p.val) r L :=
  ⟨KroneckerCanonicalEndpointReductionExact.restrict H m r L,extend H m r L hr⟩
end KroneckerInteriorJointRestriction
end
end

/- Original module: KroneckerInteriorReflectionEquivalence -/
section
/-! The actual interior dimension domain is permuted by global reflection;
the inverse is exchange-reflection-exchange, with natural subtraction checked. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorReflectionEquivalence
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
open KroneckerInteriorAllowedReflection
variable (H : ∀ m a b,Admissible (space m a b))

def inverse (m : ℕ) (hm : 3≤m) (p : Interior H m) : Interior H m :=
  exchange H m hm (reflect H m hm (exchange H m hm p))

theorem left_inverse (m : ℕ) (hm : 3≤m) :
    Function.LeftInverse (inverse H m hm) (reflect H m hm) := by
  intro p
  have hb := (KroneckerCanonicalDimensionBounds.dimension_bounds m _ _
    p.val.property.1 p.val.property.2.1 p.val.property.2.2.2).1
  apply Subtype.ext
  apply Subtype.ext
  change (p.val.val.1,m*p.val.val.1-(m*p.val.val.1-p.val.val.2))=p.val.val
  rw [Nat.sub_sub_self hb]

theorem right_inverse (m : ℕ) (hm : 3≤m) :
    Function.RightInverse (inverse H m hm) (reflect H m hm) := by
  intro p
  have ha := (KroneckerCanonicalDimensionBounds.dimension_bounds m _ _
    p.val.property.1 p.val.property.2.1 p.val.property.2.2.2).2
  apply Subtype.ext
  apply Subtype.ext
  change (m*p.val.val.2-(m*p.val.val.2-p.val.val.1),p.val.val.2)=p.val.val
  rw [Nat.sub_sub_self ha]

def equiv (m : ℕ) (hm : 3≤m) : Interior H m ≃ Interior H m :=
  ⟨reflect H m hm,inverse H m hm,left_inverse H m hm,right_inverse H m hm⟩
end KroneckerInteriorReflectionEquivalence
end
end

/- Original module: KroneckerInteriorReflectionObservables -/
section
/-! Exact height and slope laws for actual global reflection. These laws
make no assumption about Euler invariance of the reflected moduli spaces. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorReflectionObservables
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerEndpointRoots KroneckerInteriorAllowedReflection
variable (H : ∀ m a b,Admissible (space m a b))

theorem denominator_positive (m : ℕ) (hm : 3≤m) (r : ℝ) (hr : r∈interior m) : 0<(m : ℝ)-r := by
  have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
  have hp := lowerRoot_positive hm'
  have he := root_sum (m : ℝ)
  have hru := hr.2
  linarith


end KroneckerInteriorReflectionObservables
end
end

/- Original module: KroneckerInteriorReflectionEuler -/
section
/-! On actual allowed interior dimensions, reflection preserves the integer
Euler observable exactly. The family finiteness premise remains explicit. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorReflectionEuler
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerInteriorAllowedReflection
variable (H : ∀ m a b,Admissible (space m a b))
theorem euler (m : ℕ) (hm : 3≤m) (p : Interior H m) :
    KroneckerManuscriptTarget.euler (family H) m (reflect H m hm p).val.val.1 (reflect H m hm p).val.val.2 =
      KroneckerManuscriptTarget.euler (family H) m p.val.val.1 p.val.val.2 := by
  exact (KroneckerCanonicalReflectionEuler.euler_eq m _ _ p.val.property.1
    (KroneckerCanonicalDimensionBounds.dimension_bounds m _ _ p.val.property.1
      p.val.property.2.1 p.val.property.2.2.2).1 _ _).symm
end KroneckerInteriorReflectionEuler
end
end

/- Original module: KroneckerInteriorReflectionEntropy -/
section
/-! Reflection rescales the actual normalized logarithmic Euler observable
by the exact source-height factor m-r, with no positivity assumption on log. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorReflectionEntropy
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerInteriorAllowedReflection KroneckerInteriorReflectionObservables
variable (H : ∀ m a b,Admissible (space m a b))
end KroneckerInteriorReflectionEntropy
end
end

/- Original module: KroneckerInteriorInverseObservables -/
section
/-! The inverse interior reflection has exact slope, height and normalized
Euler laws; these are needed when transporting arbitrary approaching sequences. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorInverseObservables
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerInteriorAllowedReflection KroneckerInteriorReflectionEquivalence
variable (H : ∀ m a b,Admissible (space m a b))
theorem height_inverse (m : ℕ) (hm : 3≤m) (p : Interior H m) :
    (height (inverse H m hm p).val : ℝ)=slope p.val * height p.val := by
  have ha : (p.val.val.1 : ℝ)≠0 := by exact_mod_cast (ne_of_gt p.val.property.1)
  change (p.val.val.2 : ℝ)=(p.val.val.2/p.val.val.1)*p.val.val.1
  exact (div_mul_cancel₀ _ ha).symm
theorem slope_inverse (m : ℕ) (hm : 3≤m) (p : Interior H m) :
    slope (inverse H m hm p).val=(m : ℝ)-(slope p.val)⁻¹ := by
  have hb : (p.val.val.2 : ℝ)≠0 := by exact_mod_cast (ne_of_gt p.val.property.2.1)
  have hd := (KroneckerCanonicalDimensionBounds.dimension_bounds m _ _ p.val.property.1
    p.val.property.2.1 p.val.property.2.2.2).2
  change ((m*p.val.val.2-p.val.val.1 : ℕ) : ℝ)/p.val.val.2 =
    (m : ℝ)-((p.val.val.2 : ℝ)/p.val.val.1)⁻¹
  rw [Nat.cast_sub hd,Nat.cast_mul,inv_div]
  field_simp <;> ring
theorem euler_inverse (m : ℕ) (hm : 3≤m) (p : Interior H m) :
    euler (family H) m (inverse H m hm p).val.val.1 (inverse H m hm p).val.val.2 =
      euler (family H) m p.val.val.1 p.val.val.2 := by
  have h := KroneckerInteriorReflectionEuler.euler H m hm (inverse H m hm p)
  rw [right_inverse H m hm p] at h
  exact h.symm
theorem value_inverse (m : ℕ) (hm : 3≤m) (p : Interior H m) :
    value (inverse H m hm p).val=value p.val/slope p.val := by
  unfold value
  rw [euler_inverse]
  change Real.log _ / (height (inverse H m hm p).val : ℝ)=_
  rw [height_inverse]
  simp only [div_div,mul_comm,height]
end KroneckerInteriorInverseObservables
end
end

/- Original module: KroneckerInteriorInverseHeightGrowth -/
section
/-! Inverse-reflected heights diverge for every sequence approaching a
positive interior slope, using the exact b/a source-height scale. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorInverseHeightGrowth
open Filter
open scoped Topology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerInteriorAllowedReflection KroneckerInteriorReflectionEquivalence
variable (H : ∀ m a b,Admissible (space m a b))
theorem tendsto (m : ℕ) (hm : 3≤m) (p : ℕ → Interior H m) (r : ℝ) (hr : 0<r)
    (ha : Tendsto (fun n => height (p n).val) atTop atTop)
    (hs : Tendsto (fun n => slope (p n).val) atTop (𝓝 r)) :
    Tendsto (fun n => height (inverse H m hm (p n)).val) atTop atTop :=
  KroneckerExchangeHeightGrowth.height_tendsto H (fun n => (p n).val) hr ha hs
end KroneckerInteriorInverseHeightGrowth
end
end

/- Original module: KroneckerInteriorReflectionJointLimit -/
section
/-! Joint limits of actual Euler entropy on the interior domain transform
under reflection with the exact factor 1/(m-r), for every admissible sequence. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerInteriorReflectionJointLimit
open Filter KroneckerLogic
open scoped Topology
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerInteriorAllowedReflection KroneckerInteriorReflectionEquivalence
open KroneckerInteriorInverseObservables
variable (H : ∀ m a b,Admissible (space m a b))
theorem reflect (m : ℕ) (hm : 3≤m) (r L : ℝ) (hr : r∈interior m)
    (h : JointLimit (fun p : Interior H m => height p.val) (fun p => slope p.val)
      (fun p => value p.val) r L) :
    JointLimit (fun p : Interior H m => height p.val) (fun p => slope p.val)
      (fun p => value p.val) ((m : ℝ)-r)⁻¹ (L/((m : ℝ)-r)) := by
  apply jointLimit_of_sequences
  intro p ha hs
  have hd := KroneckerInteriorReflectionObservables.denominator_positive m hm r hr
  have hp : 0<((m : ℝ)-r)⁻¹ := inv_pos.mpr hd
  have hh := KroneckerInteriorInverseHeightGrowth.tendsto H m hm p _ hp ha hs
  have hsl : Tendsto (fun n => slope (inverse H m hm (p n)).val) atTop (𝓝 r) := by
    simp only [slope_inverse]
    have hi := (tendsto_const_nhds (x := (m : ℝ))).sub (hs.inv₀ (ne_of_gt hp))
    simpa only [inv_inv,sub_sub_cancel] using hi
  have hv := jointLimit_sequence _ _ _ h (fun n => inverse H m hm (p n)) hh hsl
  have he : ∀ n,value (inverse H m hm (p n)).val * slope (p n).val=value (p n).val := by
    intro n
    rw [value_inverse]
    exact div_mul_cancel₀ _ (ne_of_gt (KroneckerExchangeObservables.slope_positive H _))
  have hh' := hv.mul hs
  simp_rw [he] at hh'
  simpa only [div_eq_mul_inv] using hh'
end KroneckerInteriorReflectionJointLimit
end
end

/- Original module: KroneckerCanonicalReflectionJointLimit -/
section
/-! Actual full-domain joint entropy limits transport under geometric
reflection at strict interior slopes, including every admissible approaching sequence. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalReflectionJointLimit
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler
open KroneckerManuscriptTarget KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))
theorem reflect (m : ℕ) (hm : 3≤m) (r L : ℝ) (hr : r∈interior m)
    (h : JointLimit (height (M:=family H) (m:=m)) slope value r L) :
    JointLimit (height (M:=family H) (m:=m)) slope value ((m : ℝ)-r)⁻¹ (L/((m : ℝ)-r)) := by
  apply KroneckerInteriorJointRestriction.extend H m _ _
  · exact KroneckerCanonicalReflectionSlopeGeometry.interior m hm r hr
  · exact KroneckerInteriorReflectionJointLimit.reflect H m hm r L hr
      (KroneckerCanonicalEndpointReductionExact.restrict H m r L h)
end KroneckerCanonicalReflectionJointLimit
end
end

/- Original module: KroneckerCanonicalInverseJointLimit -/
section
/-! The inverse geometric reflection transports full-domain joint limits
with slope m-1/r and source-height factor r, closing the bidirectional limit law. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerCanonicalInverseJointLimit
open KroneckerLogic KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerEndpointRoots
variable (H : ∀ m a b,Admissible (space m a b))
theorem inverse (m : ℕ) (hm : 3≤m) (r L : ℝ) (hr : r∈interior m)
    (h : JointLimit (height (M:=family H) (m:=m)) slope value r L) :
    JointLimit (height (M:=family H) (m:=m)) slope value ((m : ℝ)-r⁻¹) (L/r) := by
  have hm' : (2 : ℝ)<m := by exact_mod_cast (show 2<m by omega)
  have hp : 0<r := (lowerRoot_positive hm').trans hr.1
  have hi : r⁻¹∈interior m := by
    simpa [KroneckerManuscriptTarget.interior,KroneckerSlopeSymmetry.exchange] using
      KroneckerSlopeSymmetry.exchange_mem_interior hm' hr
  have hd := KroneckerInteriorReflectionObservables.denominator_positive m hm _ hi
  have h1 := KroneckerExchangeJointLimit.joint_exchange H hp h
  have h2 := KroneckerCanonicalReflectionJointLimit.reflect H m hm _ _ hi h1
  have h3 := KroneckerExchangeJointLimit.joint_exchange H (inv_pos.mpr hd) h2
  simpa only [inv_inv,div_inv_eq_mul,div_mul_cancel₀ _ (ne_of_gt hd)] using h3
end KroneckerCanonicalInverseJointLimit
end
end

/- Original module: KroneckerPositiveLimitReflection -/
section
/-! Positive joint-limit existence is equivalent at every real interior
slope and its geometric reflection, using both proved limit-transport directions. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerPositiveLimitReflection
open KroneckerCanonicalKroneckerModuli KroneckerOrdinarySingularEuler KroneckerManuscriptTarget
open KroneckerPositiveLimitExchange
variable (H : ∀ m a b,Admissible (space m a b))
theorem iff (m : ℕ) (hm : 3≤m) (r : ℝ) (hr : r∈interior m) :
    PositiveLimit H m r ↔ PositiveLimit H m (KroneckerRealReflectionDynamics.step (m : ℝ) r) := by
  have hd := KroneckerInteriorReflectionObservables.denominator_positive m hm r hr
  constructor
  · rintro ⟨L,hL,hl⟩
    exact ⟨L/((m : ℝ)-r),div_pos hL hd,KroneckerCanonicalReflectionJointLimit.reflect H m hm r L hr hl⟩
  · rintro ⟨L,hL,hl⟩
    have hi := KroneckerCanonicalReflectionSlopeGeometry.interior m hm r hr
    have hh := KroneckerCanonicalInverseJointLimit.inverse H m hm ((m : ℝ)-r)⁻¹ L hi hl
    refine ⟨L/((m : ℝ)-r)⁻¹,div_pos hL (inv_pos.mpr hd),?_⟩
    simpa only [inv_inv,sub_sub_cancel] using hh
end KroneckerPositiveLimitReflection
end
end
