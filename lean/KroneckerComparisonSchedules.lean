import KroneckerTruncatedDensity
import KroneckerPeriodicRounding

section

set_option autoImplicit false
namespace KroneckerComparisonScales

def collarScale (m : ℕ) : ℝ := (m : ℝ)+4
def inflationScale (m : ℕ) : ℝ := 2*collarScale m+2

theorem upper_scale_slack (m : ℕ) (η : ℝ) (hη : 0 < η) :
    0 < collarScale m*η ∧ 0 < 1+inflationScale m*η ∧
    2*(collarScale m*η) ≤ 1+inflationScale m*η ∧
    (1+η)*1 < 1+2*η ∧
    (1+2*η)-1+(m+1 : ℕ)*η*1 < collarScale m*η := by
  dsimp [collarScale,inflationScale]
  push_cast
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem lower_scale_slack (m : ℕ) (η : ℝ) (hη : 0 < η)
    (hsmall : inflationScale m*η < 1) :
    0 < 1-inflationScale m*η ∧ 2*(collarScale m*η) ≤ 1 ∧
    (1+η)*(1-inflationScale m*η) < 1-2*(collarScale m*η) ∧
    (1-2*(collarScale m*η))-(1-inflationScale m*η)+
      (m+1 : ℕ)*η*(1-inflationScale m*η) < collarScale m*η := by
  have hC : 0 < collarScale m := by dsimp [collarScale]; positivity
  have hH : 0 < inflationScale m := by dsimp [inflationScale]; positivity
  have hηH : 0 < inflationScale m*η := mul_pos hH hη
  have hprod : 0 < η*(inflationScale m*η) := mul_pos hη hηH
  have hweight : 0 ≤ ((m+1 : ℕ) : ℝ)*η*(inflationScale m*η) := by positivity
  dsimp [inflationScale] at *
  have hcast : ((m+1 : ℕ) : ℝ)=collarScale m-3 := by simp [collarScale]; ring
  rw [hcast]
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · rw [hcast] at hweight
    nlinarith

end KroneckerComparisonScales
end

section

/- Original module: KroneckerDifferenceDensity -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerDifferenceDensity

theorem difference_density (a b c : ℕ → ℕ) (B C : ℝ) (hBC : C ≤ B)
    (hb : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 B))
    (hc : Tendsto (fun n => (c n : ℝ)/(a n : ℝ)) atTop (𝓝 C)) :
    Tendsto (fun n => ((b n-c n : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (B-C)) := by
  have h := (hb.sub hc).max
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  simpa only [max_eq_left (sub_nonneg.mpr hBC),
    ← KroneckerTruncatedDensity.normalized_sub_eq_max] using h

end KroneckerDifferenceDensity
end

/- Original module: KroneckerProportionalMiddle -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerProportionalMiddle

theorem proportional_middle_density (a b P : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (B C : ℝ) (hBC : 2*C ≤ B)
    (hb : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 B))
    (hP : Tendsto (fun n => (P n : ℝ)/(a n : ℝ)) atTop (𝓝 C)) :
    Tendsto (fun n => ((b n-2*P n-2 : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (B-2*C)) := by
  have hz : Tendsto (fun n => (2 : ℝ)/(a n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  have hcost : Tendsto (fun n => ((2*P n+2 : ℕ) : ℝ)/(a n : ℝ)) atTop (𝓝 (2*C)) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,add_div,mul_div_assoc,add_zero]
      using (hP.const_mul 2).add hz
  simpa only [Nat.sub_sub] using
    KroneckerDifferenceDensity.difference_density a b (fun n => 2*P n+2) B (2*C) hBC hb hcost

end KroneckerProportionalMiddle
end

/- Original module: KroneckerComparisonSchedules -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerComparisonSchedules
open KroneckerPeriodicRounding KroneckerComparisonScales KroneckerProportionalMiddle

noncomputable def collar (m : ℕ) (η : ℝ) (n : ℕ) : ℕ := ⌊(collarScale m*η)*(n : ℝ)⌋₊
noncomputable def upperLength (m q : ℕ) (η : ℝ) (n : ℕ) : ℕ :=
  upperPeriods q (1+inflationScale m*η) n*q
noncomputable def upperMiddle (m q : ℕ) (η : ℝ) (n : ℕ) : ℕ :=
  upperLength m q η n-2*collar m η n-2
noncomputable def lowerLength (m q : ℕ) (η : ℝ) (n : ℕ) : ℕ :=
  lowerPeriods q (1-inflationScale m*η) n*q
noncomputable def lowerMiddle (m : ℕ) (η : ℝ) (n : ℕ) : ℕ := n-2*collar m η n-2

theorem self_density (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => (a n : ℝ)/(a n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr'
  filter_upwards [ha.eventually (eventually_ge_atTop 1)] with n hn
  have hnR : (a n : ℝ) ≠ 0 := by exact_mod_cast (show a n ≠ 0 by omega)
  simp [hnR]

theorem collar_density (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (m : ℕ) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n => (collar m η (a n) : ℝ)/(a n : ℝ)) atTop (𝓝 (collarScale m*η)) :=
  KroneckerRoundedScaling.floor_scaling a ha _ (upper_scale_slack m η hη).1.le

theorem upper_middle_density (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (m q : ℕ) (hq : 0 < q) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n => (upperMiddle m q η (a n) : ℝ)/(a n : ℝ)) atTop (𝓝 (1+2*η)) := by
  have h := upper_scale_slack m η hη
  have hh := proportional_middle_density a (fun n => upperLength m q η (a n))
    (fun n => collar m η (a n)) ha _ _ h.2.2.1
    (upper_period_length_density a ha q hq _ h.2.1.le) (collar_density a ha m η hη)
  have he : 1+inflationScale m*η-2*(collarScale m*η)=1+2*η := by
    dsimp [inflationScale]
    ring
  simpa only [upperMiddle,he] using hh

theorem lower_middle_density (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (m : ℕ) (η : ℝ) (hη : 0 < η) (hsmall : inflationScale m*η < 1) :
    Tendsto (fun n => (lowerMiddle m η (a n) : ℝ)/(a n : ℝ)) atTop
      (𝓝 (1-2*(collarScale m*η))) :=
  proportional_middle_density a a (fun n => collar m η (a n)) ha _ _
    (lower_scale_slack m η hη hsmall).2.1 (self_density a ha) (collar_density a ha m η hη)

end KroneckerComparisonSchedules
end
end

