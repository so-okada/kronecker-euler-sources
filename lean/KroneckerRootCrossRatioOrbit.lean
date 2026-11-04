import KroneckerRealReflectionIterates

/- Original module: KroneckerRootCrossRatio -/
section
/-! A positive root cross ratio coordinatizes the open interval and solves
explicitly for the slope; its denominator cannot vanish in the interval. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootCrossRatio
open KroneckerEndpointRoots
def ratio (m r : ℝ) : ℝ := (r-lowerRoot m)/(upperRoot m-r)
theorem positive {m r : ℝ} (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) : 0<ratio m r :=
  div_pos (sub_pos.mpr hr.1) (sub_pos.mpr hr.2)
theorem solve {m r : ℝ} (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    r=(lowerRoot m+upperRoot m*ratio m r)/(1+ratio m r) := by
  have hd : upperRoot m-r≠0 := ne_of_gt (sub_pos.mpr hr.2)
  have hc : 1+ratio m r≠0 := ne_of_gt (by linarith [positive hr])
  apply (eq_div_iff hc).mpr
  unfold ratio
  field_simp <;> ring
end KroneckerRootCrossRatio
end
end

/- Original module: KroneckerRootCrossRatioReflection -/
section
/-! One reflection multiplies the root cross ratio by lowerRoot/upperRoot,
turning the nonlinear slope recurrence into a geometric contraction. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootCrossRatioReflection
open KroneckerEndpointRoots KroneckerRealReflectionDynamics KroneckerRootCrossRatio
theorem transform {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) :
    ratio m (step m r)=(lowerRoot m/upperRoot m)*ratio m r := by
  have hd : m-r≠0 := ne_of_gt (denominator hm hr)
  have hu : upperRoot m≠0 := ne_of_gt (upperRoot_positive hm)
  have hs := root_sum m
  have hp := root_product hm.le
  have hr' : upperRoot m-r≠0 := ne_of_gt (sub_pos.mpr hr.2)
  have ht : upperRoot m-step m r≠0 := ne_of_gt (sub_pos.mpr (interior hm hr).2)
  unfold ratio
  apply (div_eq_iff ht).mpr
  unfold step
  field_simp
  have h1 : 1-(m-r)*lowerRoot m=lowerRoot m*(r-lowerRoot m) := by nlinarith [lowerRoot_quadratic hm.le]
  have h2 : (m-r)*upperRoot m-1=upperRoot m*(upperRoot m-r) := by nlinarith [upperRoot_quadratic hm.le]
  rw [h1,h2]
  ring
end KroneckerRootCrossRatioReflection
end
end

/- Original module: KroneckerRootCrossRatioOrbit -/
section
/-! The exact cross ratio along every reflection orbit is a geometric
power times its initial value, giving a closed form without assuming convergence. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerRootCrossRatioOrbit
open KroneckerEndpointRoots KroneckerRootCrossRatio KroneckerRealReflectionIterates
theorem formula {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) (n : ℕ) :
    ratio m (orbit m r n)=(lowerRoot m/upperRoot m)^n * ratio m r := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    change ratio m (KroneckerRealReflectionDynamics.step m (orbit m r n))=_
    rw [KroneckerRootCrossRatioReflection.transform hm (interior hm hr n),ih,pow_succ]
    ring
theorem slope_formula {m r : ℝ} (hm : 2<m) (hr : r∈Set.Ioo (lowerRoot m) (upperRoot m)) (n : ℕ) :
    orbit m r n=(lowerRoot m+upperRoot m*((lowerRoot m/upperRoot m)^n*ratio m r))/
      (1+(lowerRoot m/upperRoot m)^n*ratio m r) := by
  rw [← formula hm hr n]
  exact solve (interior hm hr n)
end KroneckerRootCrossRatioOrbit
end
end
