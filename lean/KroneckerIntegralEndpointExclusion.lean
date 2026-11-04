import KroneckerNullRootExclusion

/-! No positive source dimension has rational slope equal to either root
endpoint when m≥3. Endpoint limits are therefore approaches through distinct slopes. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerIntegralEndpointExclusion
open KroneckerEndpointRoots

theorem no_root (m : ℕ) (hm : 3≤m) (a b : ℕ) (ha : 0<a) :
    (m : ℝ)*((b : ℝ)/a)-1-((b : ℝ)/a)^2≠0 := by
  intro hr
  have ha' : (a : ℝ)≠0 := by exact_mod_cast (ne_of_gt ha)
  have hq : (a : ℝ)^2+(b : ℝ)^2-(m : ℝ)*a*b=0 := by
    field_simp at hr
    nlinarith
  have hqi : (a : ℤ)^2+(b : ℤ)^2-(m : ℤ)*a*b=0 := by exact_mod_cast hq
  exact (ne_of_gt ha) (KroneckerNullRootExclusion.zero m hm a b hqi).1

theorem endpoints (m : ℕ) (hm : 3≤m) (a b : ℕ) (ha : 0<a) :
    (b : ℝ)/a≠lowerRoot m ∧ (b : ℝ)/a≠upperRoot m := by
  have hm' : (2 : ℝ)≤m := by exact_mod_cast (show 2≤m by omega)
  constructor
  · intro h
    apply no_root m hm a b ha
    rw [h]
    exact lowerRoot_quadratic hm'
  · intro h
    apply no_root m hm a b ha
    rw [h]
    exact upperRoot_quadratic hm'
end KroneckerIntegralEndpointExclusion
