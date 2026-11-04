import KroneckerManuscriptSupportBound

/-! Extract the manuscript's constants C0,q in (0,1] from the already proved
slot constants A,B. The estimate is uniform in the varying slope parameter x. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerWeistUniformConstants
open KroneckerManuscriptSupportBound KroneckerLatticeScaleNormalization

def prefactor (A B : ℝ) : ℝ := A^2 / (8*B*(1/100 : ℝ)*(256 : ℝ)^2)
def gamma0 : ℝ := 1 - 256/100000

def baseRate (A B : ℝ) : ℝ := (6*A*B*(1/100 : ℝ)*gamma0^2)/(256/27 : ℝ)
def C0 (A B : ℝ) : ℝ := min 1 (prefactor A B)
def q (A B : ℝ) : ℝ := min 1 (baseRate A B)

theorem prefactor_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < prefactor A B := by
  unfold prefactor
  positivity

theorem baseRate_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < baseRate A B := by
  unfold baseRate gamma0
  norm_num
  positivity

theorem C0_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < C0 A B :=
  lt_min (by norm_num) (prefactor_pos hA hB)

theorem q_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < q A B :=
  lt_min (by norm_num) (baseRate_pos hA hB)

theorem C0_le_one (A B : ℝ) : C0 A B ≤ 1 := min_le_left _ _
theorem q_le_one (A B : ℝ) : q A B ≤ 1 := min_le_left _ _

theorem gamma_lower {x : ℝ} (hx : 100000 ≤ x) : gamma0 ≤ gamma x := by
  have hdiv : 256/x ≤ (256/100000 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold gamma gamma0
  linarith

theorem gamma_square_lower {x : ℝ} (hx : 100000 ≤ x) :
    gamma0^2 ≤ gamma x^2 := by
  have h := gamma_lower hx
  have hp : 0 ≤ gamma0 := by norm_num [gamma0]
  nlinarith

theorem rate_le {A B x : ℝ} (hA : 0 < A) (hB : 0 < B) (hx : 100000 ≤ x) :
    q A B ≤ (6*A*B*(1/100 : ℝ)*gamma x^2)/(256/27 : ℝ) := by
  apply (min_le_right _ _).trans
  unfold baseRate
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_left (gamma_square_lower hx) (by positivity)

theorem normalized_lower {A B x : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hx : 100000 ≤ x) (n a : ℕ) :
    C0 A B * (256/27 : ℝ)^a * x^(-5/2 : ℝ) * (q A B)^(n+1) ≤
      manuscriptLower n a x A B := by
  have hxp : 0 < x := by linarith
  have ht : 0 ≤ (256/27 : ℝ)^a*x^(-5/2 : ℝ) := by positivity
  have hp := pow_le_pow_left₀ (q_pos hA hB).le (rate_le hA hB hx) (n+1)
  have hc : C0 A B * ((256/27 : ℝ)^a*x^(-5/2 : ℝ)) ≤
      prefactor A B * ((256/27 : ℝ)^a*x^(-5/2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) ht
  have H := mul_le_mul hc hp (pow_nonneg (q_pos hA hB).le _)
    (mul_nonneg (prefactor_pos hA hB).le ht)
  simpa [manuscriptLower, prefactor, mul_assoc, mul_left_comm, mul_comm] using H

theorem inverse_scale {x : ℝ} (hx : 0 < x) :
    x^(-5/2 : ℝ) = (x⁻¹)^(5/2 : ℝ) := by
  rw [Real.inv_rpow hx.le, show (-5/2 : ℝ) = -(5/2 : ℝ) by norm_num,
    Real.rpow_neg hx.le]

theorem ratio_scale {a k : ℝ} (ha : 0 < a) (hk : 0 < k) :
    (a/k)^(-5/2 : ℝ) = (k/a)^(5/2 : ℝ) := by
  rw [inverse_scale (div_pos ha hk), inv_div]

end KroneckerWeistUniformConstants
