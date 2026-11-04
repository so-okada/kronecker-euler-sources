import KroneckerIntegerEditDensity
import KroneckerGeometricOperations
import KroneckerFrameIdentity

set_option autoImplicit false
namespace KroneckerIntegerSlopeFamily
open KroneckerFrameSlope KroneckerFrameBadDensity KroneckerMechanicalRuns
open KroneckerMechanicalWords KroneckerWordEditCost
open Filter
open scoped Topology

theorem coprime (a M : ℕ) : a.Coprime (M * a + 1) := by
  simp [Nat.coprime_mul_right_add_right]

theorem inverse (a M : ℕ) (ha : 2 ≤ a) : (M * a + 1) % a = 1 := by
  simp [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < a by omega)]

theorem slope (a M : ℕ) (ha : 0 < a) :
    frameSlope a (M * a + 1) (a + 1) = (M : ℝ) + 1 / (a + 1 : ℝ) := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hap : (a : ℝ) + 1 ≠ 0 := by positivity
  unfold frameSlope
  push_cast
  field_simp
  ring

theorem family_prefix (a M k : ℕ) (ha : 0 < a) (hk : k ≤ a) :
    mechanicalPrefix (frameSlope a (M * a + 1) (a + 1)) 0 k = (k * M : ℕ) := by
  unfold mechanicalPrefix
  rw [slope a M ha]
  apply Int.floor_eq_iff.mpr
  have hp : 0 < (a : ℝ) + 1 := by positivity
  have h0 : 0 ≤ (k : ℝ) / (a + 1 : ℝ) := by positivity
  have h1 : (k : ℝ) / (a + 1 : ℝ) < 1 := by
    apply (div_lt_one hp).mpr
    exact_mod_cast Nat.lt_succ_of_le hk
  push_cast
  constructor <;> nlinarith [show (k : ℝ) * (1 / (a + 1 : ℝ)) = k / (a + 1 : ℝ) by ring]

theorem run (a M i : ℕ) (ha : 0 < a) (hi : i < a) :
    natRun (frameSlope a (M * a + 1) (a + 1)) 0 i = M := by
  have h : mechanicalRun (frameSlope a (M * a + 1) (a + 1)) 0 i = M := by
    rw [mechanicalRun, family_prefix a M (i + 1) ha (by omega), family_prefix a M i ha hi.le]
    push_cast
    ring
  simp [natRun, h]

theorem frame (a M : ℕ) (ha : 0 < a) :
    frameWord a (M * a + 1) (a + 1) = List.replicate a M ++ [1] := by
  unfold frameWord mechanicalWord
  have h : (fun i : Fin a => natRun (frameSlope a (M * a + 1) (a + 1)) 0 (0 + i.val)) =
      fun _ : Fin a => M := by
    funext i
    simpa only [Nat.zero_add] using run a M i.val ha i.isLt
  rw [h]
  simp

def parameters (m a M : ℕ) (hm : 3 ≤ m) (ha : 2 ≤ a) (hM : 1 ≤ M) :
    KroneckerFrameIdentity.Parameters where
  m := m
  a := a
  b := M * a + 1
  d₁ := a + 1
  d₂ := M * (a + 1) + 1
  k := M
  hm := hm
  ha := ha
  hab := by nlinarith
  coprime := coprime a M
  hd₁ := by omega
  hd₂ := by nlinarith
  determinant := by push_cast; ring
  length_eq := by ring

theorem geometric_frame (a M : ℕ) (ha : 0 < a) (hM : 0 < M) :
    KroneckerPaperPaths.runPath (frameWord a (M * a + 1) (a + 1)) 0 =
      KroneckerPaperPaths.concat
        (KroneckerPaperPaths.power (KroneckerPaperPaths.simpleRun M hM) a)
        (KroneckerPaperPaths.simpleRun 1 (by decide)) := by
  have hr : KroneckerPeriodicWords.repeatRuns [M] a = List.replicate a M := by
    clear ha
    induction a with
    | zero => rfl
    | succ a ih => simp [KroneckerPeriodicWords.repeatRuns, ih, List.replicate_succ']
  rw [frame a M ha, KroneckerPaperPaths.runPath_append, ← hr,
    ← KroneckerPaperPaths.runPath_power, KroneckerPaperPaths.runPath_singleton M hM,
    KroneckerPaperPaths.runPath_singleton 1 (by decide)]

theorem edit_cost (a M : ℕ) (ha : 0 < a) (hM : 1 ≤ M) :
    wordEditCost (frameWord a (M * a + 1) (a + 1)) M = M - 1 := by
  have h := KroneckerFrameEditCost.frame_edit_cost a (M * a + 1) (a + 1) M
    ha (by omega) (by omega) hM
  have hz : ((M * a + 1 : ℕ) : ℤ) - 1 - (a : ℤ) * M = 0 := by push_cast; ring
  rw [hz, abs_zero, zero_add] at h
  omega

theorem ratio_above (a M : ℕ) (ha : 0 < a) :
    (M : ℝ) < ((M * a + 1 : ℕ) : ℝ) / a := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  apply (lt_div_iff₀ ha').mpr
  push_cast
  nlinarith

theorem ratio_limit (M : ℕ) :
    Tendsto (fun a : ℕ => ((M * a + 1 : ℕ) : ℝ) / a) atTop (𝓝 (M : ℝ)) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (M : ℝ)) atTop (𝓝 (M : ℝ))).add
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun a : ℕ => (1 : ℝ) / a) atTop (𝓝 (0 : ℝ)))
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with a ha
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  push_cast
  field_simp

end KroneckerIntegerSlopeFamily
