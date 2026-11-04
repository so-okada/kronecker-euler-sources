import KroneckerBoundedRationalNeighbor
import KroneckerComparisonIntervalWidth
import KroneckerEulerFramePositivity

/- Original module: KroneckerSmallComparisonParameters -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerSmallComparisonParameters
open KroneckerComparisonScales KroneckerFiberEnvelopeLimit

theorem envelope_nonneg (m : ℕ) (τ η : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : 0 ≤ η) :
    0 ≤ fiberEnvelope m τ η := by
  have hl : 0 ≤ Real.log (1+τ) := Real.log_nonneg (by linarith)
  have ht : Real.log τ ≤ 0 := Real.log_nonpos hτ.le hτ1
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold fiberEnvelope
  have hc : 0 ≤ 2*(m : ℝ)*Real.log 2-Real.log τ := by
    have : 0 ≤ 2*(m : ℝ)*Real.log 2 := by positivity
    linarith
  positivity

theorem small_comparison_parameters (m : ℕ) (B ε : ℝ) (hε : 0 < ε) :
    ∃ η τ : ℝ, 0 < η ∧ 0 < τ ∧ τ ≤ 1 ∧ inflationScale m*η < 1 ∧
      2*inflationScale m*η*B+2*fiberEnvelope m τ η < ε := by
  let τ : ℝ := min 1 (ε/16)
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτε : τ ≤ ε/16 := min_le_right _ _
  have hlog := KroneckerSmallLogParameter.log_one_add_le τ hτ
  let x : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hx : Tendsto x atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => 2*inflationScale m*x n*B+2*fiberEnvelope m τ (x n))
      atTop (𝓝 (2*Real.log (1+τ))) := by
    simpa only [mul_zero,zero_mul,zero_add] using
      ((hx.const_mul (2*inflationScale m)).mul_const B).add ((fiberEnvelope_limit m τ x hx).const_mul 2)
  have hscale : Tendsto (fun n => inflationScale m*x n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hx.const_mul (inflationScale m)
  obtain ⟨n,hn1,hn2⟩ := ((tendsto_order.1 hscale).2 1 (by norm_num)).and
    ((tendsto_order.1 hlim).2 ε (by linarith)) |>.exists
  exact ⟨x n,τ,by dsimp [x];positivity,hτ,hτ1,hn1,hn2⟩

end KroneckerSmallComparisonParameters
end

/- Original module: KroneckerIrrationalFrameJoint -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerIrrationalFrameJoint
open KroneckerIrrationalIntervals KroneckerComparisonScales KroneckerFiberEnvelopeLimit
open KroneckerFrameObservables KroneckerLogic

theorem irrational_frame_joint (m : ℕ) (hm : 4 ≤ m) (r : ℝ) (hr : Irrational r)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) :
    ∃ L : ℝ, JointLimit height slope (value m) r L := by
  let : Nonempty (Approaching height slope r) := approaching_nonempty height slope (frame_approximable r hr1)
  have hintervals : ∀ ε : ℝ, 0 < ε → ∃ l u : ℝ, u-l < ε ∧
      ∀ x : Approaching height slope r, ∀ᶠ n in atTop, l ≤ runValue m (x.val n) ∧ runValue m (x.val n) ≤ u := by
    intro ε hε
    let B : ℝ := (m : ℝ)*m*Real.log 2
    obtain ⟨η,τ,hη,hτ,hτ1,hsmall,hwidth⟩ :=
      KroneckerSmallComparisonParameters.small_comparison_parameters m B (ε/2) (by positivity)
    obtain ⟨δ,hδ,hcomp⟩ := irrational_intervals m hm r hr hr1 hrM η hη hsmall
    obtain ⟨t,p,q,hq,hp,ht,htM,hnear,_,hF⟩ :=
      KroneckerBoundedRationalNeighbor.bounded_rational_neighbor m hm r δ hr1 hrM hδ
    refine ⟨(1-inflationScale m*η)*(periodRate m t q-fiberEnvelope m τ η)-ε/8,
      (1+inflationScale m*η)*periodRate m t q+fiberEnvelope m τ η+ε/8,?_,?_⟩
    · have hE := KroneckerSmallComparisonParameters.envelope_nonneg m τ η hτ hτ1 hη.le
      have hH : 0 ≤ inflationScale m*η := by dsimp [inflationScale,collarScale];positivity
      have hw := KroneckerComparisonIntervalWidth.comparison_interval_width
        (periodRate m t q) B (fiberEnvelope m τ η) (inflationScale m*η) (ε/8) hF hE hH
      nlinarith
    · exact hcomp t ht htM hnear p q hq hp τ hτ hτ1 (ε/8) (by positivity)
  obtain ⟨L,hL⟩ := common_intervals_limit (fun x : Approaching height slope r => fun n => runValue m (x.val n)) hintervals
  refine ⟨L,jointLimit_of_sequences height slope (value m) ?_⟩
  intro x ha hs
  have hl := hL ⟨x,ha,hs⟩
  have hscale := KroneckerSampledPeriodicLimit.successor_length_density (fun n => (x n).a) ha
  have hn : ∀ᶠ n : ℕ in atTop, ((x n).a : ℝ)+1 ≠ 0 := Eventually.of_forall (fun n => by positivity)
  have hfinal := normalization_transport
    (a := fun n => ((x n).a : ℝ)) (b := fun n => ((x n).a : ℝ)+1)
    (V := fun n => Real.log (KroneckerWordCounts.runCount m
      (KroneckerFrameBadDensity.frameWord (x n).a (x n).b (x n).d) 0 : ℝ)) 1 L hn
    (by simpa only [Nat.cast_add,Nat.cast_one] using hscale) hl
  rw [one_mul] at hfinal
  exact hfinal



end KroneckerIrrationalFrameJoint
end

/- Original module: KroneckerInteriorSlopeCases -/
section
set_option autoImplicit false
namespace KroneckerInteriorSlopeCases
open KroneckerRationalEntropy

theorem interior_slope_cases (m : ℕ) (r : ℝ) (hr1 : 1 < r) (hrM : r < (m-1 : ℕ)) :
    Irrational r ∨ (∃ k : ℕ, r = k) ∨ r ∈ rationalSlopes m := by
  classical
  by_cases hi : Irrational r
  · exact Or.inl hi
  · obtain ⟨s,hs⟩ : ∃ s : ℚ, (s : ℝ) = r := by
      simpa only [Irrational,not_not,Set.mem_range] using hi
    have hs0 : (0 : ℚ) ≤ s := by exact_mod_cast (show (0 : ℝ) ≤ s by rw [hs]; linarith)
    have hn : 0 ≤ s.num := Rat.num_nonneg.mpr hs0
    let p : ℕ := s.num.toNat
    have hp : (p : ℝ) = (s.num : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hn)
    have he : r = (p : ℝ)/(s.den : ℝ) := by rw [← hs,Rat.cast_def,hp]
    by_cases hd : s.den ∣ p
    · exact Or.inr (Or.inl ⟨p/s.den,by rw [Nat.cast_div_charZero hd]; exact he⟩)
    · exact Or.inr (Or.inr ⟨⟨p,s.den,s.pos,hd,hr1,hrM,he⟩⟩)

end KroneckerInteriorSlopeCases
end
