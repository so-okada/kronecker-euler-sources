import KroneckerFullActualUpper
import KroneckerEventualFrameAlphabet
import KroneckerRationalReduction
import KroneckerPrimitiveApproximation
import KroneckerFrameIdentity

/- Original module: KroneckerFullFrameLimit -/
section
/-! The full-interior rational limit for literal finite coloring counts is unconditional. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFullFrameLimit
open KroneckerWordCounts KroneckerPeriodicTail KroneckerFrameSlope KroneckerFrameBadDensity
open KroneckerRationalWordRotation KroneckerRationalPeriodAlphabet KroneckerRationalFrameLower
open KroneckerFullActualUpper KroneckerEventualFrameAlphabet KroneckerEventualFramePhase

theorem full_frame_limit (m p q : ℕ) (hm : 3 ≤ m) (hq : 1 < q)
    (hc : p.Coprime q) (hlo : 1 < (p : ℝ)/(q : ℝ))
    (hhi : (p : ℝ)/(q : ℝ) < (m-1 : ℕ)) (a b d : ℕ → ℕ)
    (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    Tendsto (fun n => Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/(a n : ℝ))
      atTop (𝓝 (periodicGrowth m (rationalPeriod p q)/(q : ℝ))) := by
  have hlow := rational_frame_lower m hm (rationalPeriod p q)
    (rationalPeriod_nonempty p q (by omega)) (rationalPeriod_legal p q (m-1) hlo.le hhi.le)
    a b d (p : ℤ) ha hd
    (by simpa only [rationalPeriod_length,Int.cast_natCast] using hr)
    (eventual_frame_alphabet a b d (m-1) _ ha hd hr hlo hhi)
    (eventual_frame_phase p q hq hc a b d ha hd hr)
  simp only [rationalPeriod_length] at hlow
  have hupp := full_actual_frame_upper m p q hm hq hc hlo.le hhi a b d ha hd hr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hlow (ε/2) (by positivity),hupp (ε/2) (by positivity)] with n hnlo hnhi
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end KroneckerFullFrameLimit
end

/- Original module: KroneckerNonprimitiveFrameLimit -/
section
/-! The unconditional literal-frame limit is independent of fraction reduction. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerNonprimitiveFrameLimit
open KroneckerWordCounts KroneckerFrameBadDensity KroneckerPeriodicTail KroneckerRationalWordRotation
open KroneckerFullFrameLimit KroneckerRationalReduction KroneckerRationalRateInvariant

theorem nonprimitive_frame_limit (m p q : ℕ) (hm : 3 ≤ m) (hq : 0 < q)
    (hn : ¬q ∣ p) (hlo : 1 < (p : ℝ)/(q : ℝ))
    (hhi : (p : ℝ)/(q : ℝ) < (m-1 : ℕ)) (a b d : ℕ → ℕ)
    (ha : Tendsto a atTop atTop) (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    Tendsto (fun n => Real.log (runCount m (frameWord (a n) (b n) (d n)) 0 : ℝ)/(a n : ℝ))
      atTop (𝓝 (periodicGrowth m (rationalPeriod p q)/(q : ℝ))) := by
  obtain ⟨p',q',k,hk,hq',hc,hp,hqq,hs⟩ := rational_reduction p q hq hn
  have he := rational_rate_invariant m p q p' q' hm hq (by omega) hlo.le hhi.le hs
  rw [he]
  exact full_frame_limit m p' q' hm hq' hc (by rwa [←hs]) (by rwa [←hs]) a b d ha hd
    (by simpa only [hs] using hr)

end KroneckerNonprimitiveFrameLimit
end

/- Original module: KroneckerPrimitiveSequences -/
section
/-! An explicit existence theorem for approaching primitive sequences, including integer slopes. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerPrimitiveSequences
open KroneckerPrimitiveApproximation

theorem primitive_sequences (r : ℝ) (hr : 1 < r) :
    ∃ a b : ℕ → ℕ, (∀ n, 2 ≤ a n ∧ a n < b n ∧ (a n).Coprime (b n)) ∧
      Tendsto a atTop atTop ∧
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) := by
  choose a b h using fun n : ℕ => primitive_approximation r hr (n+1)
  have ha : Tendsto a atTop atTop :=
    tendsto_atTop_mono (fun n => (show n ≤ a n from by have := (h n).1; omega)) tendsto_id
  have hac : Tendsto (fun n => (a n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ha
  have hi : Tendsto (fun n => 2 / (a n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hac).const_mul 2
  refine ⟨a,b,fun n => ⟨(h n).2.1,(h n).2.2.1,(h n).2.2.2.1⟩,ha,?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hi) ε hε] with n hn
  have hn' : 2 / (a n : ℝ) < ε := by
    simpa [Real.dist_eq,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2/(a n : ℝ))] using hn
  exact (h n).2.2.2.2.trans_lt hn'

end KroneckerPrimitiveSequences
end

/- Original module: KroneckerParameterSequences -/
section
/-! The finite-frame parameter construction applies to actual primitive approaching dimensions. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerParameterSequences
open KroneckerFrameIdentity KroneckerPrimitiveSequences


end KroneckerParameterSequences
end

/- Original module: KroneckerParameterApproximable -/
section
/-! The density premise in the manuscript continuity lemma holds for constructed frame parameters. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerParameterApproximable
open KroneckerFrameIdentity KroneckerLogic KroneckerParameterSequences

abbrev ParameterDomain (m : ℕ) := {P : Parameters // P.m=m}
def height {m : ℕ} (P : ParameterDomain m) : ℕ := P.val.a
noncomputable def slope {m : ℕ} (P : ParameterDomain m) : ℝ := (P.val.b : ℝ)/P.val.a


end KroneckerParameterApproximable
end

/- Original module: KroneckerFrameObservables -/
section
/-! A concrete domain of literal frame counts, independent of the external Euler dictionary. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFrameObservables
open KroneckerLogic KroneckerWordCounts KroneckerFrameBadDensity
open KroneckerPrimitiveSequences

structure FramePoint where
  a : ℕ
  b : ℕ
  d : ℕ
  hd : 0 < d

def height (x : FramePoint) : ℕ := x.a
noncomputable def slope (x : FramePoint) : ℝ := (x.b : ℝ)/x.a
noncomputable def value (m : ℕ) (x : FramePoint) : ℝ :=
  Real.log (runCount m (frameWord x.a x.b x.d) 0 : ℝ)/(x.a : ℝ)

theorem frame_approximable (r : ℝ) (hr : 1 < r) : Approximable height slope r := by
  obtain ⟨a,b,_,ha,hs⟩ := primitive_sequences r hr
  intro δ hδ N
  obtain ⟨n,hn,hns⟩ := (ha.eventually (eventually_ge_atTop N)).and
    ((Metric.tendsto_nhds.mp hs) δ hδ) |>.exists
  exact ⟨⟨a n,b n,1,by decide⟩,hn,hns⟩

end KroneckerFrameObservables
end
