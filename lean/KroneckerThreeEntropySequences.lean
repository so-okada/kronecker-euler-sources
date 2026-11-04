import Mathlib.Analysis.SpecialFunctions.Log.Basic
import KroneckerBinaryMechanicalLemma
import KroneckerInteriorSlopeCases

section

/-! The eight-to-one exchange loss gives a linear logarithmic error. -/
set_option autoImplicit false
namespace KroneckerThreeCountLogTransfer

theorem eight_count_log_raw (x y k : ℕ) (hx : 0 < x)
    (hc : (x : ℝ)/(8 : ℝ)^k ≤ y) :
    Real.log (x : ℝ)-(k : ℝ)*Real.log 8 ≤ Real.log (y : ℝ) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have h := Real.log_le_log (div_pos hxR (by positivity : (0 : ℝ)<8^k)) hc
  simpa only [Real.log_div (ne_of_gt hxR) (by positivity : (8 : ℝ)^k ≠ 0),Real.log_pow] using h

theorem eight_count_log_transfer (x y l k : ℕ) (hx : 0 < x) (hl : 0 < l)
    (hc : (x : ℝ)/(8 : ℝ)^k ≤ y) :
    Real.log (x : ℝ)/(l : ℝ) ≤ Real.log (y : ℝ)/(l : ℝ)+((k : ℝ)/(l : ℝ))*Real.log 8 := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hlog := Real.log_le_log (div_pos hxR (by positivity : (0 : ℝ)<8^k)) hc
  rw [Real.log_div (ne_of_gt hxR) (by positivity),Real.log_pow] at hlog
  have hh := (div_le_div_iff_of_pos_right hlR).mpr hlog
  have he : (Real.log (x : ℝ)-(k : ℝ)*Real.log 8)/(l : ℝ)=
      Real.log (x : ℝ)/(l : ℝ)-((k : ℝ)/(l : ℝ))*Real.log 8 := by ring
  rw [he] at hh
  linarith

theorem eight_rate_log_transfer (x y l k : ℕ) (η : ℝ) (hx : 0 < x) (hl : 0 < l)
    (hc : (x : ℝ)/(8 : ℝ)^k ≤ y) (hk : (k : ℝ) ≤ η*(l : ℝ)) :
    Real.log (x : ℝ)/(l : ℝ) ≤ Real.log (y : ℝ)/(l : ℝ)+η*Real.log 8 := by
  have hh := eight_count_log_transfer x y l k hx hl hc
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hdiv : (k : ℝ)/(l : ℝ) ≤ η := (div_le_iff₀ hlR).mpr hk
  have hlog : (0 : ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hdiv hlog
  linarith

end KroneckerThreeCountLogTransfer
end

section

/- Original module: KroneckerThreeMechanicalTarget -/
section
/-! Apply mixed binary composition with every collar run prescribed by one exact mechanical target. -/
set_option autoImplicit false
namespace KroneckerThreeMechanicalTarget
open KroneckerMechanicalCollarIdentity KroneckerThreeFullComposition KroneckerMechanicalWords
open KroneckerRawBinaryEdits KroneckerWordCounts

theorem three_mechanical_target (R : List ℕ) (t v : ℝ) (P T K k : ℕ)
    (ht : 1 ≤ t ∧ t ≤ 2) (hR : ∀ r ∈ R, 1 ≤ r ∧ r ≤ 2)
    (p : RawBinary R (mechanicalWord t v (P+1) T) K k) (hP : K+4*k ≤ P) :
    (runCount 3 R 0 : ℝ)/(8 : ℝ)^k ≤
      (runCount 3 (mechanicalWord t v 0 (P+1+T+1+P)) 0 : ℝ) := by
  rw [mechanical_collar_identity]
  exact (three_full_composition R (mechanicalWord t v (P+1) T)
    (mechanicalWord t v 0 P) (mechanicalWord t v (P+1+T+1) P)
    (natRun_legal t v P 2 ht.1 ht.2) (natRun_legal t v (P+1+T) 2 ht.1 ht.2) p hR
    (mechanicalWord_legal t v 0 P 2 ht.1 ht.2)
    (mechanicalWord_legal t v (P+1+T+1) P 2 ht.1 ht.2)
    (mechanicalWord_length t v 0 P) (mechanicalWord_length t v (P+1+T+1) P) hP).2

end KroneckerThreeMechanicalTarget
end

/- Original module: KroneckerThreeFullMechanicalCount -/
section
/-! Full finite three-arrow counting comparison into an exact prescribed mechanical target. -/
set_option autoImplicit false
namespace KroneckerThreeFullMechanicalCount
open KroneckerBinaryMechanicalLemma KroneckerBinaryMechanicalSource KroneckerBinarySlopeMargin
open KroneckerThreeMechanicalTarget KroneckerMechanicalWords KroneckerMechanicalWordShift KroneckerWordCounts

theorem three_full_mechanical_count (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ l T P : ℕ, ∀ R : List ℕ,
      BinaryMechanicalSource s u l R → (1+η)*(l : ℝ)+(B : ℝ) ≤ T →
      ((T-l : ℕ) : ℝ)+4*(η*(l : ℝ)+B) ≤ P →
      ∃ k : ℕ, (k : ℝ) ≤ η*(l : ℝ)+B ∧
        (runCount 3 R 0 : ℝ)/(8 : ℝ)^k ≤
          (runCount 3 (mechanicalWord t v 0 (P+1+T+1+P)) 0 : ℝ) := by
  obtain ⟨d,hd,B,hB,h⟩ := binary_mechanical_lemma r η hr hrb hη
  obtain ⟨τ,hτ,hm⟩ := binary_slope_margin r hrb
  refine ⟨min d τ,lt_min hd hτ,B,hB,?_⟩
  intro s t hs ht u v l T P R hR hT hP
  have hsb := (hm s (hs.trans_le (min_le_right _ _))).1
  have htb := (hm t (ht.trans_le (min_le_right _ _))).1
  obtain ⟨k,⟨p⟩,hk⟩ := h s t (hs.trans_le (min_le_left _ _)) (ht.trans_le (min_le_left _ _))
    u (v+((P+1 : ℕ) : ℝ)*t) l T R hR hT
  rw [← word_shift t v (P+1) T] at p
  have hbudget : T-l+4*k ≤ P := by
    have hreal : ((T-l+4*k : ℕ) : ℝ) ≤ P := by push_cast; linarith
    exact_mod_cast hreal
  exact ⟨k,hk,three_mechanical_target R t v P T (T-l) k htb (binary_source_legal hR hsb) p hbudget⟩

end KroneckerThreeFullMechanicalCount
end

/- Original module: KroneckerThreeEventualMechanicalCount -/
section
/-! Absorb the finite constants to obtain a denominator-free small-rate counting comparison for long words. -/
set_option autoImplicit false
namespace KroneckerThreeEventualMechanicalCount
open KroneckerThreeFullMechanicalCount KroneckerBinaryMechanicalSource
open KroneckerMechanicalWords KroneckerWordCounts

theorem three_eventual_mechanical_count (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ l T P : ℕ, ∀ R : List ℕ,
      N ≤ l → BinaryMechanicalSource s u l R → (1+η)*(l : ℝ) ≤ T →
      ((T-l : ℕ) : ℝ)+4*η*(l : ℝ) ≤ P →
      ∃ k : ℕ, (k : ℝ) ≤ η*(l : ℝ) ∧
        (runCount 3 R 0 : ℝ)/(8 : ℝ)^k ≤
          (runCount 3 (mechanicalWord t v 0 (P+1+T+1+P)) 0 : ℝ) := by
  obtain ⟨δ,hδ,B,hB,h⟩ := three_full_mechanical_count r (η/2) hr hrb (by positivity)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*(B : ℝ)/η))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNB : 2*(B : ℝ)/η < N := (le_max_right _ _).trans_lt hN
  have hNpos : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  refine ⟨δ,hδ,N,hNpos,?_⟩
  intro s t hs ht u v l T P R hl hR hT hP
  have hNl : (N : ℝ) ≤ l := by exact_mod_cast hl
  have hBbound : (B : ℝ) ≤ (η/2)*(l : ℝ) := by
    have hh := (div_lt_iff₀ hη).mp hNB
    have hm := mul_le_mul_of_nonneg_left hNl hη.le
    nlinarith
  obtain ⟨k,hk,hcount⟩ := h s t hs ht u v l T P R hR (by nlinarith) (by nlinarith)
  exact ⟨k,by nlinarith,hcount⟩

end KroneckerThreeEventualMechanicalCount
end

/- Original module: KroneckerThreeMechanicalLog -/
section
/-! The full three-arrow comparison has logarithmic loss at most eta*log8 on all sufficiently long sources. -/
set_option autoImplicit false
namespace KroneckerThreeMechanicalLog
open KroneckerThreeEventualMechanicalCount KroneckerThreeCountLogTransfer KroneckerBinaryMechanicalSource
open KroneckerBinarySlopeMargin KroneckerMechanicalWords KroneckerWordCounts KroneckerWordBounds

theorem three_mechanical_log (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ l T P : ℕ, ∀ R : List ℕ,
      N ≤ l → BinaryMechanicalSource s u l R → (1+η)*(l : ℝ) ≤ T →
      ((T-l : ℕ) : ℝ)+4*η*(l : ℝ) ≤ P →
      Real.log (runCount 3 R 0 : ℝ)/(l : ℝ) ≤
        Real.log (runCount 3 (mechanicalWord t v 0 (P+1+T+1+P)) 0 : ℝ)/(l : ℝ)+η*Real.log 8 := by
  obtain ⟨d,hd,N,hN,h⟩ := three_eventual_mechanical_count r η hr hrb hη
  obtain ⟨τ,hτ,hm⟩ := binary_slope_margin r hrb
  refine ⟨min d τ,lt_min hd hτ,N,hN,?_⟩
  intro s t hs ht u v l T P R hl hR hT hP
  have hsb := (hm s (hs.trans_le (min_le_right _ _))).1
  obtain ⟨k,hk,hcount⟩ := h s t (hs.trans_le (min_le_left _ _)) (ht.trans_le (min_le_left _ _))
    u v l T P R hl hR hT hP
  have hlpos : 0 < l := hN.trans_le hl
  have hne : R ≠ [] := by
    intro he
    have hh := binary_source_length hR
    rw [he,List.length_nil] at hh
    omega
  have hpos := runCount_pos 3 (by omega) R hne (binary_source_legal hR hsb)
  exact eight_rate_log_transfer _ _ l k η hpos hlpos hcount hk

end KroneckerThreeMechanicalLog
end
end

section

/- Original module: KroneckerBinaryMechanicalEventual -/
section
/-! For long sources the full binary program has exchange rate at most eta with no additive error. -/
set_option autoImplicit false
namespace KroneckerBinaryMechanicalEventual
open KroneckerBinaryMechanicalLemma KroneckerBinaryMechanicalSource KroneckerMechanicalWords KroneckerRawBinaryEdits

theorem binary_mechanical_eventual (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ l T : ℕ, ∀ R : List ℕ,
      N ≤ l → BinaryMechanicalSource s u l R → (1+η)*(l : ℝ) ≤ T →
      ∃ k, Nonempty (RawBinary R (mechanicalWord t v 0 T) (T-l) k) ∧ (k : ℝ) ≤ η*(l : ℝ) := by
  obtain ⟨δ,hδ,B,hB,h⟩ := binary_mechanical_lemma r (η/2) hr hrb (by positivity)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*(B : ℝ)/η))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNB : 2*(B : ℝ)/η < N := (le_max_right _ _).trans_lt hN
  have hNpos : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  refine ⟨δ,hδ,N,hNpos,?_⟩
  intro s t hs ht u v l T R hl hR hT
  have hNl : (N : ℝ) ≤ l := by exact_mod_cast hl
  have hBbound : (B : ℝ) ≤ (η/2)*(l : ℝ) := by
    have hh := (div_lt_iff₀ hη).mp hNB
    have hm := mul_le_mul_of_nonneg_left hNl hη.le
    nlinarith
  obtain ⟨k,hp,hk⟩ := h s t hs ht u v l T R hR (by nlinarith)
  exact ⟨k,hp,by nlinarith⟩

end KroneckerBinaryMechanicalEventual
end

/- Original module: KroneckerThreeFrameTargetCount -/
section
/-! Compare a mechanical binary source to a prescribed literal frame target. -/
set_option autoImplicit false
namespace KroneckerThreeFrameTargetCount
open KroneckerBinaryMechanicalEventual KroneckerBinaryMechanicalSource KroneckerThreeFullComposition
open KroneckerFrameBadDensity KroneckerFrameSlope KroneckerMechanicalWords KroneckerWordCounts

theorem three_frame_target_count (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ s u : ℝ,
      (1 ≤ s ∧ s ≤ 2) → |s-r| < δ → ∀ a b d l T P : ℕ,
      (1 ≤ frameSlope a b d ∧ frameSlope a b d ≤ 2) → |frameSlope a b d-r| < δ →
      N ≤ l → P+1+T+1+P=a+1 → (1+η)*(l : ℝ) ≤ T →
      ((T-l : ℕ) : ℝ)+4*η*(l : ℝ) ≤ P →
      ∃ k : ℕ, (k : ℝ) ≤ η*(l : ℝ) ∧
        (runCount 3 (mechanicalWord s u 0 l) 0 : ℝ)/(8 : ℝ)^k ≤
          (runCount 3 (frameWord a b d) 0 : ℝ) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := binary_mechanical_eventual r η hr hrb hη
  refine ⟨δ,hδ,N,hN,?_⟩
  intro s u hs hsr a b d l T P ht htr hl hsize hT hP
  obtain ⟨A,x,y,B,hX,hA,hB⟩ := KroneckerFrameCollarIdentity.frame_collar_identity a b d P T hsize
  have hlegal := KroneckerFrameWord.frameWord_legal a b d 2 ht.1 ht.2
  have hx : 1 ≤ x ∧ x ≤ 2 := hlegal x (by rw [hX]; simp)
  have hy : 1 ≤ y ∧ y ≤ 2 := hlegal y (by rw [hX]; simp)
  have hleft : ∀ z ∈ A, 1 ≤ z ∧ z ≤ 2 := by
    intro z hz
    exact hlegal z (by rw [hX]; simp [hz])
  have hright : ∀ z ∈ B, 1 ≤ z ∧ z ≤ 2 := by
    intro z hz
    exact hlegal z (by rw [hX]; simp [hz])
  obtain ⟨k,⟨p⟩,hk⟩ := h s (frameSlope a b d) hsr htr u
    ((P+1 : ℕ)*frameSlope a b d) l T (mechanicalWord s u 0 l) hl (Or.inl rfl) hT
  have hbudget : T-l+4*k ≤ P := by
    have hreal : ((T-l+4*k : ℕ) : ℝ) ≤ P := by push_cast; nlinarith
    exact_mod_cast hreal
  have hcount := (three_full_composition (mechanicalWord s u 0 l) _ A B hx hy p
    (mechanicalWord_legal s u 0 l 2 hs.1 hs.2) hleft hright hA hB hbudget).2
  exact ⟨k,hk,by simpa only [← hX] using hcount⟩

end KroneckerThreeFrameTargetCount
end

/- Original module: KroneckerThreeFrameTargetLog -/
section
/-! Reverse frame comparison with the actual linear logarithmic exchange loss. -/
set_option autoImplicit false
namespace KroneckerThreeFrameTargetLog
open KroneckerThreeFrameTargetCount KroneckerThreeCountLogTransfer
open KroneckerFrameBadDensity KroneckerFrameSlope KroneckerMechanicalWords KroneckerWordCounts

theorem three_frame_target_log (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ s u : ℝ,
      (1 ≤ s ∧ s ≤ 2) → |s-r| < δ → ∀ a b d l T P : ℕ,
      (1 ≤ frameSlope a b d ∧ frameSlope a b d ≤ 2) → |frameSlope a b d-r| < δ →
      N ≤ l → P+1+T+1+P=a+1 → (1+η)*(l : ℝ) ≤ T →
      ((T-l : ℕ) : ℝ)+4*η*(l : ℝ) ≤ P →
      Real.log (runCount 3 (mechanicalWord s u 0 l) 0 : ℝ)/((a : ℝ)+1)-
        ((l : ℝ)/((a : ℝ)+1))*(η*Real.log 8) ≤
      Real.log (runCount 3 (frameWord a b d) 0 : ℝ)/((a : ℝ)+1) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := three_frame_target_count r η hr hrb hη
  refine ⟨δ,hδ,N,hN,?_⟩
  intro s u hs hsr a b d l T P ht htr hl hsize hT hP
  obtain ⟨k,hk,hcount⟩ := h s u hs hsr a b d l T P ht htr hl hsize hT hP
  have hlpos : 0 < l := hN.trans_le hl
  have hne : mechanicalWord s u 0 l ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [mechanicalWord_length,List.length_nil] at hh
    omega
  have hpos := KroneckerWordBounds.runCount_pos 3 (by omega) _ hne (mechanicalWord_legal s u 0 l 2 hs.1 hs.2)
  have hlog := eight_count_log_raw _ _ k hpos hcount
  have hnonneg : (0 : ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hk hnonneg
  have hraw : Real.log (runCount 3 (mechanicalWord s u 0 l) 0 : ℝ)-
      (l : ℝ)*(η*Real.log 8) ≤ Real.log (runCount 3 (frameWord a b d) 0 : ℝ) := by nlinarith
  have hnorm := div_le_div_of_nonneg_right hraw (show (0 : ℝ) ≤ (a : ℝ)+1 by positivity)
  simpa only [sub_div,mul_div_right_comm] using hnorm

end KroneckerThreeFrameTargetLog
end

/- Original module: KroneckerThreeEventualLower -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerThreeEventualLower
open KroneckerComparisonSchedules KroneckerComparisonScales KroneckerFrameBadDensity
open KroneckerWordCounts KroneckerMechanicalWords

theorem three_eventual_lower (r : ℝ) (hr : Irrational r) (hrb : 1 < r ∧ r < 2)
    (η : ℝ) (hη : 0 < η) (hsmall : inflationScale 3*η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t v : ℝ, (1 ≤ t ∧ t ≤ 2) → |t-r| < δ →
      ∀ q : ℕ, 0 < q → ∀ a b d : ℕ → ℕ, Tendsto a atTop atTop → (∀ n,0 < d n) →
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) → ∀ᶠ n in atTop,
      Real.log (runCount 3 (mechanicalWord t v 0 (lowerLength 3 q η (a n+1))) 0 : ℝ)/((a n : ℝ)+1)-
        ((lowerLength 3 q η (a n+1) : ℝ)/((a n : ℝ)+1))*(η*Real.log 8) ≤
      Real.log (runCount 3 (frameWord (a n) (b n) (d n)) 0 : ℝ)/((a n : ℝ)+1) := by
  obtain ⟨δ,hδ,N,hN,h⟩ := KroneckerThreeFrameTargetLog.three_frame_target_log r η hr hrb hη
  refine ⟨δ,hδ,?_⟩
  intro t v ht htr q hq a b d ha hd hratio
  have has : Tendsto (fun n => a n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp ha
  have hbud := KroneckerLowerScheduleBudget.lower_schedule_budget (fun n => a n+1) has 3 q N hq η hη hsmall
  have hdata := KroneckerEventualFrameData.eventual_frame_data a b d ha hd r hratio 2 0 hrb.1 hrb.2 δ hδ
  filter_upwards [hbud,hdata] with n hn hdatan
  exact h t v ht htr (a n) (b n) (d n)
    (lowerLength 3 q η (a n+1)) (lowerMiddle 3 η (a n+1)) (collar 3 η (a n+1))
    ⟨hdatan.2.2.1,hdatan.2.2.2.1⟩ hdatan.2.2.2.2 hn.1 hn.2.2.2 hn.2.1 hn.2.2.1

end KroneckerThreeEventualLower
end

/- Original module: KroneckerThreeIrrationalLower -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerThreeIrrationalLower
open KroneckerComparisonSchedules KroneckerComparisonScales KroneckerPeriodicTail
open KroneckerFrameBadDensity KroneckerWordCounts KroneckerMechanicalWords

theorem three_irrational_lower (r : ℝ) (hr : Irrational r) (hrb : 1 < r ∧ r < 2)
    (η : ℝ) (hη : 0 < η) (hsmall : inflationScale 3*η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t v : ℝ, (1 ≤ t ∧ t ≤ 2) → |t-r| < δ →
      ∀ p : ℤ, ∀ q : ℕ, 0 < q → (q : ℝ)*t=p →
      ∀ a b d : ℕ → ℕ, Tendsto a atTop atTop → (∀ n,0 < d n) →
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (1-inflationScale 3*η)*(periodicGrowth 3 (mechanicalWord t v 0 q)/(q : ℝ)-η*Real.log 8)-ε ≤
      Real.log (runCount 3 (frameWord (a n) (b n) (d n)) 0 : ℝ)/((a n : ℝ)+1) := by
  obtain ⟨δ,hδ,h⟩ := KroneckerThreeEventualLower.three_eventual_lower r hr hrb η hη hsmall
  refine ⟨δ,hδ,?_⟩
  intro t v ht htr p q hq hp a b d ha hd hratio ε hε
  have has : Tendsto (fun n => a n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp ha
  have hc : 0 < 1-inflationScale 3*η := by linarith
  have hlog := KroneckerRoundedPeriodicLog.lower_rounded_periodic_log 3 (by omega) t v p q hq hp ht.1 ht.2
    (fun n => a n+1) has (1-inflationScale 3*η) hc
  have hlen := KroneckerPeriodicRounding.lower_period_length_density (fun n => a n+1) has q hq
    (1-inflationScale 3*η) hc.le
  have hlim := hlog.sub (hlen.mul_const (η*Real.log 8))
  have hbound := (tendsto_order.1 hlim).1
    ((1-inflationScale 3*η)*(periodicGrowth 3 (mechanicalWord t v 0 q)/(q : ℝ)-η*Real.log 8)-ε)
    (by nlinarith)
  filter_upwards [h t v ht htr q hq a b d ha hd hratio,hbound] with n hn hb
  refine le_trans ?_ hn
  simpa only [lowerLength,Nat.cast_add,Nat.cast_one] using hb.le

end KroneckerThreeIrrationalLower
end

/- Original module: KroneckerThreeFrameUpperLog -/
section
/-! The literal frame is an allowed binary mechanical source with exceptional last run one. -/
set_option autoImplicit false
namespace KroneckerThreeFrameUpperLog
open KroneckerThreeMechanicalLog KroneckerBinaryMechanicalSource KroneckerFrameBadDensity
open KroneckerFrameSlope KroneckerMechanicalWords KroneckerWordCounts

theorem three_frame_upper_log (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 0 < N ∧ ∀ a b d : ℕ,
      N ≤ a → |frameSlope a b d-r| < δ → ∀ t v : ℝ, |t-r| < δ → ∀ T P : ℕ,
      (1+η)*((a : ℝ)+1) ≤ T →
      ((T-(a+1) : ℕ) : ℝ)+4*η*((a : ℝ)+1) ≤ P →
      Real.log (runCount 3 (frameWord a b d) 0 : ℝ)/((a : ℝ)+1) ≤
        Real.log (runCount 3 (mechanicalWord t v 0 (P+1+T+1+P)) 0 : ℝ)/((a : ℝ)+1)+η*Real.log 8 := by
  obtain ⟨δ,hδ,N,hN,h⟩ := three_mechanical_log r η hr hrb hη
  refine ⟨δ,hδ,N,hN,?_⟩
  intro a b d ha hs t v ht T P hT hP
  have hsource : BinaryMechanicalSource (frameSlope a b d) 0 (a+1) (frameWord a b d) :=
    Or.inr ⟨a,1,rfl,by omega,by omega,rfl⟩
  simpa only [Nat.cast_add,Nat.cast_one] using h (frameSlope a b d) t hs ht 0 v (a+1) T P
    (frameWord a b d) (by omega) hsource (by simpa using hT) (by simpa using hP)

end KroneckerThreeFrameUpperLog
end

/- Original module: KroneckerThreeEventualUpper -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerThreeEventualUpper
open KroneckerComparisonSchedules KroneckerFrameBadDensity KroneckerWordCounts KroneckerMechanicalWords

theorem three_eventual_upper (r : ℝ) (hr : Irrational r) (hrb : 1 < r ∧ r < 2)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t v : ℝ, |t-r| < δ → ∀ q : ℕ, 0 < q →
      ∀ a b d : ℕ → ℕ, Tendsto a atTop atTop → (∀ n,0 < d n) →
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) → ∀ᶠ n in atTop,
      Real.log (runCount 3 (frameWord (a n) (b n) (d n)) 0 : ℝ)/((a n : ℝ)+1) ≤
      Real.log (runCount 3 (mechanicalWord t v 0 (upperLength 3 q η (a n+1))) 0 : ℝ)/((a n : ℝ)+1)+η*Real.log 8 := by
  obtain ⟨δ,hδ,N,hN,h⟩ := KroneckerThreeFrameUpperLog.three_frame_upper_log r η hr hrb hη
  refine ⟨δ,hδ,?_⟩
  intro t v htr q hq a b d ha hd hratio
  have has : Tendsto (fun n => a n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp ha
  have hbud := KroneckerUpperScheduleBudget.upper_schedule_budget (fun n => a n+1) has 3 q 0 hq η hη
  have hdata := KroneckerEventualFrameData.eventual_frame_data a b d ha hd r hratio 2 N hrb.1 hrb.2 δ hδ
  filter_upwards [hbud,hdata] with n hn hdatan
  have hh := h (a n) (b n) (d n) hdatan.1 hdatan.2.2.2.2 t v htr
    (upperMiddle 3 q η (a n+1)) (collar 3 η (a n+1))
    (by simpa only [Nat.cast_add,Nat.cast_one] using hn.2.1)
    (by simpa using hn.2.2.1)
  simpa only [hn.2.2.2] using hh

end KroneckerThreeEventualUpper
end

/- Original module: KroneckerThreeIrrationalUpper -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerThreeIrrationalUpper
open KroneckerComparisonSchedules KroneckerComparisonScales KroneckerPeriodicTail
open KroneckerFrameBadDensity KroneckerWordCounts KroneckerMechanicalWords

theorem three_irrational_upper (r : ℝ) (hr : Irrational r) (hrb : 1 < r ∧ r < 2)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t v : ℝ, (1 ≤ t ∧ t ≤ 2) → |t-r| < δ →
      ∀ p : ℤ, ∀ q : ℕ, 0 < q → (q : ℝ)*t=p →
      ∀ a b d : ℕ → ℕ, Tendsto a atTop atTop → (∀ n,0 < d n) →
      Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 r) → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (runCount 3 (frameWord (a n) (b n) (d n)) 0 : ℝ)/((a n : ℝ)+1) ≤
        (1+inflationScale 3*η)*(periodicGrowth 3 (mechanicalWord t v 0 q)/(q : ℝ))+η*Real.log 8+ε := by
  obtain ⟨δ,hδ,h⟩ := KroneckerThreeEventualUpper.three_eventual_upper r hr hrb η hη
  refine ⟨δ,hδ,?_⟩
  intro t v ht htr p q hq hp a b d ha hd hratio ε hε
  have has : Tendsto (fun n => a n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp ha
  have hlim := KroneckerRoundedPeriodicLog.upper_rounded_periodic_log 3 (by omega) t v p q hq hp ht.1 ht.2
    (fun n => a n+1) has (1+inflationScale 3*η) (upper_scale_slack 3 η hη).2.1
  have hbound := (tendsto_order.1 (hlim.add_const (η*Real.log 8))).2
    ((1+inflationScale 3*η)*(periodicGrowth 3 (mechanicalWord t v 0 q)/(q : ℝ))+η*Real.log 8+ε)
    (by linarith)
  filter_upwards [h t v htr q hq a b d ha hd hratio,hbound] with n hn hb
  exact hn.trans (by simpa only [upperLength,Nat.cast_add,Nat.cast_one] using hb.le)

end KroneckerThreeIrrationalUpper
end

/- Original module: KroneckerThreeIrrationalIntervals -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerThreeIrrationalIntervals
open KroneckerComparisonScales KroneckerIrrationalIntervals KroneckerFrameObservables KroneckerLogic

theorem three_irrational_intervals (r : ℝ) (hr : Irrational r) (hrb : 1 < r ∧ r < 2)
    (η : ℝ) (hη : 0 < η) (hsmall : inflationScale 3*η < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, (1 ≤ t ∧ t ≤ 2) → |t-r| < δ →
      ∀ p : ℤ, ∀ q : ℕ, 0 < q → (q : ℝ)*t=p → ∀ ε : ℝ, 0 < ε →
      ∀ x : Approaching height slope r, ∀ᶠ n in atTop,
      (1-inflationScale 3*η)*(periodRate 3 t q-η*Real.log 8)-ε ≤ runValue 3 (x.val n) ∧
      runValue 3 (x.val n) ≤ (1+inflationScale 3*η)*periodRate 3 t q+η*Real.log 8+ε := by
  obtain ⟨δu,hδu,hu⟩ := KroneckerThreeIrrationalUpper.three_irrational_upper r hr hrb η hη
  obtain ⟨δl,hδl,hl⟩ := KroneckerThreeIrrationalLower.three_irrational_lower r hr hrb η hη hsmall
  refine ⟨min δu δl,lt_min hδu hδl,?_⟩
  intro t ht htr p q hq hp ε hε x
  have hu' := hu t 0 ht (htr.trans_le (min_le_left _ _)) p q hq hp
    (fun n => (x.val n).a) (fun n => (x.val n).b) (fun n => (x.val n).d)
    x.property.1 (fun n => (x.val n).hd) x.property.2 ε hε
  have hl' := hl t 0 ht (htr.trans_le (min_le_right _ _)) p q hq hp
    (fun n => (x.val n).a) (fun n => (x.val n).b) (fun n => (x.val n).d)
    x.property.1 (fun n => (x.val n).hd) x.property.2 ε hε
  exact hl'.and hu'

end KroneckerThreeIrrationalIntervals
end

/- Original module: KroneckerThreeRationalNeighbor -/
section
/-! A nearby rational binary slope has a uniformly bounded periodic growth rate at m=3. -/
set_option autoImplicit false
namespace KroneckerThreeRationalNeighbor
open KroneckerBoundedRationalNeighbor KroneckerIrrationalIntervals

theorem three_rational_neighbor (r δ : ℝ) (hr : 1 < r ∧ r < 2) (hδ : 0 < δ) :
    ∃ t : ℝ, ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧ (q : ℝ)*t=p ∧
      (1 ≤ t ∧ t ≤ 2) ∧ |t-r| < δ ∧ 0 ≤ periodRate 3 t q ∧ periodRate 3 t q ≤ 9*Real.log 2 := by
  have hleft : max 1 (r-δ/2) < r := max_lt hr.1 (by linarith)
  have hright : r < min 2 (r+δ/2) := lt_min hr.2 (by linarith)
  obtain ⟨s,hslo,hshi⟩ := exists_rat_btwn (hleft.trans hright)
  have ht1 : 1 ≤ (s : ℝ) := (lt_of_le_of_lt (le_max_left _ _) hslo).le
  have ht2 : (s : ℝ) ≤ 2 := (lt_of_lt_of_le hshi (min_le_left _ _)).le
  have hnear : |(s : ℝ)-r| < δ := by
    have hl := lt_of_le_of_lt (le_max_right _ _) hslo
    have hu := lt_of_lt_of_le hshi (min_le_right _ _)
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hq : 0 < s.den := s.pos
  have hp : (s.den : ℝ)*(s : ℝ)=(s.num : ℝ) := by
    rw [Rat.cast_def]
    have hq0 : (s.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    field_simp
  have hb := period_rate_bound 3 (by omega) (s : ℝ) s.den hq ht1 ht2
  refine ⟨s,s.num,s.den,hq,hp,⟨ht1,ht2⟩,hnear,hb.1,?_⟩
  norm_num at hb ⊢
  exact hb.2

end KroneckerThreeRationalNeighbor
end

/- Original module: KroneckerThreeSmallParameters -/
section
/-! The linear exchange loss and collar inflation can be made jointly arbitrarily small. -/
set_option autoImplicit false
namespace KroneckerThreeSmallParameters
open KroneckerComparisonScales

theorem three_small_parameters (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ inflationScale 3*η < 1 ∧
      2*(inflationScale 3*η)*B+2*(η*Real.log 8) < ε := by
  let A := 32*B+2*Real.log 8+1
  have hlog : (0 : ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  let η := min (1/32) (ε/(2*A))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1/32 := min_le_left _ _
  have hη2 : η ≤ ε/(2*A) := min_le_right _ _
  have hm := (le_div_iff₀ (by positivity : (0 : ℝ)<2*A)).mp hη2
  refine ⟨η,hη,?_,?_⟩
  · norm_num [inflationScale,collarScale]
    linarith
  · norm_num [inflationScale,collarScale]
    dsimp [A] at hm
    nlinarith

end KroneckerThreeSmallParameters
end

/- Original module: KroneckerThreeIrrationalFrameJoint -/
section
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerThreeIrrationalFrameJoint
open KroneckerThreeIrrationalIntervals KroneckerThreeRationalNeighbor KroneckerThreeSmallParameters
open KroneckerIrrationalIntervals KroneckerComparisonScales KroneckerFrameObservables KroneckerLogic

theorem three_irrational_frame_joint (r : ℝ) (hr : Irrational r) (hrb : 1 < r ∧ r < 2) :
    ∃ L : ℝ, JointLimit height slope (value 3) r L := by
  let : Nonempty (Approaching height slope r) := approaching_nonempty height slope (frame_approximable r hrb.1)
  have hintervals : ∀ ε : ℝ, 0 < ε → ∃ l u : ℝ, u-l < ε ∧
      ∀ x : Approaching height slope r, ∀ᶠ n in atTop, l ≤ runValue 3 (x.val n) ∧ runValue 3 (x.val n) ≤ u := by
    intro ε hε
    let B : ℝ := 9*Real.log 2
    have hB : 0 ≤ B := by dsimp [B]; exact mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
    obtain ⟨η,hη,hsmall,hwidth⟩ := three_small_parameters B (ε/2) hB (by positivity)
    obtain ⟨δ,hδ,hcomp⟩ := three_irrational_intervals r hr hrb η hη hsmall
    obtain ⟨t,p,q,hq,hp,ht,hnear,hF0,hF⟩ := three_rational_neighbor r δ hrb hδ
    refine ⟨(1-inflationScale 3*η)*(periodRate 3 t q-η*Real.log 8)-ε/8,
      (1+inflationScale 3*η)*periodRate 3 t q+η*Real.log 8+ε/8,?_,?_⟩
    · have hE : 0 ≤ η*Real.log 8 := mul_nonneg hη.le (Real.log_nonneg (by norm_num))
      have hH : 0 ≤ inflationScale 3*η := by dsimp [inflationScale,collarScale]; positivity
      have hw := KroneckerComparisonIntervalWidth.comparison_interval_width
        (periodRate 3 t q) B (η*Real.log 8) (inflationScale 3*η) (ε/8) hF hE hH
      nlinarith
    · exact hcomp t ht hnear p q hq hp (ε/8) (by positivity)
  obtain ⟨L,hL⟩ := common_intervals_limit (fun x : Approaching height slope r => fun n => runValue 3 (x.val n)) hintervals
  refine ⟨L,jointLimit_of_sequences height slope (value 3) ?_⟩
  intro x ha hs
  have hl := hL ⟨x,ha,hs⟩
  have hscale := KroneckerSampledPeriodicLimit.successor_length_density (fun n => (x n).a) ha
  have hn : ∀ᶠ n : ℕ in atTop, ((x n).a : ℝ)+1 ≠ 0 := Eventually.of_forall (fun n => by positivity)
  have hfinal := normalization_transport
    (a := fun n => ((x n).a : ℝ)) (b := fun n => ((x n).a : ℝ)+1)
    (V := fun n => Real.log (KroneckerWordCounts.runCount 3
      (KroneckerFrameBadDensity.frameWord (x n).a (x n).b (x n).d) 0 : ℝ)) 1 L hn
    (by simpa only [Nat.cast_add,Nat.cast_one] using hscale) hl
  rw [one_mul] at hfinal
  exact hfinal

end KroneckerThreeIrrationalFrameJoint
end

/- Original module: KroneckerThreeInteriorExistence -/
section
/-! Irrational and rational cases cover every slope strictly between one and two. -/
set_option autoImplicit false
namespace KroneckerThreeInteriorExistence
open KroneckerLogic KroneckerFrameObservables

theorem three_interior_limit_exists (r : ℝ) (hr : 1 < r ∧ r < 2) :
    ∃ L : ℝ, JointLimit height slope (value 3) r L := by
  rcases KroneckerInteriorSlopeCases.interior_slope_cases 3 r hr.1 hr.2 with hi | ⟨k,hk⟩ | hq
  · exact KroneckerThreeIrrationalFrameJoint.three_irrational_frame_joint r hi hr
  · subst r
    have hk1 : 1 < k := by exact_mod_cast hr.1
    have hk2 : k < 2 := by exact_mod_cast hr.2
    omega
  · exact ⟨_,KroneckerRationalEntropy.rate_joint 3 (by omega) r hq⟩

end KroneckerThreeInteriorExistence
end

/- Original module: KroneckerThreeEntropy -/
section
/-! A canonical three-arrow entropy on the full open binary slope interval. -/
set_option autoImplicit false
namespace KroneckerThreeEntropy
open KroneckerLogic KroneckerFrameObservables

def interior : Set ℝ := Set.Ioo 1 2

noncomputable def entropy (r : ℝ) : ℝ := by
  classical
  exact if h : r ∈ interior then Classical.choose (KroneckerThreeInteriorExistence.three_interior_limit_exists r h) else 0

theorem entropy_joint (r : ℝ) (hr : r ∈ interior) : JointLimit height slope (value 3) r (entropy r) := by
  rw [entropy,dite_eq_left hr]
  exact Classical.choose_spec (KroneckerThreeInteriorExistence.three_interior_limit_exists r hr)

end KroneckerThreeEntropy
end

/- Original module: KroneckerThreeEntropyContinuity -/
section
/-! The canonical three-arrow entropy is continuous throughout the open binary slope interval. -/
set_option autoImplicit false
namespace KroneckerThreeEntropyContinuity
open KroneckerThreeEntropy KroneckerFrameObservables

theorem entropy_continuousOn : ContinuousOn entropy interior :=
  KroneckerLogic.continuousOn_of_jointLimits height slope (value 3)
    entropy_joint (fun r hr => frame_approximable r hr.1)

theorem entropy_continuousAt (r : ℝ) (hr : r ∈ interior) : ContinuousAt entropy r :=
  (entropy_continuousOn r hr).continuousAt (isOpen_Ioo.mem_nhds hr)

end KroneckerThreeEntropyContinuity
end

/- Original module: KroneckerThreeEntropySequences -/
section
/-! The joint three-arrow entropy controls every approaching literal frame sequence. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerThreeEntropySequences
open KroneckerThreeEntropy KroneckerFrameObservables KroneckerLogic

theorem three_frame_sequence (r : ℝ) (hr : r ∈ interior) (x : ℕ → FramePoint)
    (ha : Tendsto (fun n => (x n).a) atTop atTop)
    (hs : Tendsto (fun n => slope (x n)) atTop (𝓝 r)) :
    Tendsto (fun n => value 3 (x n)) atTop (𝓝 (entropy r)) :=
  jointLimit_sequence height slope (value 3) (entropy_joint r hr) x ha hs

end KroneckerThreeEntropySequences
end
end

