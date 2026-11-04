import KroneckerMechanicalSlices
import KroneckerBadWindowBounds
import KroneckerFrameSlopeLimit

/- Original module: KroneckerFiniteWindows -/
section
/-! Full windows in finite literal run words and their mechanical counterpart. -/
set_option autoImplicit false
namespace KroneckerFiniteWindows
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalSlices
open KroneckerMechanicalWindows KroneckerWindowDiscrepancy
open KroneckerBadWindowCount KroneckerBadWindowBounds

def wordWindowSum (X : List ℕ) (i q : ℕ) : ℤ := (((X.drop i).take q).sum : ℤ)

def badWordWindows (X : List ℕ) (p : ℤ) (q : ℕ) : ℕ :=
  ((Finset.range (X.length+1-q)).filter (fun i => wordWindowSum X i q ≠ p)).card

theorem wordWindowSum_mechanical (s u : ℝ) (start n i q : ℕ)
    (h : i+q ≤ n) (hs : 0 ≤ s) :
    wordWindowSum (mechanicalWord s u start n) i q = windowSum s u q (start+i) := by
  rw [wordWindowSum, mechanical_slice_sum s u start n i q h hs]
  exact (mechanical_block_sum s u (start+i) q).symm

theorem badWordWindows_mechanical (s u : ℝ) (n : ℕ) (p : ℤ) (q : ℕ) (hs : 0 ≤ s) :
    badWordWindows (mechanicalWord s u 0 n) p q = badWindows s u p q (n+1-q) := by
  unfold badWordWindows badWindows nonzeroCount
  rw [mechanicalWord_length]
  congr 1
  apply Finset.filter_congr
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [wordWindowSum_mechanical s u 0 n i q (by omega) hs]
  simp [discrepancy, sub_eq_zero]

end KroneckerFiniteWindows
end

/- Original module: KroneckerAppendedWindows -/
section
/-! Appending a run preserves every full window already in the word. -/
set_option autoImplicit false
namespace KroneckerAppendedWindows
open KroneckerFiniteWindows

theorem wordWindowSum_append (X Y : List ℕ) (i q : ℕ) (h : i+q ≤ X.length) :
    wordWindowSum (X++Y) i q = wordWindowSum X i q := by
  unfold wordWindowSum
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem old_bad_windows_preserved (X : List ℕ) (r : ℕ) (p : ℤ) (q : ℕ) :
    (Finset.range (X.length+1-q)).filter (fun i => wordWindowSum (X++[r]) i q ≠ p) =
    (Finset.range (X.length+1-q)).filter (fun i => wordWindowSum X i q ≠ p) := by
  apply Finset.filter_congr
  intro i hi
  rw [wordWindowSum_append X [r] i q (by have := Finset.mem_range.mp hi; omega)]

end KroneckerAppendedWindows
end

/- Original module: KroneckerAppendedBadCount -/
section
/-! Appending one run increases the number of bad full windows by at most one. -/
set_option autoImplicit false
namespace KroneckerAppendedBadCount
open KroneckerFiniteWindows KroneckerAppendedWindows

theorem filtered_range_step (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((Finset.range (N+1)).filter P).card ≤ ((Finset.range N).filter P).card+1 := by
  by_cases h : P N
  · simp only [Finset.range_add_one, Finset.filter_insert, h, ite_true]
    exact Finset.card_insert_le _ _
  · simp only [Finset.range_add_one, Finset.filter_insert, h, ite_false]
    omega

theorem badWordWindows_append_one (X : List ℕ) (r : ℕ) (p : ℤ) (q : ℕ) :
    badWordWindows (X++[r]) p q ≤ badWordWindows X p q+1 := by
  by_cases hq : q ≤ X.length+1
  · have hlen : (X++[r]).length+1-q = (X.length+1-q)+1 := by
      simp only [List.length_append, List.length_singleton]
      omega
    unfold badWordWindows
    rw [hlen]
    have h := filtered_range_step (fun i => wordWindowSum (X++[r]) i q ≠ p) (X.length+1-q)
    rw [old_bad_windows_preserved] at h
    exact h
  · have hlen : (X++[r]).length+1-q = 0 := by
      simp only [List.length_append, List.length_singleton]
      omega
    unfold badWordWindows
    rw [hlen]
    simp

end KroneckerAppendedBadCount
end

/- Original module: KroneckerBadWindowAbsolute -/
section
/-! A uniform finite bad-window estimate in terms of slope discrepancy. -/
set_option autoImplicit false
namespace KroneckerBadWindowAbsolute
open KroneckerBadWindowBounds

theorem bad_windows_absolute (s u : ℝ) (p : ℤ) (q N : ℕ)
    (hclose : |(q : ℝ)*s-(p : ℝ)| ≤ 1) :
    (badWindows s u p q N : ℝ) ≤ (N : ℝ)*|(q : ℝ)*s-(p : ℝ)|+(q : ℝ) := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hclose
  by_cases hside : (p : ℝ) ≤ (q : ℝ)*s
  · rw [abs_of_nonneg (sub_nonneg.mpr hside)]
    exact bad_windows_above s u p q N hside (by linarith)
  · rw [abs_of_nonpos (by linarith : (q : ℝ)*s-(p : ℝ) ≤ 0)]
    have h := bad_windows_below s u p q N (by linarith) (by linarith)
    simpa only [neg_sub] using h


end KroneckerBadWindowAbsolute
end

/- Original module: KroneckerBadWindowDensity -/
section
/-! Mechanical bad windows have zero asymptotic density at a fixed rational
slope, uniformly in the intercept. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerBadWindowDensity
open KroneckerBadWindowBounds KroneckerBadWindowAbsolute

theorem bad_window_density (s u : ℕ → ℝ) (a N : ℕ → ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (ha : Tendsto a atTop atTop) (hs : Tendsto s atTop (𝓝 ((p : ℝ)/(q : ℝ))))
    (hN : ∀ n, N n ≤ a n) :
    Tendsto (fun n => (badWindows (s n) (u n) p q (N n) : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hd : Tendsto (fun n => |(q : ℝ)*s n-(p : ℝ)|) atTop (𝓝 (0 : ℝ)) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (q : ℝ)) atTop (𝓝 (q : ℝ))).mul hs).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (p : ℝ)) atTop (𝓝 (p : ℝ)))
    have heq : (q : ℝ)*((p : ℝ)/(q : ℝ)) = (p : ℝ) := by field_simp
    simpa only [heq, sub_self, abs_zero] using h.abs
  have hqdiv : Tendsto (fun n => (q : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  have hup : Tendsto (fun n => |(q : ℝ)*s n-(p : ℝ)|+(q : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa using hd.add hqdiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall (fun n => by positivity)
  · have hnear := (tendsto_order.1 hd).2 1 (by norm_num)
    filter_upwards [hnear, ha.eventually (eventually_ge_atTop 1)] with n hn han
    have ha' : (0 : ℝ) < a n := by exact_mod_cast han
    have hN' : (N n : ℝ) ≤ (a n : ℝ) := by exact_mod_cast hN n
    have hbound := bad_windows_absolute (s n) (u n) p q (N n) hn.le
    apply (div_le_iff₀ ha').2
    have hmul := mul_le_mul_of_nonneg_right hN' (abs_nonneg ((q : ℝ)*s n-(p : ℝ)))
    have heq : (|(q : ℝ)*s n-(p : ℝ)|+(q : ℝ)/(a n : ℝ))*(a n : ℝ) =
        (a n : ℝ)*|(q : ℝ)*s n-(p : ℝ)|+(q : ℝ) := by
      field_simp
    rw [heq]
    linarith

end KroneckerBadWindowDensity
end

/- Original module: KroneckerFiniteBadDensity -/
section
/-! The bad-window density vanishes for finite mechanical words, including
one arbitrary exceptional appended run. The window length is fixed. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFiniteBadDensity
open KroneckerMechanicalWords KroneckerFiniteWindows KroneckerBadWindowDensity
open KroneckerAppendedBadCount

theorem finite_bad_window_density (s u : ℕ → ℝ) (a : ℕ → ℕ) (p : ℤ) (q : ℕ)
    (hq : 0 < q) (ha : Tendsto a atTop atTop)
    (hs : Tendsto s atTop (𝓝 ((p : ℝ)/(q : ℝ)))) (hs0 : ∀ n, 0 ≤ s n) :
    Tendsto (fun n => (badWordWindows (mechanicalWord (s n) (u n) 0 (a n)) p q : ℝ)/
      (a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have h := bad_window_density s u a (fun n => a n+1-q) p q hq ha hs (fun n => by omega)
  apply h.congr'
  exact Eventually.of_forall (fun n => by dsimp only; rw [badWordWindows_mechanical _ _ _ _ _ (hs0 n)])

theorem appended_bad_window_density (s u : ℕ → ℝ) (a v : ℕ → ℕ) (p : ℤ) (q : ℕ)
    (hq : 0 < q) (ha : Tendsto a atTop atTop)
    (hs : Tendsto s atTop (𝓝 ((p : ℝ)/(q : ℝ)))) (hs0 : ∀ n, 0 ≤ s n) :
    Tendsto (fun n => (badWordWindows (mechanicalWord (s n) (u n) 0 (a n)++[v n]) p q : ℝ)/
      (a n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hbase := finite_bad_window_density s u a p q hq ha hs hs0
  have hone : Tendsto (fun n => (1 : ℝ)/(a n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp ha)
  have hup := hbase.add hone
  simp only [zero_add] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall (fun n => by positivity)
  · apply Eventually.of_forall
    intro n
    have hb : (badWordWindows (mechanicalWord (s n) (u n) 0 (a n)++[v n]) p q : ℝ) ≤
        (badWordWindows (mechanicalWord (s n) (u n) 0 (a n)) p q : ℝ)+1 := by
      exact_mod_cast badWordWindows_append_one (mechanicalWord (s n) (u n) 0 (a n)) (v n) p q
    simpa only [add_div] using div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ a n)

end KroneckerFiniteBadDensity
end

/- Original module: KroneckerFrameBadDensity -/
section
/-! Bad full windows in the precise literal frame have sublinear count.
This is a word statement; the geometric frame identity is still separate. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace KroneckerFrameBadDensity
open KroneckerFrameSlope KroneckerFrameSlopeLimit KroneckerMechanicalWords
open KroneckerFiniteWindows KroneckerFiniteBadDensity

noncomputable def frameWord (a b d : ℕ) : List ℕ := mechanicalWord (frameSlope a b d) 0 0 a++[1]

theorem frame_bad_window_density (a b d : ℕ → ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n)
    (hd : ∀ n, 0 < d n)
    (hr : Tendsto (fun n => (b n : ℝ)/(a n : ℝ)) atTop (𝓝 ((p : ℝ)/(q : ℝ)))) :
    Tendsto (fun n => (badWordWindows (frameWord (a n) (b n) (d n)) p q : ℝ)/(a n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  exact appended_bad_window_density (fun n => frameSlope (a n) (b n) (d n)) (fun _ => 0)
    a (fun _ => 1) p q hq ha (frame_slope_limit a b d _ ha hd hr)
    (fun n => frameSlope_nonnegative (a n) (b n) (d n) (ha0 n) (hb n) (hd n))

end KroneckerFrameBadDensity
end

/- Original module: KroneckerFramePrefix -/
section
/-! The first a frame runs have exactly b-1 vertical edges. -/
set_option autoImplicit false
namespace KroneckerFramePrefix
open KroneckerFrameSlope KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem frame_prefix_floor (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    mechanicalPrefix (frameSlope a b d) 0 a = (b : ℤ)-1 := by
  unfold mechanicalPrefix
  rw [zero_add, frameSlope_mul a b d ha hd]
  apply Int.floor_eq_iff.mpr
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < 1/(d : ℝ) := by positivity
  have hle : 1/(d : ℝ) ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num) hd1
  push_cast
  constructor <;> linarith

theorem frame_mechanical_sum (a b d : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    (mechanicalWord (frameSlope a b d) 0 0 a).sum = b-1 := by
  have h := mechanicalWord_sum_cast (frameSlope a b d) 0 0 a (frameSlope_nonnegative a b d ha hb hd)
  rw [Nat.zero_add, frame_prefix_floor a b d ha hd] at h
  have hzero : mechanicalPrefix (frameSlope a b d) 0 0 = 0 := by simp [mechanicalPrefix]
  rw [hzero, sub_zero] at h
  omega

end KroneckerFramePrefix
end

/- Original module: KroneckerFrameWord -/
section
/-! Literal frame dimensions and alphabet legality. -/
set_option autoImplicit false
namespace KroneckerFrameWord
open KroneckerFrameSlope KroneckerFrameBadDensity KroneckerFramePrefix KroneckerMechanicalWords

theorem frameWord_length (a b d : ℕ) : (frameWord a b d).length = a+1 := by
  simp [frameWord, mechanicalWord_length]

theorem frameWord_sum (a b d : ℕ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    (frameWord a b d).sum = b := by
  simp only [frameWord, List.sum_append, List.sum_singleton, frame_mechanical_sum a b d ha hb hd]
  omega

theorem frameWord_legal (a b d M : ℕ) (hs : 1 ≤ frameSlope a b d) (hM : frameSlope a b d ≤ M) :
    ∀ r ∈ frameWord a b d, 1 ≤ r ∧ r ≤ M := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact mechanicalWord_legal _ _ _ _ _ hs hM r hr
  · simp only [List.mem_singleton] at hr
    subst r
    have h : (1 : ℝ) ≤ M := le_trans hs hM
    exact ⟨le_rfl, by exact_mod_cast h⟩

end KroneckerFrameWord
end
