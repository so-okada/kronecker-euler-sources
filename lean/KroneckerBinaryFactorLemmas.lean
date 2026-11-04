import KroneckerGeometricBinaryPrograms

/-! Lemmas 9.10 and 9.11: complete mechanical factors and the exceptional
last simple run. RawBinary records the actual insertions and exchanges. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KroneckerBinaryFactorLemmas
open KroneckerMechanicalWords KroneckerRawBinaryEdits
open KroneckerMechanicalLetterBounds KroneckerNormalizedWindow

def margin (r : ℝ) : ℝ := min (r - 1) (2 - r) / 2
def padding (r : ℝ) : ℕ := ⌈4 / margin r⌉₊

theorem margin_pos {r : ℝ} (hr : 1 < r ∧ r < 2) : 0 < margin r := by
  exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)

theorem padding_budget {r : ℝ} (hr : 1 < r ∧ r < 2) :
    4 ≤ (padding r : ℝ) * margin r := by
  have h := mul_le_mul_of_nonneg_right (Nat.le_ceil (4 / margin r)) (margin_pos hr).le
  simpa [padding, div_mul_cancel₀ _ (ne_of_gt (margin_pos hr))] using h

theorem nearby_margins {r s δ : ℝ} (hδ : δ < margin r) (hs : |s-r| < δ) :
    1 + margin r < s ∧ s < 2 - margin r := by
  have h1 : 2 * margin r ≤ r - 1 := by
    dsimp [margin]
    linarith [min_le_left (r-1) (2-r)]
  have h2 : 2 * margin r ≤ 2 - r := by
    dsimp [margin]
    linarith [min_le_right (r-1) (2-r)]
  obtain ⟨hl, hu⟩ := abs_lt.mp hs
  constructor <;> linarith

theorem mechanical_factor_comparison (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) (hη4 : η < 1/4) :
    ∃ L : ℕ, 0 < L ∧ ∃ δ : ℝ, 0 < δ ∧
      (padding r : ℝ) ≤ η * L ∧ δ < min (margin r) (η / (4 * L)) ∧
      ∀ s t u v : ℝ, |s-r| < δ → |t-r| < δ →
      (0 ≤ u ∧ u < 1) → (0 ≤ v ∧ v < 1) → ∀ p : ℕ,
      ∃ j k : ℕ, ((padding r + j : ℕ) : ℝ) ≤ η * L ∧
        Nonempty (RawBinary (mechanicalWord s u 0 L)
          (mechanicalWord t v p (L + padding r + j)) (padding r + j) k) ∧
        (k : ℝ) ≤ 7 * η * L := by
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / η)
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := (div_pos (by norm_num) hη).trans hq
    exact_mod_cast this
  have hqη : 1 ≤ η * q := by
    have := (div_lt_iff₀ hη).mp hq
    nlinarith
  obtain ⟨Q, hQ, hall⟩ :=
    KroneckerUniformBinaryPrefixBlock.uniform_binary_prefix_block r hr q hq0
  let C := padding r
  obtain ⟨L, hL⟩ := exists_nat_gt (((Q : ℝ) + C + 1 + (C : ℝ)^2) / η + 1)
  have hL0r : (0 : ℝ) < L := by
    have : 0 ≤ ((Q : ℝ) + C + 1 + (C : ℝ)^2) / η := by positivity
    linarith
  have hL0 : 0 < L := by exact_mod_cast hL0r
  have hscale : (Q : ℝ) + C + 1 + (C : ℝ)^2 < η * L := by
    have hh : ((Q : ℝ) + C + 1 + (C : ℝ)^2) / η < (L : ℝ) := by linarith
    have := (div_lt_iff₀ hη).mp hh
    nlinarith
  have hQC : (Q : ℝ) + C ≤ η * L := by nlinarith [sq_nonneg (C : ℝ)]
  have hC2 : 1 + (C : ℝ)^2 ≤ η * L := by nlinarith
  obtain ⟨d, hd, hblock⟩ := hall L
  let δ := min d (min (margin r) (η / (4 * L))) / 2
  have hm := margin_pos hrb
  have hδ : 0 < δ := by
    exact div_pos (lt_min hd (lt_min hm (by positivity))) (by norm_num)
  have hδd : δ < d := by
    have := min_le_left d (min (margin r) (η / (4 * L)))
    dsimp [δ] at hδ ⊢
    linarith
  have hδm : δ < min (margin r) (η / (4 * L)) := by
    have := min_le_right d (min (margin r) (η / (4 * L)))
    dsimp [δ] at hδ ⊢
    linarith
  refine ⟨L, hL0, δ, hδ, by dsimp [C] at hQC; linarith, hδm, ?_⟩
  intro s t u v hs ht hu hv p
  have hsm := nearby_margins (hδm.trans_le (min_le_left _ _)) hs
  have htm := nearby_margins (hδm.trans_le (min_le_left _ _)) ht
  have hsb : 1 ≤ s ∧ s ≤ 2 := ⟨by linarith, by linarith⟩
  have htb : 1 ≤ t ∧ t ≤ 2 := ⟨by linarith, by linarith⟩
  have hfreq : ∀ b : Bool, margin r ≤ frequency t b := by
    intro b
    cases b <;> simp only [frequency, Bool.false_eq_true, ↓reduceIte] <;> linarith [htm.1, htm.2]
  have hst : |s-t| ≤ 2 * δ := by
    have := abs_sub_le s r t
    rw [abs_sub_comm r t] at this
    linarith
  have hδL : δ * (4 * L) < η :=
    (lt_div_iff₀ (by positivity)).mp (hδm.trans_le (min_le_right _ _))
  have hbudget : 2 + (L : ℝ) * (2 * δ) ≤ (C : ℝ) * margin r := by
    have := padding_budget hrb
    dsimp [C]
    nlinarith
  let w := Int.fract (v + (p : ℝ) * t)
  obtain ⟨j, hj, k, hp, hk⟩ := hblock s t u w (margin r) (2 * δ)
    (hs.trans hδd) (ht.trans hδd) hsb htb hu
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩ hfreq hst L le_rfl C hbudget
  have hjr : (j : ℝ) < Q := by exact_mod_cast hj
  have hinsert : ((C + j : ℕ) : ℝ) ≤ η * L := by push_cast; linarith
  have hdiv : (((L / q : ℕ) : ℝ) * q) ≤ L := by
    exact_mod_cast Nat.div_mul_le_self L q
  have hdiv0 : (0 : ℝ) ≤ (L / q : ℕ) := by positivity
  have hdivη : ((L / q : ℕ) : ℝ) ≤ η * L := by
    have h1 := mul_le_mul_of_nonneg_left hdiv hη.le
    have h2 := mul_le_mul_of_nonneg_left hqη hdiv0
    nlinarith
  have hkr : (k : ℝ) ≤ (L / q : ℕ) + 1 + (C : ℝ)^2 := by exact_mod_cast hk
  refine ⟨j, k, hinsert, ?_, ?_⟩
  · dsimp only [w] at hp
    rw [← normalized_window t v p (j+L+C)] at hp
    simpa only [C, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hp
  · nlinarith only [hkr, hC2, hdivη, mul_pos hη hL0r]

theorem exceptional_final_factor (s u t v : ℝ) (a C p z : ℕ)
    (ha : 0 < a) (hs : 1 < s ∧ s < 2) (ht : 1 < t ∧ t < 2)
    (hz : z = 1 ∨ z = 2)
    (hbudget : 3 + (a : ℝ) * |s-t| < (C : ℝ) * min (t-1) (2-t)) :
    ∃ k, Nonempty (RawBinary (mechanicalWord s u 0 (a-1) ++ [z])
      (mechanicalWord t v p (a+C)) C k) ∧ k ≤ (a+C)^2 := by
  have hmargin : ∀ b : Bool, min (t-1) (2-t) ≤ frequency t b := by
    intro b
    cases b
    · exact min_le_right _ _
    · exact min_le_left _ _
  have hn : a - 1 + 1 = a := by omega
  rcases hz with rfl | rfl
  · simpa only [hn, Bool.false_eq_true, ↓reduceIte] using
      KroneckerShiftedBinaryTerminal.shifted_terminal_edits s u t v
        (min (t-1) (2-t)) |s-t| 0 p (a-1) C false
        ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hmargin le_rfl
        (by simpa only [hn] using hbudget.le)
  · simpa only [hn, ↓reduceIte] using
      KroneckerShiftedBinaryTerminal.shifted_terminal_edits s u t v
        (min (t-1) (2-t)) |s-t| 0 p (a-1) C true
        ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hmargin le_rfl
        (by simpa only [hn] using hbudget.le)

open KroneckerPaperPaths

theorem mechanical_factor_paths (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) (hη4 : η < 1/4) :
    ∃ L : ℕ, 0 < L ∧ ∃ δ : ℝ, 0 < δ ∧
      (padding r : ℝ) ≤ η * L ∧ δ < min (margin r) (η / (4 * L)) ∧
      ∀ s t u v : ℝ, |s-r| < δ → |t-r| < δ →
      (0 ≤ u ∧ u < 1) → (0 ≤ v ∧ v < 1) → ∀ p : ℕ, ∀ o : LatticePoint,
      ∃ j k : ℕ, ((padding r + j : ℕ) : ℝ) ≤ η * L ∧
        (∃ w : LatticePoint, Nonempty (BinaryProgram
          (runPath (mechanicalWord s u 0 L) o)
          (translate (runPath (mechanicalWord t v p (L + padding r + j)) 0) w)
          (padding r + j) k)) ∧ (k : ℝ) ≤ 7 * η * L := by
  obtain ⟨L, hL, δ, hδ, hC, hd, h⟩ := mechanical_factor_comparison r η hr hrb hη hη4
  refine ⟨L, hL, δ, hδ, hC, hd, ?_⟩
  intro s t u v hs ht hu hv p o
  obtain ⟨j, k, hj, ⟨prog⟩, hk⟩ := h s t u v hs ht hu hv p
  exact ⟨j, k, hj, rawBinary_translated_target prog o, hk⟩

theorem exceptional_final_paths (s u t v : ℝ) (a C p z : ℕ)
    (ha : 0 < a) (hs : 1 < s ∧ s < 2) (ht : 1 < t ∧ t < 2)
    (hz : z = 1 ∨ z = 2)
    (hbudget : 3 + (a : ℝ) * |s-t| < (C : ℝ) * min (t-1) (2-t)) (o : LatticePoint) :
    ∃ k, (∃ w : LatticePoint, Nonempty (BinaryProgram
      (runPath (mechanicalWord s u 0 (a-1) ++ [z]) o)
      (translate (runPath (mechanicalWord t v p (a+C)) 0) w) C k)) ∧ k ≤ (a+C)^2 := by
  obtain ⟨k, ⟨prog⟩, hk⟩ := exceptional_final_factor s u t v a C p z ha hs ht hz hbudget
  exact ⟨k, rawBinary_translated_target prog o, hk⟩

end KroneckerBinaryFactorLemmas
