import Mathlib

/-! Lemma 6.3: gaps and counts for fractional parts near a rational slope. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerFractionalPartEstimates

def latticeIndex (p q : ℕ) (σ w : ℝ) (j : ℕ) : ℤ :=
  (j : ℤ)*p-(q : ℤ)*⌊w+(j : ℝ)*σ⌋

theorem grid_error (p q j : ℕ) (σ w : ℝ) (hq : 0<q) (hj : j<q)
    (hσ : |σ-(p : ℝ)/q|<2/(q : ℝ)^2) :
    |Int.fract (w+(j : ℝ)*σ)-(w+(latticeIndex p q σ w j : ℝ)/q)|<2/(q : ℝ) := by
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hjR : (j : ℝ)<q := by exact_mod_cast hj
  have hq0 : (q : ℝ)≠0 := ne_of_gt hqR
  have hid : Int.fract (w+(j : ℝ)*σ)-(w+(latticeIndex p q σ w j : ℝ)/q)=
      (j : ℝ)*(σ-(p : ℝ)/q) := by
    simp only [Int.fract, latticeIndex, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
  have hden : (0 : ℝ)<2/(q : ℝ)^2 := by positivity
  calc
    (j : ℝ)*|σ-(p : ℝ)/q|  ≤  (j : ℝ)*(2/(q : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hσ.le (Nat.cast_nonneg j)
    _ < (q : ℝ)*(2/(q : ℝ)^2) := mul_lt_mul_of_pos_right hjR hden
    _ = 2/(q : ℝ) := by field_simp

theorem latticeIndex_injective (p q : ℕ) (σ w : ℝ) (hpq : p.Coprime q) :
    Set.InjOn (latticeIndex p q σ w) (Set.Iio q) := by
  intro i hi j hj hij
  have hm : (i : ZMod q)*(p : ZMod q)=(j : ZMod q)*(p : ZMod q) := by
    have h := congrArg (fun z : ℤ => (z : ZMod q)) hij
    simpa [latticeIndex] using h
  have hc := congrArg (fun z : ZMod q => z*(p : ZMod q)⁻¹) hm
  have he : (i : ZMod q)=(j : ZMod q) := by
    simpa only [mul_assoc, ZMod.coe_mul_inv_eq_one p hpq, mul_one] using hc
  have h := (ZMod.natCast_eq_natCast_iff' i j q).mp he
  simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using h

theorem grid_approximated (p q : ℕ) (σ w : ℝ) (hq : 0<q)
    (hpq : p.Coprime q) (hσ : |σ-(p : ℝ)/q|<2/(q : ℝ)^2) (t : ℤ) :
    ∃ j : ℕ, j<q ∧ ∃ n : ℤ,
      |(Int.fract (w+(j : ℝ)*σ)+(n : ℝ))-(w+(t : ℝ)/q)|<2/(q : ℝ) := by
  haveI : NeZero q := ⟨by omega⟩
  let z : ZMod q := (t : ZMod q)*(p : ZMod q)⁻¹
  let j : ℕ := z.val
  have hj : j<q := ZMod.val_lt z
  have hjmod : (j : ZMod q)*(p : ZMod q)=(t : ZMod q) := by
    dsimp [j,z]
    rw [ZMod.natCast_zmod_val]
    calc
      (t : ZMod q)*(p : ZMod q)⁻¹*(p : ZMod q) =
          (t : ZMod q)*((p : ZMod q)*(p : ZMod q)⁻¹) := by ring
      _ = (t : ZMod q) := by rw [ZMod.coe_mul_inv_eq_one p hpq, mul_one]
  have hm : (latticeIndex p q σ w j : ZMod q)=(t : ZMod q) := by
    simpa [latticeIndex] using hjmod
  obtain ⟨n,hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (latticeIndex p q σ w j) t q).mp hm
  have ht : t=latticeIndex p q σ w j+n*q := by nlinarith
  refine ⟨j,hj,n,?_⟩
  have hid : (Int.fract (w+(j : ℝ)*σ)+(n : ℝ))-(w+(t : ℝ)/q)=
      Int.fract (w+(j : ℝ)*σ)-(w+(latticeIndex p q σ w j : ℝ)/q) := by
    rw [ht]
    push_cast
    field_simp
    ring
  rw [hid]
  exact grid_error p q j σ w hq hj hσ

theorem grid_between (q : ℕ) (hq : 0<q) (w a b : ℝ)
    (hab : a+1/(q : ℝ)<b) :
    ∃ t : ℤ, a<w+(t : ℝ)/q ∧ w+(t : ℝ)/q<b := by
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hq0 : (q : ℝ)≠0 := ne_of_gt hqR
  let t : ℤ := ⌊(q : ℝ)*(a-w)⌋+1
  have htlow : (q : ℝ)*(a-w)<t := by
    dsimp [t]; push_cast; exact Int.lt_floor_add_one _
  have hthigh : (t : ℝ) ≤ (q : ℝ)*(a-w)+1 := by
    dsimp [t]; push_cast; linarith [Int.floor_le ((q : ℝ)*(a-w))]
  have hc := div_mul_cancel₀ (t : ℝ) hq0
  have hunit := one_div_mul_cancel hq0
  refine ⟨t,?_,?_⟩
  · apply (mul_lt_mul_iff_left₀ hqR).mp
    nlinarith
  · have hle : w+(t : ℝ)/q  ≤  a+1/(q : ℝ) := by
      apply (mul_le_mul_iff_left₀ hqR).mp
      nlinarith
    exact hle.trans_lt hab

theorem empty_gap_bound (p q : ℕ) (σ w a b : ℝ) (hq : 0<q)
    (hpq : p.Coprime q) (hσ : |σ-(p : ℝ)/q|<2/(q : ℝ)^2)
    (hgap : ∀ j : ℕ, j<q → ∀ n : ℤ,
      ¬(a<Int.fract (w+(j : ℝ)*σ)+(n : ℝ) ∧ Int.fract (w+(j : ℝ)*σ)+(n : ℝ)<b)) :
    b-a ≤ 5/(q : ℝ) := by
  by_contra hn
  have hwide : (a+2/(q : ℝ))+1/(q : ℝ)<b-2/(q : ℝ) := by
    simp only [div_eq_mul_inv] at hn ⊢
    linarith
  obtain ⟨t,hta,htb⟩ := grid_between q hq w (a+2/(q : ℝ)) (b-2/(q : ℝ)) hwide
  obtain ⟨j,hj,n,he⟩ := grid_approximated p q σ w hq hpq hσ t
  have he' := abs_lt.mp he
  exact hgap j hj n ⟨by linarith,by linarith⟩

theorem int_interval_card (a b : ℝ) (hab : a ≤ b) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ b-a+1 := by
  by_cases h : (⌈a⌉ : ℤ) ≤ ⌊b⌋
  · have hc : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ)=(⌊b⌋ : ℝ)+1-(⌈a⌉ : ℝ) := by
      exact_mod_cast (Int.card_Icc_of_le ⌈a⌉ ⌊b⌋ (by omega : (⌈a⌉ : ℤ) ≤ ⌊b⌋+1))
    rw [hc]
    linarith [Int.le_ceil a,Int.floor_le b]
  · have hz : Finset.Icc (⌈a⌉ : ℤ) ⌊b⌋=∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hz];simp only [Finset.card_empty,Nat.cast_zero]
    linarith

theorem interval_count (p q : ℕ) (σ w a b : ℝ) (hq : 0<q)
    (hpq : p.Coprime q) (hσ : |σ-(p : ℝ)/q|<2/(q : ℝ)^2) (hab : a ≤ b) :
    (((Finset.range q).filter (fun (j : ℕ) => a ≤ Int.fract (w+(j : ℝ)*σ) ∧
      Int.fract (w+(j : ℝ)*σ) ≤ b)).card : ℝ)  ≤  (b-a)*q+5 := by
  classical
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hq0 : (q : ℝ)≠0 := ne_of_gt hqR
  let s := (Finset.range q).filter (fun (j : ℕ) => a ≤ Int.fract (w+(j : ℝ)*σ) ∧
      Int.fract (w+(j : ℝ)*σ) ≤ b)
  let A := (q : ℝ)*(a-w)-2
  let B := (q : ℝ)*(b-w)+2
  have hinj : Set.InjOn (latticeIndex p q σ w) (s : Set ℕ) := by
    intro i hi j hj he
    exact latticeIndex_injective p q σ w hpq
      (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) he
  have hsub : s.image (latticeIndex p q σ w)⊆Finset.Icc ⌈A⌉ ⌊B⌋ := by
    intro t ht
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hjrange,hja,hjb⟩ := Finset.mem_filter.mp hj
    have he := abs_lt.mp (grid_error p q j σ w hq (Finset.mem_range.mp hjrange) hσ)
    have hc := div_mul_cancel₀ (latticeIndex p q σ w j : ℝ) hq0
    have htwo := div_mul_cancel₀ (2 : ℝ) hq0
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.ceil_le.mpr
      dsimp [A]
      have hh := (mul_lt_mul_iff_left₀ hqR).mpr he.2
      nlinarith
    · apply Int.le_floor.mpr
      dsimp [B]
      have hh := (mul_lt_mul_iff_left₀ hqR).mpr he.1
      nlinarith
  have hcard : (s.card : ℝ) ≤ (Finset.Icc ⌈A⌉ ⌊B⌋).card := by
    rw [← Finset.card_image_iff.mpr hinj]
    exact_mod_cast Finset.card_le_card hsub
  have hAB : A ≤ B := by dsimp [A,B];nlinarith
  have hbound := int_interval_card A B hAB
  change (s.card : ℝ) ≤ _
  dsimp [A,B] at hbound
  nlinarith

/-- Claim 1 of Lemma 6.3. The ordered list covers every fractional part;
the hypotheses also allow repeated fractional parts. Indices are one-based. -/
theorem ordered_gaps (p q : ℕ) (σ w : ℝ) (hq : 0<q)
    (hpq : p.Coprime q) (hσ : |σ-(p : ℝ)/q|<2/(q : ℝ)^2)
    (x : ℕ → ℝ)
    (hx : ∀ i : ℕ, 1 ≤ i → i ≤ q → 0 ≤ x i ∧ x i<1)
    (hmono : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ q → x i ≤ x j)
    (hcover : ∀ j : ℕ, j<q → ∃ k : ℕ, 1 ≤ k ∧ k ≤ q ∧ x k=Int.fract (w+(j : ℝ)*σ))
    (hwrap : x (q+1)=x 1+1) :
    ∀ i : ℕ, 1 ≤ i → i ≤ q → x (i+1)-x i ≤ 5/(q : ℝ) := by
  intro i hi hiq
  apply empty_gap_bound p q σ w (x i) (x (i+1)) hq hpq hσ
  intro j hj n hn
  obtain ⟨k,hk,hkq,hkv⟩ := hcover j hj
  have hz := Int.fract_nonneg (w+(j : ℝ)*σ)
  have hz1 := Int.fract_lt_one (w+(j : ℝ)*σ)
  by_cases hil : i<q
  · have hxi := hx i hi hiq
    have hxn := hx (i+1) (by omega) (by omega)
    have hn0 : n=0 := by
      by_contra hne
      have hcases : n ≤ -1 ∨ 1 ≤ n := by omega
      rcases hcases with hneg|hpos
      · have hnR : (n : ℝ) ≤ -1 := by exact_mod_cast hneg
        linarith [hn.1]
      · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hpos
        linarith [hn.2]
    subst n
    simp only [Int.cast_zero,add_zero] at hn
    by_cases hki : k ≤ i
    · have hle := hmono k i hk hki hiq
      linarith [hn.1]
    · have hle := hmono (i+1) k (by omega) (by omega) hkq
      linarith [hn.2]
  · have hie : i=q := by omega
    subst i
    rw [hwrap] at hn
    have hlo := hmono 1 k (by omega) hk hkq
    have hhi := hmono k q hk hkq (le_refl q)
    by_cases hnle : n ≤ 0
    · have hnR : (n : ℝ) ≤ 0 := by exact_mod_cast hnle
      linarith [hn.1]
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith [hn.2]

def nearIntegerIndices (q : ℕ) (σ w η : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range q).filter (fun (j : ℕ) =>
    (0 ≤ Int.fract (w+(j : ℝ)*σ) ∧ Int.fract (w+(j : ℝ)*σ) ≤ 2*η) ∨
    (1-2*η ≤ Int.fract (w+(j : ℝ)*σ) ∧ Int.fract (w+(j : ℝ)*σ)<1))

/-- Claim 2 of Lemma 6.3; the estimate holds for every eta >= 0. -/
theorem near_integer_count (p q : ℕ) (σ w η : ℝ) (hq : 0<q)
    (hpq : p.Coprime q) (hσ : |σ-(p : ℝ)/q|<2/(q : ℝ)^2) (hη : 0 ≤ η) :
    ((nearIntegerIndices q σ w η).card : ℝ) ≤ 4*η*q+10 := by
  classical
  let s := nearIntegerIndices q σ w η
  let s₁ := (Finset.range q).filter (fun (j : ℕ) =>
    0 ≤ Int.fract (w+(j : ℝ)*σ) ∧ Int.fract (w+(j : ℝ)*σ) ≤ 2*η)
  let s₂ := (Finset.range q).filter (fun (j : ℕ) =>
    1-2*η ≤ Int.fract (w+(j : ℝ)*σ) ∧ Int.fract (w+(j : ℝ)*σ) ≤ 1)
  have hsub : s⊆s₁∪s₂ := by
    intro j hj
    obtain ⟨hjq,hj₁|hj₂⟩ := Finset.mem_filter.mp hj
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjq,hj₁⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjq,hj₂.1,hj₂.2.le⟩)
  have hcard : (s.card : ℝ) ≤ (s₁.card : ℝ)+(s₂.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le s₁ s₂)
  have h₁ := interval_count p q σ w 0 (2*η) hq hpq hσ (by linarith)
  have h₂ := interval_count p q σ w (1-2*η) 1 hq hpq hσ (by linarith)
  change (s₁.card : ℝ) ≤ _ at h₁
  change (s₂.card : ℝ) ≤ _ at h₂
  change (s.card : ℝ) ≤ _
  nlinarith

end KroneckerFractionalPartEstimates
