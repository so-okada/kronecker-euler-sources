import Mathlib.Data.Int.GCD
import KroneckerMechanicalWordShift
import Mathlib.Data.Nat.ModEq
import KroneckerRationalPeriodAlphabet
import KroneckerMechanicalSlices

section

/- Original module: KroneckerCoprimeIndexGap -/
section
/-! Coprimeness excludes equality at the integer boundary of a prefix gap. -/
set_option autoImplicit false
namespace KroneckerCoprimeIndexGap

theorem index_sub_dvd_implies_eq (q i j : ℕ) (hi : i < q) (hj : j < q)
    (hdiv : (q : ℤ) ∣ (i : ℤ)-(j : ℤ)) : i=j := by
  have hmod := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdiv)
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hj)] at hmod
  exact_mod_cast hmod

theorem coprime_cancel_indices (p q i j : ℕ) (hc : p.Coprime q)
    (hi : i < q) (hj : j < q)
    (hdiv : (q : ℤ) ∣ ((i : ℤ)-(j : ℤ))*(p : ℤ)) : i=j := by
  have hg : Int.gcd (q : ℤ) (p : ℤ)=1 := by simpa using hc.symm
  exact index_sub_dvd_implies_eq q i j hi hj
    (Int.dvd_of_dvd_mul_left_of_gcd_one hdiv hg)

theorem scaled_gap_ne_modulus (p q i j : ℕ) (hc : p.Coprime q)
    (hi : i < q) (hj : j < q) (hne : i ≠ j) (x y : ℤ) :
    (q : ℤ)*(x-y)-((i : ℤ)-(j : ℤ))*(p : ℤ) ≠ (q : ℤ) := by
  intro heq
  apply hne
  apply coprime_cancel_indices p q i j hc hi hj
  refine ⟨x-y-1, ?_⟩
  nlinarith

end KroneckerCoprimeIndexGap
end

/- Original module: KroneckerPrefixWordEquality -/
section
/-! Prefix values determine the mechanical word, including its final run. -/
set_option autoImplicit false
namespace KroneckerPrefixWordEquality
open KroneckerMechanicalRuns KroneckerMechanicalWords

theorem run_eq_of_prefix_offset (s u t v : ℝ) (i : ℕ) (z : ℤ)
    (h₀ : mechanicalPrefix s u i = mechanicalPrefix t v i+z)
    (h₁ : mechanicalPrefix s u (i+1) = mechanicalPrefix t v (i+1)+z) :
    mechanicalRun s u i = mechanicalRun t v i := by
  unfold mechanicalRun
  rw [h₀,h₁]
  ring

theorem word_eq_of_prefix_offset (s u t v : ℝ) (n : ℕ) (z : ℤ)
    (h : ∀ i ≤ n, mechanicalPrefix s u i = mechanicalPrefix t v i+z) :
    mechanicalWord s u 0 n = mechanicalWord t v 0 n := by
  apply List.ext_getElem
  · simp [mechanicalWord_length]
  · intro i hi hi'
    have hin : i < n := by simpa [mechanicalWord_length] using hi
    have hr := run_eq_of_prefix_offset s u t v i z (h i (by omega)) (h (i+1) (by omega))
    simpa [mechanicalWord,natRun] using congrArg Int.toNat hr

end KroneckerPrefixWordEquality
end

/- Original module: KroneckerPhasePerturbation -/
section
/-! Uniform perturbation bound for every pair of indices in one rational period. -/
set_option autoImplicit false
namespace KroneckerPhasePerturbation

theorem index_distance_lt (q i j : ℕ) (hi : i < q) (hj : j < q) :
    |(i : ℝ)-(j : ℝ)| < (q : ℝ) := by
  have hi' : (i : ℝ) < (q : ℝ) := by exact_mod_cast hi
  have hj' : (j : ℝ) < (q : ℝ) := by exact_mod_cast hj
  have hi0 : (0 : ℝ) ≤ i := by positivity
  have hj0 : (0 : ℝ) ≤ j := by positivity
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem scaled_error_lt_one (Q d e : ℝ) (hQ : 0 < Q) (hd : |d| ≤ Q)
    (he : |e| < 1/Q^2) : |Q*d*e| < 1 := by
  have hsq : 0 < Q^2 := sq_pos_of_pos hQ
  have he' : |e| * Q^2 < 1 := (lt_div_iff₀ hsq).mp he
  have hprod : 0 ≤ Q*(Q-|d|)*|e| :=
    mul_nonneg (mul_nonneg hQ.le (sub_nonneg.mpr hd)) (abs_nonneg e)
  rw [abs_mul, abs_mul, abs_of_pos hQ]
  nlinarith

theorem index_slope_error (q i j : ℕ) (hq : 0 < q) (hi : i < q) (hj : j < q)
    (s r : ℝ) (hs : |s-r| < 1/(q : ℝ)^2) :
    |(q : ℝ)*((i : ℝ)-(j : ℝ))*(s-r)| < 1 := by
  exact scaled_error_lt_one q ((i : ℝ)-(j : ℝ)) (s-r)
    (by exact_mod_cast hq) (index_distance_lt q i j hi hj).le hs

end KroneckerPhasePerturbation
end

/- Original module: KroneckerPrefixResidues -/
section
/-! Integer residues of the prefix-floor vector at a nearby rational slope. -/
set_option autoImplicit false
namespace KroneckerPrefixResidues
open KroneckerMechanicalRuns KroneckerPhasePerturbation

noncomputable def prefixResidue (p q : ℕ) (s u : ℝ) (i : ℕ) : ℤ :=
  (q : ℤ)*mechanicalPrefix s u i-(i : ℤ)*(p : ℤ)

theorem prefix_difference_upper (s u : ℝ) (i j : ℕ) :
    ((mechanicalPrefix s u i-mechanicalPrefix s u j : ℤ) : ℝ) <
      ((i : ℝ)-(j : ℝ))*s+1 := by
  have hi := Int.floor_le (u+(i : ℝ)*s)
  have hj := Int.lt_floor_add_one (u+(j : ℝ)*s)
  unfold mechanicalPrefix
  push_cast
  nlinarith

theorem residue_difference_lt_succ (p q i j : ℕ) (hq : 0 < q)
    (hi : i < q) (hj : j < q) (s u : ℝ)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    prefixResidue p q s u i-prefixResidue p q s u j < (q : ℤ)+1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hfloor := mul_lt_mul_of_pos_left (prefix_difference_upper s u i j) hq'
  have he := (abs_lt.mp (index_slope_error q i j hq hi hj s ((p : ℝ)/(q : ℝ)) hs)).2
  have hqr : (q : ℝ)*((p : ℝ)/(q : ℝ))=(p : ℝ) := by field_simp
  have hid : (q : ℝ)*((i : ℝ)-(j : ℝ))*((p : ℝ)/(q : ℝ))=
      ((i : ℝ)-(j : ℝ))*(p : ℝ) := by
    calc
      _ = ((i : ℝ)-(j : ℝ))*((q : ℝ)*((p : ℝ)/(q : ℝ))) := by ring
      _ = _ := by rw [hqr]
  have hreal : ((prefixResidue p q s u i-prefixResidue p q s u j : ℤ) : ℝ) < (q : ℝ)+1 := by
    unfold prefixResidue
    push_cast at hfloor ⊢
    nlinarith
  exact_mod_cast hreal

theorem residue_difference_le_modulus (p q i j : ℕ) (hq : 0 < q)
    (hi : i < q) (hj : j < q) (s u : ℝ)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    prefixResidue p q s u i-prefixResidue p q s u j ≤ (q : ℤ) := by
  have h := residue_difference_lt_succ p q i j hq hi hj s u hs
  omega

end KroneckerPrefixResidues
end

/- Original module: KroneckerStrictPrefixGap -/
section
/-! The rational coprimality hypothesis improves the weak gap to a strict gap. -/
set_option autoImplicit false
namespace KroneckerStrictPrefixGap
open KroneckerMechanicalRuns KroneckerPrefixResidues KroneckerCoprimeIndexGap

theorem residue_difference_lt_modulus (p q i j : ℕ) (hq : 0 < q) (hc : p.Coprime q)
    (hi : i < q) (hj : j < q) (s u : ℝ)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    prefixResidue p q s u i-prefixResidue p q s u j < (q : ℤ) := by
  by_cases hij : i=j
  · subst j
    simpa using (show (0 : ℤ) < q by exact_mod_cast hq)
  · have hle := residue_difference_le_modulus p q i j hq hi hj s u hs
    have hne := scaled_gap_ne_modulus p q i j hc hi hj hij
      (mechanicalPrefix s u i) (mechanicalPrefix s u j)
    have hid : prefixResidue p q s u i-prefixResidue p q s u j =
        (q : ℤ)*(mechanicalPrefix s u i-mechanicalPrefix s u j)-((i : ℤ)-(j : ℤ))*(p : ℤ) := by
      unfold prefixResidue
      ring
    rw [hid] at hle ⊢
    omega

end KroneckerStrictPrefixGap
end

/- Original module: KroneckerMaximalPrefixResidue -/
section
/-! A finite maximum selects a rational phase from all prefix residues. -/
set_option autoImplicit false
namespace KroneckerMaximalPrefixResidue
open KroneckerPrefixResidues

noncomputable def maximalPrefixResidue (p q : ℕ) (hq : 0 < q) (s u : ℝ) : ℤ :=
  (Finset.range q).sup' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hq)) (prefixResidue p q s u)

theorem residue_le_maximal (p q : ℕ) (hq : 0 < q) (s u : ℝ) (i : ℕ) (hi : i < q) :
    prefixResidue p q s u i ≤ maximalPrefixResidue p q hq s u := by
  exact Finset.le_sup' (prefixResidue p q s u) (Finset.mem_range.mpr hi)

theorem maximal_residue_attained (p q : ℕ) (hq : 0 < q) (s u : ℝ) :
    ∃ i < q, maximalPrefixResidue p q hq s u = prefixResidue p q s u i := by
  obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hq)) (prefixResidue p q s u)
  exact ⟨i,Finset.mem_range.mp hi,heq⟩

end KroneckerMaximalPrefixResidue
end

/- Original module: KroneckerSelectedPhaseRange -/
section
/-! The selected integer phase lies between zero and q-1. -/
set_option autoImplicit false
namespace KroneckerSelectedPhaseRange
open KroneckerMechanicalRuns KroneckerPrefixResidues KroneckerStrictPrefixGap
open KroneckerMaximalPrefixResidue

theorem zero_prefix_residue (p q : ℕ) (s u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u < 1) :
    prefixResidue p q s u 0 = 0 := by
  have hu : ⌊u⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hu₀,hu₁⟩
  simp [prefixResidue,mechanicalPrefix,hu]

theorem selected_phase_range (p q : ℕ) (hq : 0 < q) (hc : p.Coprime q)
    (s u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u < 1)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    0 ≤ maximalPrefixResidue p q hq s u ∧ maximalPrefixResidue p q hq s u < (q : ℤ) := by
  have hz := zero_prefix_residue p q s u hu₀ hu₁
  constructor
  · simpa [hz] using residue_le_maximal p q hq s u 0 hq
  · obtain ⟨i,hi,heq⟩ := maximal_residue_attained p q hq s u
    rw [heq]
    simpa [hz] using residue_difference_lt_modulus p q i 0 hq hc hi hq s u hs

end KroneckerSelectedPhaseRange
end

/- Original module: KroneckerRationalPrefixRealization -/
section
/-! A nearby mechanical prefix vector is realized at an exact rational intercept. -/
set_option autoImplicit false
namespace KroneckerRationalPrefixRealization
open KroneckerMechanicalRuns KroneckerPrefixResidues KroneckerStrictPrefixGap
open KroneckerMaximalPrefixResidue KroneckerSelectedPhaseRange

theorem selected_prefix_realization (p q : ℕ) (hq : 0 < q) (hc : p.Coprime q)
    (s u : ℝ) (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2)
    (i : ℕ) (hi : i < q) :
    mechanicalPrefix ((p : ℝ)/(q : ℝ))
      ((maximalPrefixResidue p q hq s u : ℝ)/(q : ℝ)) i = mechanicalPrefix s u i := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo := residue_le_maximal p q hq s u i hi
  obtain ⟨j,hj,heq⟩ := maximal_residue_attained p q hq s u
  have hhi : maximalPrefixResidue p q hq s u-prefixResidue p q s u i < (q : ℤ) := by
    rw [heq]
    exact residue_difference_lt_modulus p q j i hq hc hj hi s u hs
  unfold prefixResidue at hlo hhi
  have hlo' : (q : ℝ)*(mechanicalPrefix s u i : ℝ)-(i : ℝ)*(p : ℝ) ≤
      (maximalPrefixResidue p q hq s u : ℝ) := by exact_mod_cast hlo
  have hhi' : (maximalPrefixResidue p q hq s u : ℝ)-
      ((q : ℝ)*(mechanicalPrefix s u i : ℝ)-(i : ℝ)*(p : ℝ)) < (q : ℝ) := by
    exact_mod_cast hhi
  have hx : (q : ℝ)*((maximalPrefixResidue p q hq s u : ℝ)/(q : ℝ)+
      (i : ℝ)*((p : ℝ)/(q : ℝ))) =
      (maximalPrefixResidue p q hq s u : ℝ)+(i : ℝ)*(p : ℝ) := by
    field_simp
  unfold mechanicalPrefix
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (mul_le_mul_iff_right₀ hq').mp
    rw [hx]
    change (q : ℝ)*(mechanicalPrefix s u i : ℝ) ≤ _
    linarith
  · apply (mul_lt_mul_iff_right₀ hq').mp
    rw [hx]
    change _ < (q : ℝ)*((mechanicalPrefix s u i : ℝ)+1)
    nlinarith

theorem selected_intercept_range (p q : ℕ) (hq : 0 < q) (hc : p.Coprime q)
    (s u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u < 1)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    0 ≤ (maximalPrefixResidue p q hq s u : ℝ)/(q : ℝ) ∧
      (maximalPrefixResidue p q hq s u : ℝ)/(q : ℝ) < 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨h₀,h₁⟩ := selected_phase_range p q hq hc s u hu₀ hu₁ hs
  constructor
  · exact div_nonneg (by exact_mod_cast h₀) hq'.le
  · apply (div_lt_one hq').mpr
    exact_mod_cast h₁

end KroneckerRationalPrefixRealization
end

/- Original module: KroneckerGoodWindowRealization -/
section
/-! The good-window sum fixes the remaining endpoint of a rational realization. -/
set_option autoImplicit false
namespace KroneckerGoodWindowRealization
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalWindows
open KroneckerMechanicalPeriodicity KroneckerMaximalPrefixResidue
open KroneckerRationalPrefixRealization KroneckerPrefixWordEquality

theorem good_window_endpoint (p q : ℕ) (s u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u < 1)
    (hgood : windowSum s u q 0=(p : ℤ)) : mechanicalPrefix s u q=(p : ℤ) := by
  have hu : ⌊u⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hu₀,hu₁⟩
  have hsum := mechanical_prefix_sum s u q
  have hg : (∑ i ∈ Finset.range q, mechanicalRun s u i)=(p : ℤ) := by
    simpa [windowSum] using hgood
  rw [hu,hg] at hsum
  omega

theorem rational_endpoint (p q : ℕ) (hq : 0 < q) (v : ℝ) (hv₀ : 0 ≤ v) (hv₁ : v < 1) :
    mechanicalPrefix ((p : ℝ)/(q : ℝ)) v q=(p : ℤ) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hv : ⌊v⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hv₀,hv₁⟩
  unfold mechanicalPrefix
  rw [show (q : ℝ)*((p : ℝ)/(q : ℝ))=(p : ℝ) by field_simp,
    ← Int.cast_natCast, Int.floor_add_intCast, hv, zero_add]

theorem selected_good_word (p q : ℕ) (hq : 0 < q) (hc : p.Coprime q)
    (s u : ℝ) (hu₀ : 0 ≤ u) (hu₁ : u < 1)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2)
    (hgood : windowSum s u q 0=(p : ℤ)) :
    mechanicalWord s u 0 q = mechanicalWord ((p : ℝ)/(q : ℝ))
      ((maximalPrefixResidue p q hq s u : ℝ)/(q : ℝ)) 0 q := by
  apply word_eq_of_prefix_offset s u _ _ q 0
  intro i hi
  simp only [add_zero]
  rcases lt_or_eq_of_le hi with hlt | heq
  · exact (selected_prefix_realization p q hq hc s u hs i hlt).symm
  · subst i
    obtain ⟨hv₀,hv₁⟩ := selected_intercept_range p q hq hc s u hu₀ hu₁ hs
    rw [good_window_endpoint p q s u hu₀ hu₁ hgood, rational_endpoint p q hq _ hv₀ hv₁]

end KroneckerGoodWindowRealization
end

/- Original module: KroneckerRationalResiduePhases -/
section
/-! Every rational intercept grid point is reached by a cyclic phase. -/
set_option autoImplicit false
namespace KroneckerRationalResiduePhases

theorem coprime_inverse (p q : ℕ) (hq : 1 < q) (hc : p.Coprime q) :
    ∃ c, p*c%q=1 := by
  obtain ⟨c, _, hc'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hq
  exact ⟨c, hc'⟩

theorem every_residue_phase (p q k : ℕ) (hq : 1 < q) (hc : p.Coprime q) (hk : k < q) :
    ∃ j < q, j*p%q=k := by
  obtain ⟨c,hc'⟩ := coprime_inverse p q hq hc
  refine ⟨(c*k)%q,Nat.mod_lt _ (by omega),?_⟩
  have hm : Nat.ModEq q ((c*k)%q) (c*k) := Nat.mod_mod _ _
  calc
    ((c*k)%q*p)%q = ((c*k)*p)%q := hm.mul_right p
    _ = ((p*c)*k)%q := by congr 1; ring
    _ = (1*k)%q := (show Nat.ModEq q (p*c) 1 from by simpa [Nat.ModEq, Nat.mod_eq_of_lt hq] using hc').mul_right k
    _ = k := by simp [Nat.mod_eq_of_lt hk]

theorem phase_division_identity (p q j k : ℕ) (h : j*p%q=k) :
    j*p=k+q*(j*p/q) := by
  have hd := Nat.mod_add_div (j*p) q
  rw [h] at hd
  exact hd.symm

end KroneckerRationalResiduePhases
end

/- Original module: KroneckerRationalGridShift -/
section
/-! A rational grid intercept differs from a cyclic shift by an integer. -/
set_option autoImplicit false
namespace KroneckerRationalGridShift
open KroneckerRationalResiduePhases

theorem grid_shift_identity (p q j k : ℕ) (hq : 0 < q) (h : j*p%q=k) :
    (j : ℝ)*((p : ℝ)/(q : ℝ))=(k : ℝ)/(q : ℝ)+(j*p/q : ℕ) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hd : (j : ℝ)*(p : ℝ)=(k : ℝ)+(q : ℝ)*(j*p/q : ℕ) := by
    exact_mod_cast phase_division_identity p q j k h
  field_simp
  nlinarith

theorem exists_grid_shift (p q k : ℕ) (hq : 1 < q) (hc : p.Coprime q) (hk : k < q) :
    ∃ j < q, ∃ z : ℤ, (j : ℝ)*((p : ℝ)/(q : ℝ))=(k : ℝ)/(q : ℝ)+(z : ℝ) := by
  obtain ⟨j,hj,hmod⟩ := every_residue_phase p q k hq hc hk
  refine ⟨j,hj,(j*p/q : ℕ),?_⟩
  simpa only [Int.cast_natCast] using grid_shift_identity p q j k (by omega) hmod

end KroneckerRationalGridShift
end

/- Original module: KroneckerGridWordRotation -/
section
/-! Every grid-intercept rational word is a rotation of the canonical period. -/
set_option autoImplicit false
namespace KroneckerGridWordRotation
open KroneckerMechanicalWords KroneckerMechanicalTranslation KroneckerMechanicalWordShift
open KroneckerRationalGridShift KroneckerRationalWordRotation

theorem grid_word_rotation (p q k : ℕ) (hq : 1 < q) (hc : p.Coprime q) (hk : k < q) :
    ∃ j < q, mechanicalWord ((p : ℝ)/(q : ℝ)) ((k : ℝ)/(q : ℝ)) 0 q =
      (rationalPeriod p q).rotate j := by
  obtain ⟨j,hj,z,hz⟩ := exists_grid_shift p q k hq hc hk
  refine ⟨j,hj,?_⟩
  have hshift := word_shift ((p : ℝ)/(q : ℝ)) 0 j q
  simp only [zero_add] at hshift
  rw [hz,word_add_integer] at hshift
  rw [← hshift]
  exact rational_word_rotation p q (by omega) j

end KroneckerGridWordRotation
end

/- Original module: KroneckerNormalizedGoodPhase -/
section
/-! A good block with arbitrary intercept has a rational grid representative. -/
set_option autoImplicit false
namespace KroneckerNormalizedGoodPhase
open KroneckerMechanicalRuns KroneckerMechanicalWords KroneckerMechanicalWindows
open KroneckerMechanicalTranslation KroneckerMechanicalFractional
open KroneckerMaximalPrefixResidue KroneckerSelectedPhaseRange KroneckerGoodWindowRealization

theorem window_add_integer (s u : ℝ) (z : ℤ) (q start : ℕ) :
    windowSum s (u+(z : ℝ)) q start = windowSum s u q start := by
  simp only [windowSum, run_add_integer]

theorem window_fractional (s u : ℝ) (q start : ℕ) :
    windowSum s (Int.fract u) q start = windowSum s u q start := by
  have h := window_add_integer s (Int.fract u) ⌊u⌋ q start
  rw [Int.fract_add_floor] at h
  exact h.symm

theorem exists_grid_good_word (p q : ℕ) (hq : 0 < q) (hc : p.Coprime q)
    (s u : ℝ) (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2)
    (hgood : windowSum s u q 0=(p : ℤ)) :
    ∃ k < q, mechanicalWord s u 0 q =
      mechanicalWord ((p : ℝ)/(q : ℝ)) ((k : ℝ)/(q : ℝ)) 0 q := by
  let z := maximalPrefixResidue p q hq s (Int.fract u)
  obtain ⟨hz₀,hz₁⟩ := selected_phase_range p q hq hc s (Int.fract u)
    (Int.fract_nonneg u) (Int.fract_lt_one u) hs
  have hzcast : (z.toNat : ℤ)=z := Int.toNat_of_nonneg hz₀
  have hk : z.toNat < q := by
    have h : (z.toNat : ℤ) < (q : ℤ) := by rw [hzcast]; exact hz₁
    exact_mod_cast h
  refine ⟨z.toNat,hk,?_⟩
  have hg := selected_good_word p q hq hc s (Int.fract u)
    (Int.fract_nonneg u) (Int.fract_lt_one u) hs
    (by rw [window_fractional]; exact hgood)
  rw [word_fractional] at hg
  have hzreal : (z.toNat : ℝ)=(z : ℝ) := by exact_mod_cast hzcast
  rw [hzreal]
  exact hg

end KroneckerNormalizedGoodPhase
end

/- Original module: KroneckerNearbyRationalPhase -/
section
/-! Nearby rational good q-windows are canonical cyclic rotations, with no phase assumption. -/
set_option autoImplicit false
namespace KroneckerNearbyRationalPhase
open KroneckerMechanicalWords KroneckerMechanicalWindows KroneckerMechanicalWordShift
open KroneckerNormalizedGoodPhase KroneckerGridWordRotation KroneckerRationalWordRotation

theorem nearby_good_window_rotation (p q : ℕ) (hq : 1 < q) (hc : p.Coprime q)
    (s u : ℝ) (start : ℕ) (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2)
    (hgood : windowSum s u q start=(p : ℤ)) :
    ∃ j < q, mechanicalWord s u start q=(rationalPeriod p q).rotate j := by
  rw [window_shift] at hgood
  obtain ⟨k,hk,hword⟩ := exists_grid_good_word p q (by omega) hc s
    (u+(start : ℝ)*s) hs hgood
  obtain ⟨j,hj,hrot⟩ := grid_word_rotation p q k hq hc hk
  refine ⟨j,hj,?_⟩
  rw [word_shift,hword,hrot]

theorem nearby_good_window_phase (p q : ℕ) (hq : 1 < q) (hc : p.Coprime q)
    (s u : ℝ) (start : ℕ) (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2)
    (hgood : windowSum s u q start=(p : ℤ)) :
    ∃ j ≤ (rationalPeriod p q).length,
      mechanicalWord s u start (rationalPeriod p q).length=(rationalPeriod p q).rotate j := by
  obtain ⟨j,hj,heq⟩ := nearby_good_window_rotation p q hq hc s u start hs hgood
  simpa only [rationalPeriod_length] using (show ∃ j ≤ q,
    mechanicalWord s u start q=(rationalPeriod p q).rotate j from ⟨j,hj.le,heq⟩)

end KroneckerNearbyRationalPhase
end
end

section

/- Original module: KroneckerShortPrefixPhase -/
section
/-! Short nearby-rational factors admit grid representatives without a window-sum condition. -/
set_option autoImplicit false
namespace KroneckerShortPrefixPhase
open KroneckerMechanicalWords KroneckerMechanicalFractional KroneckerMaximalPrefixResidue
open KroneckerSelectedPhaseRange KroneckerRationalPrefixRealization KroneckerPrefixWordEquality

theorem exists_grid_short_word (p q : ℕ) (hq : 0 < q) (hc : p.Coprime q)
    (s u : ℝ) (n : ℕ) (hn : n < q)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    ∃ k < q, mechanicalWord s u 0 n =
      mechanicalWord ((p : ℝ)/(q : ℝ)) ((k : ℝ)/(q : ℝ)) 0 n := by
  let z := maximalPrefixResidue p q hq s (Int.fract u)
  obtain ⟨hz₀,hz₁⟩ := selected_phase_range p q hq hc s (Int.fract u)
    (Int.fract_nonneg u) (Int.fract_lt_one u) hs
  have hzcast : (z.toNat : ℤ)=z := Int.toNat_of_nonneg hz₀
  have hk : z.toNat < q := by
    have h : (z.toNat : ℤ) < (q : ℤ) := by rw [hzcast]; exact hz₁
    exact_mod_cast h
  refine ⟨z.toNat,hk,?_⟩
  have hzreal : (z.toNat : ℝ)=(z : ℝ) := by exact_mod_cast hzcast
  rw [hzreal,← word_fractional s u 0 n]
  apply word_eq_of_prefix_offset s (Int.fract u) _ _ n 0
  intro i hi
  simp only [add_zero]
  exact (selected_prefix_realization p q hq hc s (Int.fract u) hs i (by omega)).symm

end KroneckerShortPrefixPhase
end

/- Original module: KroneckerNearbyShortFactor -/
section
/-! Every short nearby-rational factor occurs in a cyclic rational period. -/
set_option autoImplicit false
namespace KroneckerNearbyShortFactor
open KroneckerMechanicalWords KroneckerMechanicalWordShift KroneckerMechanicalSlices
open KroneckerShortPrefixPhase KroneckerGridWordRotation KroneckerRationalWordRotation

theorem word_take (s u : ℝ) (N n : ℕ) (hn : n ≤ N) :
    (mechanicalWord s u 0 N).take n=mechanicalWord s u 0 n := by
  simpa using mechanicalWord_slice s u 0 N 0 n (by omega)

theorem nearby_short_factor (p q : ℕ) (hq : 1 < q) (hc : p.Coprime q)
    (s u : ℝ) (start n : ℕ) (hn : n < q)
    (hs : |s-(p : ℝ)/(q : ℝ)| < 1/(q : ℝ)^2) :
    ∃ j < q, mechanicalWord s u start n=((rationalPeriod p q).rotate j).take n := by
  obtain ⟨k,hk,hword⟩ := exists_grid_short_word p q (by omega) hc s
    (u+(start : ℝ)*s) n hn hs
  obtain ⟨j,hj,hrot⟩ := grid_word_rotation p q k hq hc hk
  refine ⟨j,hj,?_⟩
  rw [word_shift,hword,← hrot,word_take _ _ q n hn.le]

end KroneckerNearbyShortFactor
end
end

