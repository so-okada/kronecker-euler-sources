import Mathlib.NumberTheory.Real.Irrational
import KroneckerPairedMechanicalCost
import KroneckerMechanicalPrefixSublist
import KroneckerUniformBlockAlignment
import KroneckerNormalizedWindow
import KroneckerMechanicalSlices
import KroneckerRoundedBlockLength

section

/- Original module: KroneckerNearBoundaryInteger -/
section
/-! A near-boundary fractional part has an explicit nearby integer witness. -/
set_option autoImplicit false
namespace KroneckerNearBoundaryInteger
open KroneckerBoundaryVisits

theorem near_boundary_integer (x ε : ℝ) (h : NearBoundary x ε) :
    ∃ z : ℤ, |x-(z : ℝ)| < ε := by
  have hf := Int.fract_nonneg x
  have hlt := Int.fract_lt_one x
  rcases h with h|h
  · refine ⟨⌊x⌋,?_⟩
    change |Int.fract x| < ε
    rwa [abs_of_nonneg hf]
  · refine ⟨⌊x⌋+1,?_⟩
    have he : x-((⌊x⌋+1 : ℤ) : ℝ)=Int.fract x-1 := by
      simp only [Int.fract,Int.cast_add,Int.cast_one]
      ring
    rw [he,abs_of_neg (by linarith)]
    linarith

end KroneckerNearBoundaryInteger
end

/- Original module: KroneckerNearBoundaryPair -/
section
/-! Two boundary visits force their orbit displacement close to an integer. -/
set_option autoImplicit false
namespace KroneckerNearBoundaryPair
open KroneckerBoundaryVisits KroneckerNearBoundaryInteger

theorem near_boundary_pair (x y ε : ℝ) (hx : NearBoundary x ε) (hy : NearBoundary y ε) :
    ∃ z : ℤ, |(y-x)-(z : ℝ)| < 2*ε := by
  obtain ⟨a,ha⟩ := near_boundary_integer x ε hx
  obtain ⟨b,hb⟩ := near_boundary_integer y ε hy
  refine ⟨b-a,?_⟩
  have he : (y-x)-((b-a : ℤ) : ℝ)=(y-(b : ℝ))-(x-(a : ℝ)) := by
    push_cast
    ring
  rw [he]
  have h := abs_sub (y-(b : ℝ)) (x-(a : ℝ))
  linarith

end KroneckerNearBoundaryPair
end

/- Original module: KroneckerIntegerSeparation -/
section
/-! A nonintegral real point has a positive, explicit distance from every integer. -/
set_option autoImplicit false
namespace KroneckerIntegerSeparation

noncomputable def gap (x : ℝ) : ℝ := min (Int.fract x) (1-Int.fract x)

theorem gap_le_integer_distance (x : ℝ) (z : ℤ) : gap x ≤ |x-(z : ℝ)| := by
  have hf : Int.fract x=x-(⌊x⌋ : ℝ) := rfl
  by_cases hz : z ≤ ⌊x⌋
  · have hz' : (z : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hz
    have h := le_abs_self (x-(z : ℝ))
    have hg : gap x ≤ Int.fract x := min_le_left _ _
    linarith
  · have hz' : (⌊x⌋ : ℝ)+1 ≤ (z : ℝ) := by
      exact_mod_cast (show ⌊x⌋+1 ≤ z by omega)
    have h := neg_le_abs (x-(z : ℝ))
    have hg : gap x ≤ 1-Int.fract x := min_le_right _ _
    linarith

theorem irrational_gap_pos (x : ℝ) (hx : Irrational x) : 0 < gap x := by
  apply lt_min
  · have hf := Int.fract_nonneg x
    by_contra h
    have hz : Int.fract x=0 := by linarith
    have he : x=(⌊x⌋ : ℝ) := by simpa only [Int.fract,sub_eq_zero] using hz
    exact hx.ne_int ⌊x⌋ he
  · have h := Int.fract_lt_one x
    linarith

end KroneckerIntegerSeparation
end

/- Original module: KroneckerIrrationalFiniteSeparation -/
section
/-! Every fixed finite set of nonzero irrational multiples stays uniformly away from integers. -/
set_option autoImplicit false
namespace KroneckerIrrationalFiniteSeparation
open KroneckerIntegerSeparation

theorem irrational_finite_separation (r : ℝ) (hr : Irrational r) (q : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ k : ℕ, 0 < k → k < q → ∀ z : ℤ, ρ ≤ |(k : ℝ)*r-(z : ℝ)| := by
  induction q with
  | zero => exact ⟨1,by norm_num,fun k _ hk => by omega⟩
  | succ q ih =>
    obtain ⟨ρ,hρ,h⟩ := ih
    by_cases hq : q=0
    · subst q
      exact ⟨1,by norm_num,fun k hk hk' => by omega⟩
    · have hg := irrational_gap_pos ((q : ℝ)*r) (hr.natCast_mul hq)
      refine ⟨min ρ (gap ((q : ℝ)*r)),lt_min hρ hg,?_⟩
      intro k hk hkq z
      by_cases hlt : k < q
      · exact (min_le_left _ _).trans (h k hk hlt z)
      · have he : k=q := by omega
        subst k
        exact (min_le_right _ _).trans (gap_le_integer_distance _ z)

end KroneckerIrrationalFiniteSeparation
end

/- Original module: KroneckerNearbySlopeSeparation -/
section
/-! Finite integer separation persists uniformly in a neighborhood of the slope. -/
set_option autoImplicit false
namespace KroneckerNearbySlopeSeparation

theorem nearby_slope_separation (r s ρ : ℝ) (q : ℕ) (hq : 0 < q)
    (hgap : ∀ k : ℕ, 0 < k → k < q → ∀ z : ℤ, ρ ≤ |(k : ℝ)*r-(z : ℝ)|)
    (hs : |s-r| < ρ/(2*(q : ℝ))) :
    ∀ k : ℕ, 0 < k → k < q → ∀ z : ℤ, ρ/2 ≤ |(k : ℝ)*s-(z : ℝ)| := by
  intro k hk hkq z
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hs' : |s-r| < (ρ/2)/(q : ℝ) := by convert hs using 1; ring
  have hmul := (lt_div_iff₀ hq').mp hs'
  have hk' : (k : ℝ) ≤ q := by exact_mod_cast hkq.le
  have hm := mul_le_mul_of_nonneg_right hk' (abs_nonneg (s-r))
  have he : (k : ℝ)*r-(z : ℝ)=(k : ℝ)*(r-s)+((k : ℝ)*s-(z : ℝ)) := by ring
  have ht := abs_add_le ((k : ℝ)*(r-s)) ((k : ℝ)*s-(z : ℝ))
  rw [←he,abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ k by positivity),abs_sub_comm r s] at ht
  have hg := hgap k hk hkq z
  nlinarith

end KroneckerNearbySlopeSeparation
end

/- Original module: KroneckerBoundaryWindowSparsity -/
section
/-! Uniform finite integer separation permits at most one boundary visit per window. -/
set_option autoImplicit false
namespace KroneckerBoundaryWindowSparsity
open KroneckerBoundaryVisits KroneckerNearBoundaryPair

theorem boundary_window_sparse (s u ε : ℝ) (q : ℕ)
    (hsep : ∀ k : ℕ, 0 < k → k < q → ∀ z : ℤ, 2*ε ≤ |(k : ℝ)*s-(z : ℝ)|) :
    visits s u ε q ≤ 1 := by
  classical
  have hpair : ∀ i j : ℕ, i < j → j < q →
      NearBoundary (u+((i+1 : ℕ) : ℝ)*s) ε →
      NearBoundary (u+((j+1 : ℕ) : ℝ)*s) ε → False := by
    intro i j hij hj hi' hj'
    obtain ⟨z,hz⟩ := near_boundary_pair _ _ ε hi' hj'
    have he : (u+((j+1 : ℕ) : ℝ)*s)-(u+((i+1 : ℕ) : ℝ)*s)=((j-i : ℕ) : ℝ)*s := by
      rw [Nat.cast_sub hij.le]
      push_cast
      ring
    rw [he] at hz
    exact (not_lt_of_ge (hsep (j-i) (by omega) (by omega) z)) hz
  unfold visits
  rw [←Finset.card_filter]
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [Finset.mem_filter,Finset.mem_range] at hi hj
  rcases lt_trichotomy i j with hij|hij|hij
  · exact (hpair i j hij hj.1 hi.2 hj.2).elim
  · exact hij
  · exact (hpair j i hij hi.1 hj.2 hi.2).elim

end KroneckerBoundaryWindowSparsity
end

/- Original module: KroneckerVisitsConcatenation -/
section
/-! Boundary visits concatenate with the exact shifted intercept and are monotone in length. -/
set_option autoImplicit false
namespace KroneckerVisitsConcatenation
open KroneckerBoundaryVisits

theorem visits_add (s u ε : ℝ) (n k : ℕ) :
    visits s u ε (n+k)=visits s u ε n+visits s (u+(n : ℝ)*s) ε k := by
  classical
  unfold visits
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : u+((n+i+1 : ℕ) : ℝ)*s=(u+(n : ℝ)*s)+((i+1 : ℕ) : ℝ)*s := by
    push_cast
    ring
  rw [he]

theorem visits_mono (s u ε : ℝ) (n k : ℕ) (h : n ≤ k) : visits s u ε n ≤ visits s u ε k := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [visits_add]
  omega

end KroneckerVisitsConcatenation
end

/- Original module: KroneckerVisitsBlockedBound -/
section
/-! Uniform one-visit windows imply a uniform density bound at every block length. -/
set_option autoImplicit false
namespace KroneckerVisitsBlockedBound
open KroneckerBoundaryVisits KroneckerVisitsConcatenation

theorem visits_multiple_bound (s ε : ℝ) (q : ℕ) (h : ∀ u : ℝ, visits s u ε q ≤ 1) :
    ∀ k : ℕ, ∀ u : ℝ, visits s u ε (k*q) ≤ k := by
  intro k
  induction k with
  | zero => intro u; simp [visits]
  | succ k ih =>
    intro u
    rw [Nat.succ_mul,visits_add]
    exact Nat.add_le_add (ih u) (h _)

theorem visits_blocked_bound (s u ε : ℝ) (q n : ℕ) (hq : 0 < q)
    (h : ∀ v : ℝ, visits s v ε q ≤ 1) : visits s u ε n ≤ n/q+1 := by
  have hmod := Nat.mod_lt n hq
  have hdiv := Nat.div_add_mod n q
  have hlen : n ≤ (n/q+1)*q := by nlinarith
  exact (visits_mono s u ε n _ hlen).trans (visits_multiple_bound s ε q h (n/q+1) u)

end KroneckerVisitsBlockedBound
end

/- Original module: KroneckerIrrationalVisitDensity -/
section
/-! Nearby slopes have uniformly sparse near-integer visits at every intercept. -/
set_option autoImplicit false
namespace KroneckerIrrationalVisitDensity
open KroneckerBoundaryVisits KroneckerIrrationalFiniteSeparation KroneckerNearbySlopeSeparation
open KroneckerBoundaryWindowSparsity KroneckerVisitsBlockedBound

theorem irrational_visit_density (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ ε δ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧
      ∀ s : ℝ, |s-r| < δ → ∀ u : ℝ, ∀ n : ℕ, visits s u ε n ≤ n/q+1 := by
  obtain ⟨ρ,hρ,hgap⟩ := irrational_finite_separation r hr q
  refine ⟨min (ρ/4) (1/2),ρ/(2*(q : ℝ)),lt_min (by positivity) (by norm_num),?_,by positivity,?_⟩
  · exact (min_le_right _ _).trans (by norm_num)
  · intro s hs u n
    have hsep := nearby_slope_separation r s ρ q hq hgap hs
    apply visits_blocked_bound s u _ q n hq
    intro v
    apply boundary_window_sparse
    intro k hk hkq z
    have he : 2*min (ρ/4) (1/2) ≤ ρ/2 := by have := min_le_left (ρ/4) (1/2); linarith
    exact he.trans (hsep k hk hkq z)

end KroneckerIrrationalVisitDensity
end
end

section

/- Original module: KroneckerAlignedPairedCost -/
section
set_option autoImplicit false
namespace KroneckerAlignedPairedCost
open KroneckerPairedRunCosts KroneckerPairedMechanicalCost KroneckerMechanicalWords
open KroneckerMechanicalBoundaryCost KroneckerBoundaryVisits

theorem aligned_paired_cost (s u t v ε : ℝ) (n : ℕ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hu : 0 ≤ u ∧ u < 1) (hv : 0 ≤ v ∧ v < 1) (hε : ε ≤ 1)
    (hclose : |u-v|+(n : ℝ)*|s-t| < ε) :
    cost (mechanicalWord s u 0 n) (mechanicalWord t v 0 n) ≤ 2*visits s u ε n := by
  have h := mechanical_boundary_cost s u t v ε n hu hv hε hclose
  rw [← paired_mechanical_cost s u t v n hs ht] at h
  exact_mod_cast h

end KroneckerAlignedPairedCost
end

/- Original module: KroneckerMechanicalGapSublist -/
section
set_option autoImplicit false
namespace KroneckerMechanicalGapSublist
open KroneckerMechanicalWords KroneckerMechanicalWordSums

theorem mechanical_gap_sublist (s u : ℝ) (T j L : ℕ) :
    (mechanicalWord s u 0 T ++ mechanicalWord s u (T+j) L).Sublist
      (mechanicalWord s u 0 (T+j+L)) := by
  rw [show T+j+L = T+(j+L) by omega, mechanicalWord_append s u 0 T (j+L)]
  simp only [Nat.zero_add]
  rw [mechanicalWord_append s u T j L]
  exact List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _)

end KroneckerMechanicalGapSublist
end

/- Original module: KroneckerGreedyBlocks -/
section
set_option autoImplicit false
namespace KroneckerGreedyBlocks
open KroneckerMechanicalWords KroneckerMechanicalWordSums KroneckerMechanicalGapSublist
open KroneckerPairedRunCosts KroneckerPairedCostsAppend

theorem greedy_blocks (s t u v : ℝ) (L Q B : ℕ)
    (hmatch : ∀ i k : ℕ, ∃ j < Q,
      cost (mechanicalWord s u i L) (mechanicalWord t v (k+j) L) ≤ B) (a : ℕ) :
    ∃ T : ℕ, ∃ Y : List ℕ, a*L ≤ T ∧ T ≤ a*(L+Q) ∧ Y.length = a*L ∧
      Y.Sublist (mechanicalWord t v 0 T) ∧
      cost (mechanicalWord s u 0 (a*L)) Y ≤ a*B := by
  induction a with
  | zero =>
    refine ⟨0,[],?_⟩
    simp [mechanicalWord,cost,rises,falls]
  | succ a ih =>
    obtain ⟨T,Y,hlo,hhi,hlen,hsub,hcost⟩ := ih
    obtain ⟨j,hj,hjcost⟩ := hmatch (a*L) T
    let Z := mechanicalWord t v (T+j) L
    refine ⟨T+j+L,Y++Z,?_,?_,?_,?_,?_⟩
    · rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega
    · simp only [List.length_append,hlen,Z,mechanicalWord_length,Nat.succ_mul]
    · exact (hsub.append (List.Sublist.refl Z)).trans (mechanical_gap_sublist t v T j L)
    · rw [Nat.succ_mul,mechanicalWord_append]
      simp only [Nat.zero_add]
      rw [cost_append _ _ _ _ (by rw [mechanicalWord_length,hlen])]
      change cost (mechanicalWord s u 0 (a*L)) Y +
        cost (mechanicalWord s u (a*L) L) (mechanicalWord t v (T+j) L) ≤ (a+1)*B
      nlinarith

end KroneckerGreedyBlocks
end

/- Original module: KroneckerIrrationalBlockCost -/
section
set_option autoImplicit false
namespace KroneckerIrrationalBlockCost
open KroneckerUniformBlockAlignment KroneckerAlignedPairedCost
open KroneckerIrrationalVisitDensity KroneckerNormalizedWindow
open KroneckerMechanicalWords KroneckerPairedRunCosts

theorem irrational_block_cost (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s t u v : ℝ,
      0 ≤ s → 0 ≤ t → |s-r| < δ → |t-r| < δ →
      (0 ≤ u ∧ u < 1) → (0 ≤ v ∧ v < 1) →
      ∀ n ≤ L, ∃ j < Q,
        cost (mechanicalWord s u 0 n) (mechanicalWord t v j n) ≤ 2*(n/q+1) := by
  obtain ⟨ε,d,hε,hε1,hd,hvis⟩ := irrational_visit_density r hr q hq
  obtain ⟨Q,hQ,hL⟩ := uniform_block_alignment r ε hr hε
  refine ⟨Q,hQ,?_⟩
  intro L
  obtain ⟨e,he,halign⟩ := hL L
  refine ⟨min d e,lt_min hd he,?_⟩
  intro s t u v hs ht hsr htr hu hv n hn
  obtain ⟨j,hj,hjclose⟩ := halign s t u v
    (lt_of_lt_of_le hsr (min_le_right _ _))
    (lt_of_lt_of_le htr (min_le_right _ _)) hu hv n hn
  have hc := aligned_paired_cost s u t (Int.fract (v+(j : ℝ)*t)) ε n hs ht hu
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ hε1 hjclose
  refine ⟨j,hj,?_⟩
  rw [normalized_window t v j n]
  exact hc.trans (Nat.mul_le_mul_left 2 (hvis s (lt_of_lt_of_le hsr (min_le_left _ _)) u n))

end KroneckerIrrationalBlockCost
end

/- Original module: KroneckerShiftedBlockCost -/
section
set_option autoImplicit false
namespace KroneckerShiftedBlockCost
open KroneckerIrrationalBlockCost KroneckerNormalizedWindow
open KroneckerMechanicalWords KroneckerPairedRunCosts

theorem shifted_block_cost (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ,
      0 ≤ s → 0 ≤ t → |s-r| < δ → |t-r| < δ →
      ∀ u v : ℝ, ∀ i k n : ℕ, n ≤ L → ∃ j < Q,
        cost (mechanicalWord s u i n) (mechanicalWord t v (k+j) n) ≤ 2*(n/q+1) := by
  obtain ⟨Q,hQ,hL⟩ := irrational_block_cost r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L
  obtain ⟨δ,hδ,h⟩ := hL L
  refine ⟨δ,hδ,?_⟩
  intro s t hs ht hsr htr u v i k n hn
  obtain ⟨j,hj,hc⟩ := h s t (Int.fract (u+(i : ℝ)*s))
    (Int.fract (v+(k : ℝ)*t)) hs ht hsr htr
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ n hn
  refine ⟨j,hj,?_⟩
  rw [← normalized_window s u i n, nested_window] at hc
  exact hc

end KroneckerShiftedBlockCost
end

/- Original module: KroneckerIrrationalBlockSubsequence -/
section
set_option autoImplicit false
namespace KroneckerIrrationalBlockSubsequence
open KroneckerGreedyBlocks KroneckerShiftedBlockCost
open KroneckerMechanicalWords KroneckerPairedRunCosts

theorem irrational_block_subsequence (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ,
      0 ≤ s → 0 ≤ t → |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ a : ℕ,
      ∃ T : ℕ, ∃ Y : List ℕ, a*L ≤ T ∧ T ≤ a*(L+Q) ∧ Y.length = a*L ∧
        Y.Sublist (mechanicalWord t v 0 T) ∧
        cost (mechanicalWord s u 0 (a*L)) Y ≤ a*(2*(L/q+1)) := by
  obtain ⟨Q,hQ,hL⟩ := shifted_block_cost r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L
  obtain ⟨δ,hδ,h⟩ := hL L
  refine ⟨δ,hδ,?_⟩
  intro s t hs ht hsr htr u v a
  apply greedy_blocks s t u v L Q (2*(L/q+1)) ?_ a
  intro i k
  exact h s t hs ht hsr htr u v i k L le_rfl

end KroneckerIrrationalBlockSubsequence
end

/- Original module: KroneckerPairedPrefixCost -/
section
set_option autoImplicit false
namespace KroneckerPairedPrefixCost
open KroneckerPairedRunCosts

theorem paired_prefix_cost (X Y : List ℕ) (n : ℕ) :
    cost (X.take n) (Y.take n) ≤ cost X Y := by
  induction n generalizing X Y with
  | zero => simp [cost,rises,falls]
  | succ n ih =>
    cases X with
    | nil => simp [cost,rises,falls]
    | cons x X =>
      cases Y with
      | nil => simp [cost,rises,falls]
      | cons y Y =>
        have h := ih X Y
        simp only [List.take_succ_cons,cost,falls,rises,List.zipWith_cons_cons,
          List.sum_cons] at h ⊢
        omega

end KroneckerPairedPrefixCost
end

/- Original module: KroneckerTruncatedMatch -/
section
set_option autoImplicit false
namespace KroneckerTruncatedMatch
open KroneckerPairedRunCosts KroneckerPairedPrefixCost
open KroneckerMechanicalWords KroneckerMechanicalSlices

theorem truncated_match (s u : ℝ) (N n B : ℕ) (Y Z : List ℕ)
    (hn : n ≤ N) (hlen : Y.length = N) (hsub : Y.Sublist Z)
    (hc : cost (mechanicalWord s u 0 N) Y ≤ B) :
    ∃ X : List ℕ, X.length = n ∧ X.Sublist Z ∧
      cost (mechanicalWord s u 0 n) X ≤ B := by
  refine ⟨Y.take n,?_,(List.take_sublist n Y).trans hsub,?_⟩
  · simp [List.length_take,hlen,Nat.min_eq_left hn]
  · have htake : (mechanicalWord s u 0 N).take n = mechanicalWord s u 0 n := by
      simpa using mechanicalWord_slice s u 0 N 0 n (by omega)
    have h := paired_prefix_cost (mechanicalWord s u 0 N) Y n
    rw [htake] at h
    exact h.trans hc

end KroneckerTruncatedMatch
end

/- Original module: KroneckerIrrationalWordSubsequence -/
section
set_option autoImplicit false
namespace KroneckerIrrationalWordSubsequence
open KroneckerIrrationalBlockSubsequence KroneckerRoundedBlockLength KroneckerTruncatedMatch
open KroneckerMechanicalWords KroneckerPairedRunCosts

theorem irrational_word_subsequence (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, 0 < L → ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ,
      0 ≤ s → 0 ≤ t → |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ n : ℕ,
      ∃ T : ℕ, ∃ Y : List ℕ, n ≤ T ∧ T ≤ (n/L+1)*(L+Q) ∧ Y.length = n ∧
        Y.Sublist (mechanicalWord t v 0 T) ∧
        cost (mechanicalWord s u 0 n) Y ≤ (n/L+1)*(2*(L/q+1)) := by
  obtain ⟨Q,hQ,hL⟩ := irrational_block_subsequence r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L hLpos
  obtain ⟨δ,hδ,h⟩ := hL L
  refine ⟨δ,hδ,?_⟩
  intro s t hs ht hsr htr u v n
  obtain ⟨T,Y,hlo,hhi,hlen,hsub,hc⟩ := h s t hs ht hsr htr u v (n/L+1)
  have hn := (rounded_block_length n L hLpos).1
  obtain ⟨X,hXlen,hXsub,hXcost⟩ := truncated_match s u _ n _ Y _ hn hlen hsub hc
  exact ⟨T,X,hn.trans hlo,hhi,hXlen,hXsub,hXcost⟩

end KroneckerIrrationalWordSubsequence
end
end

