import KroneckerIrrationalIntervals

set_option autoImplicit false


namespace KroneckerGlobalExceptionalSubsequence
open KroneckerIrrationalWordSubsequence KroneckerExceptionalSubsequence KroneckerMechanicalPrefixSublist
open KroneckerMechanicalWords KroneckerPairedRunCosts

theorem global_exceptional_subsequence (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, 0 < L → ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ,
      0 ≤ s → 1 ≤ t → |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ n N M z : ℕ,
      t ≤ M → (1 ≤ z ∧ z ≤ M) → (n/L+1)*(L+Q)+1 ≤ N →
      ∃ Y : List ℕ, Y.length = n+1 ∧ Y.Sublist (mechanicalWord t v 0 N) ∧
        cost (mechanicalWord s u 0 n ++ [z]) Y ≤ (n/L+1)*(2*(L/q+1))+(M-1) := by
  obtain ⟨Q,hQ,hL⟩ := irrational_word_subsequence r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L hLpos
  obtain ⟨δ,hδ,h⟩ := hL L hLpos
  refine ⟨δ,hδ,?_⟩
  intro s t hs ht hsr htr u v n N M z htM hz hN
  obtain ⟨T,Y,_,hhi,hlen,hsub,hc⟩ := h s t hs (by linarith) hsr htr u v n
  obtain ⟨Z,hZlen,hZsub,hZcost⟩ := exceptional_subsequence (mechanicalWord s u 0 n) Y
    t v T z M _ (by rw [mechanicalWord_length,hlen]) hsub hc hz ht htM
  refine ⟨Z,?_,hZsub.trans (mechanical_prefix_sublist t v 0 (T+1) N (by omega)),hZcost⟩
  simpa only [mechanicalWord_length] using hZlen

end KroneckerGlobalExceptionalSubsequence

namespace KroneckerGlobalExceptionalPrograms
open KroneckerGlobalExceptionalSubsequence KroneckerPairedSublistPrograms
open KroneckerMechanicalWords KroneckerPairedRunCosts KroneckerRawMixedPrograms KroneckerWordCounts

theorem global_exceptional_programs (r : ℝ) (hr : Irrational r) (q : ℕ) (hq : 0 < q) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ L : ℕ, 0 < L → ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℕ,
      ∀ s t : ℝ, 0 ≤ s → 1 ≤ t → t ≤ (m-2 : ℕ) → |s-r| < δ → |t-r| < δ →
      ∀ u v : ℝ, ∀ n N z : ℕ, (1 ≤ z ∧ z ≤ m-2) → (n/L+1)*(L+Q)+1 ≤ N →
      ∃ A D : ℕ, A+D ≤ (n/L+1)*(2*(L/q+1))+(m-3) ∧
        Nonempty (RawProgram m (runWord (mechanicalWord s u 0 n ++ [z]))
          (runWord (mechanicalWord t v 0 N)) (N-(n+1)) A D) := by
  obtain ⟨Q,hQ,hL⟩ := global_exceptional_subsequence r hr q hq
  refine ⟨Q,hQ,?_⟩
  intro L hLpos
  obtain ⟨δ,hδ,h⟩ := hL L hLpos
  refine ⟨δ,hδ,?_⟩
  intro m s t hs ht htM hsr htr u v n N z hz hN
  obtain ⟨Y,hlen,hsub,hc⟩ := h s t hs ht hsr htr u v n N (m-2) z htM hz hN
  let X := mechanicalWord s u 0 n ++ [z]
  refine ⟨rises X Y,falls X Y,?_,?_⟩
  · simpa only [Nat.sub_sub,cost,X] using hc
  · have hp := paired_sublist_program m X Y (mechanicalWord t v 0 N)
      (by simp [X,mechanicalWord_length,hlen]) hsub (mechanicalWord_legal t v 0 N (m-2) ht htM)
    simpa only [X,List.length_append,List.length_singleton,mechanicalWord_length] using hp

end KroneckerGlobalExceptionalPrograms

namespace KroneckerSparsePrescribedExceptional
open KroneckerSparseExceptionalSubsequence KroneckerMechanicalPrefixSublist KroneckerPairedSublistPrograms
open KroneckerMechanicalWords KroneckerPairedRunCosts KroneckerRawMixedPrograms KroneckerWordCounts



theorem uniform_exceptional_programs (r : ℝ) (hr : Irrational r) (η : ℝ) (hη : 0 < η) (m : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, ∀ s t : ℝ,
      0 ≤ s → 1 ≤ t → t ≤ (m-2 : ℕ) → |s-r| < δ → |t-r| < δ →
      ∀ u v : ℝ, ∀ n T z : ℕ, (1 ≤ z ∧ z ≤ m-2) →
      (1+η)*((n : ℝ)+1)+(B₀ : ℝ) ≤ T →
      ∃ A D : ℕ, ((A+D : ℕ) : ℝ) ≤ η*((n : ℝ)+1)+(B₀ : ℝ) ∧
        Nonempty (RawProgram m (runWord (mechanicalWord s u 0 n ++ [z]))
          (runWord (mechanicalWord t v 0 T)) (T-(n+1)) A D) := by
  obtain ⟨q,hq,hcoeff⟩ := KroneckerSmallBlockCoefficients.small_block_coefficients η hη
  obtain ⟨Q,_,hL⟩ := KroneckerGlobalExceptionalPrograms.global_exceptional_programs r hr q hq
  obtain ⟨L,hLpos,hQsmall,hBsmall⟩ := hcoeff Q
  obtain ⟨δ,hδ,h⟩ := hL L hLpos
  let B := 2*(L/q+1)
  let B₀ := (L+Q+1)+B+(m-3)
  have hQη : (Q : ℝ)/L ≤ η := by linarith
  have hBη : (B : ℝ)/L ≤ η := by dsimp [B]; linarith
  have hbaseL : (L : ℝ)+(Q : ℝ)+1 ≤ B₀ := by
    exact_mod_cast (show L+Q+1 ≤ B₀ by dsimp [B₀]; omega)
  have hbaseB : (B : ℝ)+(m-3 : ℕ) ≤ B₀ := by
    exact_mod_cast (show B+(m-3) ≤ B₀ by dsimp [B₀]; omega)
  refine ⟨δ,hδ,B₀,?_⟩
  intro s t hs ht htM hsr htr u v n T z hz hT
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlen := KroneckerRoundedAffineBudget.rounded_length_budget n L Q hLpos
  have hmulQ := mul_le_mul_of_nonneg_right hQη hnR
  have hneeded : (n/L+1)*(L+Q)+1 ≤ T := by
    have hreal : (((n/L+1)*(L+Q)+1 : ℕ) : ℝ) ≤ T := by
      push_cast at hlen ⊢
      nlinarith
    exact_mod_cast hreal
  obtain ⟨A,D,hc,hp⟩ := h m s t hs ht htM hsr htr u v n T z hz hneeded
  refine ⟨A,D,?_,hp⟩
  have hb := KroneckerRoundedAffineBudget.rounded_affine_budget n L B hLpos
  have hmulB := mul_le_mul_of_nonneg_right hBη hnR
  have hcR : ((A+D : ℕ) : ℝ) ≤ (((n/L+1)*B : ℕ) : ℝ)+(m-3 : ℕ) := by
    exact_mod_cast hc
  nlinarith

theorem mechanical_edit_lemma (m : ℕ) (r η : ℝ) (hr : Irrational r)
    (hr1 : 1 < r) (hrM : r < (m-2 : ℕ)) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B₀ : ℕ, ∀ s t u v : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ n T z : ℕ, (1 ≤ z ∧ z ≤ m-2) →
      (1+η)*((n : ℝ)+1)+(B₀ : ℝ) ≤ T →
      ∃ A D : ℕ, ((A+D : ℕ) : ℝ) ≤ η*((n : ℝ)+1)+(B₀ : ℝ) ∧
        Nonempty (RawProgram m (runWord (mechanicalWord s u 0 n ++ [z]))
          (runWord (mechanicalWord t v 0 T)) (T-(n+1)) A D) := by
  obtain ⟨d,hd,B₀,h⟩ := uniform_exceptional_programs r hr η hη m
  let δ := min d (min (r-1) ((m-2 : ℕ)-r))
  have hδ : 0 < δ := lt_min hd (lt_min (by linarith) (by linarith))
  refine ⟨δ,hδ,B₀,?_⟩
  intro s t u v hs ht n T z hz hT
  have hs' := abs_lt.mp hs
  have ht' := abs_lt.mp ht
  have hd1 : δ ≤ r-1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdM : δ ≤ (m-2 : ℕ)-r := (min_le_right _ _).trans (min_le_right _ _)
  exact h s t (by linarith [hs'.1]) (by linarith [ht'.1]) (by linarith [ht'.2])
    (lt_of_lt_of_le hs (min_le_left _ _)) (lt_of_lt_of_le ht (min_le_left _ _)) u v n T z hz hT


end KroneckerSparsePrescribedExceptional
