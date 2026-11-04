import KroneckerMechanicalEditsStatement
import KroneckerManuscriptBinaryEditClaims

/-! Lemma 9.19 uses the admissible tuples of Definition 6.2 with M = 2.
The last source run may be exceptional. Shrinking delta ensures that both
mechanical slopes lie in (1,2), so all source and target runs are binary. -/
set_option autoImplicit false
noncomputable section

namespace KroneckerMechanicalEditsStatement
open KroneckerPaperPaths KroneckerMechanicalWords KroneckerCurrentMechanicalNotation

theorem Admissible.binary_source {r η δ B : ℝ} (x : Admissible 2 r η δ B) :
    KroneckerBinaryMechanicalSource.BinaryMechanicalSource x.σ₁ x.u₁ x.l x.S := by
  have hlen := x.length_eq
  have hpos := x.l_pos
  refine Or.inr ⟨x.l-1, x.S[x.l-1]'(by omega), by omega,
    x.last_length.1, x.last_length.2, ?_⟩
  exact source_list x.S (x.l-1) (x.S[x.l-1]'(by omega)) x.σ₁ x.u₁
    (by linarith [x.σ₁_ge]) (by omega) x.first_lengths rfl

/-- Admissibility alone supplies all source and target hypotheses of Lemma 9.19. -/
theorem binary_mechanical_admissible (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < min (r-1) (2-r) ∧ ∃ B : ℕ, 0 < B ∧
      ∀ x : Admissible 2 r η δ B, ∀ U : TNEPath, U = runPath x.S U.origin →
      ∃ k : ℕ, (∃ ζ : LatticePoint,
        Nonempty (BinEdit (x.T-x.l) k U (translate (MechRunFactor x.σ₂ x.u₂ 1 x.T) ζ))) ∧
        (k : ℝ) ≤ 7*η*(x.l : ℝ)+B := by
  obtain ⟨δ₀, hδ₀, B, hB, h⟩ := binary_mechanical_binEdit r η hr hrb hη
  let δ := min δ₀ (min (r-1) (2-r)) / 2
  have hsmall : 0 < min δ₀ (min (r-1) (2-r)) := by
    exact lt_min hδ₀ (lt_min (by linarith [hrb.1]) (by linarith [hrb.2]))
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδ₀' : δ < δ₀ := by
    have := min_le_left δ₀ (min (r-1) (2-r))
    dsimp [δ]; linarith
  have hδr : δ < min (r-1) (2-r) := by
    have := min_le_right δ₀ (min (r-1) (2-r))
    dsimp [δ]; linarith
  refine ⟨δ, hδ, hδr, B, hB, ?_⟩
  intro x U hU
  have hs : x.σ₁ ≤ 2 := by
    have := (abs_lt.mp x.σ₁_near).2
    have := lt_of_lt_of_le hδr (min_le_right (r-1) (2-r))
    linarith
  have hlegal := KroneckerBinaryMechanicalSource.binary_source_legal x.binary_source
    ⟨x.σ₁_ge, hs⟩
  have hbinary : Binary U := by
    rw [hU]
    apply (binary_runPath_iff x.S U.origin).mpr
    refine ⟨?_, ?_⟩
    · intro he
      have := x.length_eq
      have := x.l_pos
      simp [he] at *
      omega
    · intro z hz
      have := hlegal z hz
      omega
  exact h x.σ₁ x.σ₂ x.u₁ x.u₂ (lt_trans x.σ₁_near hδ₀')
    (lt_trans x.σ₂_near hδ₀') x.l x.T x.S x.binary_source x.length_budget U hbinary
    (by rw [hU]; rfl)

end KroneckerMechanicalEditsStatement

#print axioms KroneckerMechanicalEditsStatement.Admissible.binary_source
#print axioms KroneckerMechanicalEditsStatement.binary_mechanical_admissible
