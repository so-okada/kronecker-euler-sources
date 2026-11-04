import KroneckerBoundedMechanicalEdits

/-! The pointwise source-length hypotheses and explicit concluding path of Lemma 6.5.
Lists record the vertical lengths of the concatenated simple runs.
The witnesses delta and B denote delta_m(r,eta) and B_m(r,eta);
their quantifiers follow m,r,eta. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerMechanicalEditsStatement
open KroneckerPaperPaths KroneckerMechanicalWords KroneckerMechanicalRuns
open KroneckerCurrentMechanicalNotation KroneckerRunEditPrograms

theorem source_list (S : List ℕ) (n z : ℕ) (σ u : ℝ) (hs : 0 ≤ σ)
    (hlen : S.length=n+1)
    (hfirst : ∀ i : ℕ, ∀ hi : i<n,
      (S[i]'(by omega) : ℤ)=⌊u+((i+1 : ℕ) : ℝ)*σ⌋-⌊u+(i : ℝ)*σ⌋)
    (hlast : S[n]'(by omega)=z) :
    S=mechanicalWord σ u 0 n ++ [z] := by
  apply List.ext_getElem
  · simp [hlen, mechanicalWord_length]
  · intro i hi hj
    by_cases hin : i<n
    · rw [List.getElem_append_left (by simpa [mechanicalWord_length] using hin)]
      simp only [mechanicalWord, List.getElem_ofFn, Nat.zero_add]
      apply Int.ofNat_inj.mp
      rw [natRun_cast σ u i hs]
      exact hfirst i hin
    · have he : i=n := by omega
      subst i
      simpa [List.getElem_append, mechanicalWord_length] using hlast

/-- Definition 6.2. S contains the vertical lengths of A_1,...,A_l.
The path reached by the run-edits is not part of an admissible tuple. -/
structure Admissible (M : ℕ) (r η δ B : ℝ) where
  l : ℕ
  T : ℕ
  l_pos : 0 < l
  T_pos : 0 < T
  σ₁ : ℝ
  σ₂ : ℝ
  u₁ : ℝ
  u₂ : ℝ
  σ₁_ge : 1 ≤ σ₁
  σ₂_ge : 1 ≤ σ₂
  u₁_range : u₁ ∈ Set.Ico (0 : ℝ) 1
  u₂_range : u₂ ∈ Set.Ico (0 : ℝ) 1
  S : List ℕ
  length_eq : S.length=l
  first_lengths : ∀ i : ℕ, ∀ hi : i<l-1,
    (S[i]'(by have := length_eq; omega) : ℤ)=
      ⌊u₁+((i+1 : ℕ) : ℝ)*σ₁⌋-⌊u₁+(i : ℝ)*σ₁⌋
  last_length : 1 ≤ S[l-1]'(by have := length_eq; have := l_pos; omega) ∧
    S[l-1]'(by have := length_eq; have := l_pos; omega) ≤ M
  σ₁_near : |σ₁-r| < δ
  σ₂_near : |σ₂-r| < δ
  length_budget : (1+η)*(l : ℝ)+B ≤ T

/-- The constants precede all free parameters. The concluding path is
Trans(MechRunFactor sigma2 u2 1 T, ζ); ζ is existential.
No path V occurs among the hypotheses. -/
theorem mechanical_edits_expanded (m : ℕ) (r η : ℝ) (hm : 4 ≤ m)
    (hr : Irrational r) (hr1 : 1 < r) (hrM : r < (m-2 : ℕ))
    (hη : 0 < η ∧ η < 1/4) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧
      ∀ l T : ℕ, ∀ hl : 0 < l, 0 < T → ∀ σ₁ σ₂ u₁ u₂ : ℝ,
      1 ≤ σ₁ → 1 ≤ σ₂ → u₁ ∈ Set.Ico (0 : ℝ) 1 → u₂ ∈ Set.Ico (0 : ℝ) 1 →
      ∀ S : List ℕ, ∀ hlen : S.length=l,
      (∀ i : ℕ, ∀ hi : i<l-1,
        (S[i]'(by omega) : ℤ)=⌊u₁+((i+1 : ℕ) : ℝ)*σ₁⌋-⌊u₁+(i : ℝ)*σ₁⌋) →
      (1 ≤ S[l-1]'(by omega) ∧ S[l-1]'(by omega) ≤ m-2) →
      |σ₁-r| < δ → |σ₂-r| < δ → (1+η)*(l : ℝ)+(B : ℝ) ≤ T →
      ∀ U : TNEPath, U=runPath S U.origin →
      ∃ A D : ℕ, ((A+D : ℕ) : ℝ) ≤ 12*η*(l : ℝ)+(B : ℝ) ∧
      ∃ Ω : RunEdits m S (mechanicalWord σ₂ u₂ 0 T) (T-l) A D,
        (∀ X ∈ KroneckerBoundedRunEdits.states Ω, ∀ a ∈ X, 1 ≤ a ∧ a ≤ m-2) ∧
        ∃ ζ : LatticePoint, Nonempty (EditProgram m U (translate (MechRunFactor σ₂ u₂ 1 T) ζ) (T-l) A D) := by
  obtain ⟨δ,hδ,B,hB,h⟩ := KroneckerBoundedMechanicalEdits.mechanical_edits
    m r η hm hr hr1 hrM hη.1
  refine ⟨δ,hδ,B,hB,?_⟩
  intro l T hl _ σ₁ σ₂ u₁ u₂ hs _ _ _ S hlen hfirst hlast hprox₁ hprox₂ hbudget U hU
  have hS := source_list S (l-1) (S[l-1]'(by omega)) σ₁ u₁ (by linarith)
    (by omega) hfirst rfl
  obtain ⟨A,D,hcost,Ω,hstates,ζ,hpath⟩ := h l T hl σ₁ σ₂ u₁ u₂
    (S[l-1]'(by omega)) hlast hprox₁ hprox₂ hbudget U (MechRunFactor σ₂ u₂ 1 T) (by rwa [← hS]) rfl
  have hb : ∃ q : RunEdits m S (mechanicalWord σ₂ u₂ 0 T) (T-l) A D,
      ∀ X ∈ KroneckerBoundedRunEdits.states q, ∀ a ∈ X, 1 ≤ a ∧ a ≤ m-2 := by
    rw [hS]
    exact ⟨Ω,hstates⟩
  obtain ⟨q,hq⟩ := hb
  exact ⟨A,D,hcost,q,hq,ζ,hpath⟩

/-- Lemma 6.5 stated using Definition 6.2. -/
theorem mechanical_edits (m : ℕ) (r η : ℝ) (hm : 4 ≤ m)
    (hr : Irrational r) (hr1 : 1 < r) (hrM : r < (m-2 : ℕ))
    (hη : 0 < η ∧ η < 1/4) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧
      ∀ x : Admissible (m-2) r η δ B,
      ∀ U : TNEPath, U=runPath x.S U.origin →
      ∃ A D : ℕ, ((A+D : ℕ) : ℝ) ≤ 12*η*(x.l : ℝ)+(B : ℝ) ∧
      ∃ Ω : RunEdits m x.S (mechanicalWord x.σ₂ x.u₂ 0 x.T) (x.T-x.l) A D,
        (∀ X ∈ KroneckerBoundedRunEdits.states Ω, ∀ a ∈ X, 1 ≤ a ∧ a ≤ m-2) ∧
        ∃ ζ : LatticePoint, Nonempty (EditProgram m U
          (translate (MechRunFactor x.σ₂ x.u₂ 1 x.T) ζ) (x.T-x.l) A D) := by
  obtain ⟨δ,hδ,B,hB,h⟩ := mechanical_edits_expanded m r η hm hr hr1 hrM hη
  refine ⟨δ,hδ,B,hB,?_⟩
  intro x U hU
  exact h x.l x.T x.l_pos x.T_pos x.σ₁ x.σ₂ x.u₁ x.u₂ x.σ₁_ge x.σ₂_ge
    x.u₁_range x.u₂_range x.S x.length_eq x.first_lengths x.last_length
    x.σ₁_near x.σ₂_near x.length_budget U hU

end KroneckerMechanicalEditsStatement
