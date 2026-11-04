import KroneckerGeometricRunEdits
import KroneckerGeometricPrograms
import KroneckerBinaryMechanicalLemma

set_option autoImplicit false
noncomputable section
namespace KroneckerPaperPaths
open KroneckerWordCounts KroneckerBinaryExchangeShapes KroneckerRawBinaryEdits

def Binary (P : TNEPath) : Prop :=
  ∃ rs : List ℕ, rs ≠ [] ∧ P = runPath rs P.origin ∧
    ∀ r ∈ rs, r = 1 ∨ r = 2

theorem binary_runPath_iff (rs : List ℕ) (o : LatticePoint) :
    Binary (runPath rs o) ↔ rs ≠ [] ∧ ∀ r ∈ rs, r = 1 ∨ r = 2 := by
  constructor
  · rintro ⟨ts, ht, he, hl⟩
    have h : rs = ts := runWord_injective (congrArg TNEPath.steps he)
    simpa only [h] using And.intro ht hl
  · rintro ⟨hr, hl⟩
    exact ⟨rs, hr, by rw [runPath_origin rs o hr], hl⟩

theorem insert_runPath_zero (A B : List ℕ) (r : ℕ) (hr : 0 < r) :
    insert (runPath (A ++ B) 0) (runWord A).length (simpleRun r hr) =
      runPath (A ++ r :: B) 0 := by
  apply TNEPath.ext
  · simp [insert, runPath, runWord, List.flatMap_append, simpleRun, KroneckerStack.runShape,
      List.append_assoc]
  · simp [insert, runPath, ofSteps, simpleRun]

theorem exchange_pairRuns (A B : List ℕ) (right : Bool) (o : LatticePoint) :
    exchangeRuns (runPath (A ++ pairRuns right ++ B) o) A.length =
      runPath (A ++ pairRuns (!right) ++ B) o := by
  cases right <;> exact exchangeRuns_adjacent A B _ _ o

inductive BinaryProgram (U : TNEPath) : TNEPath → ℕ → ℕ → Type
  | nil : BinaryProgram U U 0 0
  | insert {A B : List ℕ} {o : LatticePoint} {K k : ℕ}
      (p : BinaryProgram U (runPath (A ++ B) o) K k)
      (r : ℕ) (hr : 1 ≤ r ∧ r ≤ 2) :
      BinaryProgram U (KroneckerPaperPaths.insert (runPath (A ++ B) o)
        (runWord A).length (simpleRun r hr.1)) (K + 1) k
  | exchange {A B : List ℕ} {o : LatticePoint} {K k : ℕ}
      (right : Bool) (p : BinaryProgram U (runPath (A ++ pairRuns right ++ B) o) K k) :
      BinaryProgram U
        (exchangeRuns (runPath (A ++ pairRuns right ++ B) o) A.length) K (k + 1)

theorem rawBinary_realization {R S : List ℕ} {K k : ℕ} (p : RawBinary R S K k)
    (o : LatticePoint) :
    ∃ Q : TNEPath, Nonempty (BinaryProgram (runPath R o) Q K k) ∧ Q.steps = runWord S := by
  induction p with
  | nil => exact ⟨runPath R o, ⟨.nil⟩, rfl⟩
  | @insert A B K k p r hr ih =>
      obtain ⟨Q, ⟨q⟩, hs⟩ := ih
      have he : Q = runPath (A ++ B) Q.origin := by
        have h := ofSteps_self Q
        rw [hs] at h
        exact h.symm
      have q' : BinaryProgram (runPath R o) (runPath (A ++ B) Q.origin) K k := he ▸ q
      refine ⟨insert (runPath (A ++ B) Q.origin) (runWord A).length (simpleRun r hr.1),
        ⟨.insert q' r hr⟩, ?_⟩
      exact congrArg TNEPath.steps (insert_runPath_zero A B r hr.1)
  | @exchange A B K k right p ih =>
      obtain ⟨Q, ⟨q⟩, hs⟩ := ih
      have he : Q = runPath (A ++ pairRuns right ++ B) Q.origin := by
        have h := ofSteps_self Q
        rw [hs] at h
        exact h.symm
      have q' : BinaryProgram (runPath R o)
          (runPath (A ++ pairRuns right ++ B) Q.origin) K k := he ▸ q
      refine ⟨exchangeRuns (runPath (A ++ pairRuns right ++ B) Q.origin) A.length,
        ⟨.exchange right q'⟩, ?_⟩
      rw [exchange_pairRuns]
      rfl

theorem rawBinary_translated_target {R S : List ℕ} {K k : ℕ} (p : RawBinary R S K k)
    (o : LatticePoint) : ∃ w : LatticePoint,
    Nonempty (BinaryProgram (runPath R o) (translate (runPath S 0) w) K k) := by
  obtain ⟨Q, hQ, hs⟩ := rawBinary_realization p o
  refine ⟨Q.origin - (runPath S 0).origin, ?_⟩
  have he := same_steps_translation (P := runPath S 0) (Q := Q) hs.symm
  rwa [he]

theorem binary_mechanical_paths (r η : ℝ) (hr : Irrational r)
    (hrb : 1 < r ∧ r < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧ ∀ s t : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ u v : ℝ, ∀ l N : ℕ, ∀ R : List ℕ,
      KroneckerBinaryMechanicalSource.BinaryMechanicalSource s u l R →
      (1+η)*(l : ℝ)+(B : ℝ) ≤ N →
      ∀ o : LatticePoint, ∃ k, (∃ w : LatticePoint,
        Nonempty (BinaryProgram (runPath R o)
          (translate (runPath (KroneckerMechanicalWords.mechanicalWord t v 0 N) 0) w) (N-l) k)) ∧
        (k : ℝ) ≤ 7*η*(l : ℝ)+B := by
  obtain ⟨δ,hδ,B,hB,h⟩ := KroneckerBinaryMechanicalLemma.binary_mechanical_seven r η hr hrb hη
  refine ⟨δ,hδ,B,hB,?_⟩
  intro s t hs ht u v l N R hR hN o
  obtain ⟨k,⟨p⟩,hk⟩ := h s t hs ht u v l N R hR hN
  exact ⟨k,rawBinary_translated_target p o,hk⟩

end KroneckerPaperPaths
