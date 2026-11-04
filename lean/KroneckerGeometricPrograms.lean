import KroneckerManuscriptMechanicalEdits
import KroneckerGeometricCounts
import KroneckerDeletePrescribedRuns

set_option autoImplicit false

namespace KroneckerPaperPaths

inductive EditProgram (m : ℕ) (U : TNEPath) : TNEPath → ℕ → ℕ → ℕ → Type
  | nil : EditProgram m U U 0 0 0
  | complete {V : TNEPath} {K A D : ℕ} (p : EditProgram m U V K A D)
      (r i : ℕ) (hr : 1 ≤ r ∧ r ≤ m - 2) (hi : i ≤ V.steps.length) :
      EditProgram m U (insert V i (simpleRun r hr.1)) (K + 1) A D
  | north {V : TNEPath} {K A D : ℕ} (p : EditProgram m U V K A D)
      (i : ℕ) (hi : i ≤ V.steps.length) :
      EditProgram m U (insert V i (ofSteps [false] 0)) K (A + 1) D
  | delete {V : TNEPath} {K A D : ℕ} (p : EditProgram m U V K A D)
      (k : Edge V) (hv : V.steps.get k = false) :
      EditProgram m U (deleteVertical V k hv) K A (D + 1)

noncomputable def EditProgram.toRaw {m K A D : ℕ} {U V : TNEPath}
    (p : EditProgram m U V K A D) :
    KroneckerRawMixedPrograms.RawProgram m U.steps V.steps K A D := by
  induction p with
  | nil => exact .nil
  | complete p r i hr hi ih =>
    exact .complete ih r i hr hi
  | north p i hi ih =>
    simpa only [insert_steps, ofSteps_steps, KroneckerListInsertion.insertAt,
      List.append_assoc, List.singleton_append] using
      KroneckerRawMixedPrograms.RawProgram.insert ih i hi
  | delete p k hv ih =>
    rw [deleteVertical_steps]
    exact .delete ih k.val k.isLt (by simpa only [List.get_eq_getElem] using hv)

theorem rawProgram_realization {m K A D : ℕ} {U : TNEPath} {V : List Bool}
    (p : KroneckerRawMixedPrograms.RawProgram m U.steps V K A D) :
    ∃ Q : TNEPath, Nonempty (EditProgram m U Q K A D) ∧ Q.steps = V := by
  induction p with
  | nil => exact ⟨U, ⟨.nil⟩, rfl⟩
  | complete p r i hr hi ih =>
    obtain ⟨Q, ⟨q⟩, hq⟩ := ih
    refine ⟨insert Q i (simpleRun r hr.1), ⟨.complete q r i hr (by rwa [hq])⟩, ?_⟩
    simp only [insert_steps, simpleRun_steps, hq]
    rfl
  | insert p i hi ih =>
    obtain ⟨Q, ⟨q⟩, hq⟩ := ih
    refine ⟨insert Q i (ofSteps [false] 0), ⟨.north q i (by rwa [hq])⟩, ?_⟩
    simp [insert_steps, hq, KroneckerListInsertion.insertAt, List.append_assoc]
  | delete p i hi hv ih =>
    obtain ⟨Q, ⟨q⟩, hq⟩ := ih
    let k : Edge Q := ⟨i, by rwa [hq]⟩
    have hk : Q.steps.get k = false := by simpa [k, hq] using hv
    refine ⟨deleteVertical Q k hk, ⟨.delete q k hk⟩, ?_⟩
    rw [deleteVertical_steps]
    simp only [k, hq]
    rfl

theorem same_steps_translation {P Q : TNEPath} (h : P.steps = Q.steps) :
    translate P (Q.origin - P.origin) = Q := by
  rw [translate_to_origin, h, ofSteps_self]

theorem rawProgram_translated_target {m K A D : ℕ} (U V : TNEPath)
    (p : KroneckerRawMixedPrograms.RawProgram m U.steps V.steps K A D) :
    ∃ t : LatticePoint, Nonempty (EditProgram m U (translate V t) K A D) := by
  obtain ⟨Q, hQ, hs⟩ := rawProgram_realization p
  refine ⟨Q.origin - V.origin, ?_⟩
  rwa [same_steps_translation hs.symm]


theorem mechanical_path_edits (M : ℕ) (r η : ℝ) (hr : Irrational r)
    (hr1 : 1 < r) (hrM : r < M) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, 0 < B ∧ ∀ s t u v : ℝ,
      |s-r| < δ → |t-r| < δ → ∀ n T z : ℕ, (1 ≤ z ∧ z ≤ M) →
      (1+η)*((n : ℝ)+1)+(B : ℝ) ≤ T → ∀ o : LatticePoint,
      ∃ A D : ℕ, ((A+D : ℕ) : ℝ) ≤ 12*η*((n : ℝ)+1)+(B : ℝ) ∧
        ∃ w : LatticePoint, Nonempty (EditProgram (M+2)
          (runPath (KroneckerMechanicalWords.mechanicalWord s u 0 n ++ [z]) o)
          (translate (runPath (KroneckerMechanicalWords.mechanicalWord t v 0 T) 0) w)
          (T-(n+1)) A D) := by
  obtain ⟨δ,hδ,B,h⟩ := KroneckerSparsePrescribedExceptional.mechanical_edit_lemma
    (M+2) r η hr hr1 (by simpa using hrM) hη
  refine ⟨δ,hδ,B+1,by omega,?_⟩
  intro s t u v hs ht n T z hz hT o
  have hT' : (1+η)*((n : ℝ)+1)+(B : ℝ) ≤ T := by
    push_cast at hT
    linarith
  obtain ⟨A,D,hcost,⟨p⟩⟩ := h s t u v hs ht n T z (by simpa using hz) hT'
  refine ⟨A,D,?_,?_⟩
  · push_cast at hcost ⊢
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  · exact rawProgram_translated_target
      (runPath (KroneckerMechanicalWords.mechanicalWord s u 0 n ++ [z]) o)
      (runPath (KroneckerMechanicalWords.mechanicalWord t v 0 T) 0) p

end KroneckerPaperPaths

namespace KroneckerPaperPathGradings
open KroneckerPaperPaths

theorem geometric_composition {m M u v P K A D : ℕ} (hm : 3 ≤ m)
    (hM : M ≤ m-1) (hinsert : 0 < K+A → 4 ≤ m ∧ M ≤ m-2)
    (hu : 1 ≤ u ∧ u ≤ M) (hv : 1 ≤ v ∧ v ≤ M)
    (rs ts left right : List ℕ) (o q w : LatticePoint)
    (p : EditProgram m (runPath rs o) (runPath ts q) K A D)
    (hl : ∀ r ∈ left, 1 ≤ r ∧ r ≤ M)
    (hr : ∀ r ∈ right, 1 ≤ r ∧ r ≤ M)
    (hll : left.length=P) (hrl : right.length=P)
    (hP : K+A+(m+1)*D ≤ P) :
    (connectedCount m (runPath rs o) 0 : ℝ) /
        (KroneckerFiberBudget.fiberBudget m rs.length D : ℝ) ≤
      (connectedCount m (runPath (left++(u::ts++[v])++right) w) 0 : ℝ) := by
  simpa only [connectedCount_runPath] using
    KroneckerDeletePrescribedRuns.prescribed_run_real hm hM hinsert hu hv
      rs ts left right p.toRaw hl hr hll hrl hP

end KroneckerPaperPathGradings
