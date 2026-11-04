import KroneckerGeometricPredecessor

set_option autoImplicit false
noncomputable section

namespace KroneckerPaperPathGradings
open KroneckerPaperPaths

/-- Definition 2.6(1): for each vertical edge, the assigned edge has the
greatest index among the horizontal edges satisfying (a) and (b).
Lean indices are zero-based; manuscript edge indices are one-based. -/
def IsHPrecursor {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) : Prop :=
  ∀ v : Vertical P, IsGreatest
    {i : ℕ | ∃ x : Horizontal P, i = edgeIndex x.val ∧
      edgeIndex x.val < edgeIndex v.val ∧
      assignmentCount p (edgeIndex v.val) x < (g x.val).val}
    (edgeIndex (p v).val)

/-- The shortened last-edge condition is equivalent to the original three
conditions, for the same geometric path, grading, and assignment map. -/
theorem isHPrecursor_iff {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) :
    IsHPrecursor g p ↔ IsPredecessor g p := by
  constructor
  · intro hp v
    obtain ⟨x, hx, hbefore, hcap⟩ := (hp v).1
    have he : x = p v := by
      apply Subtype.ext
      apply (edgeEquiv P).symm.injective
      apply Fin.ext
      exact hx.symm
    subst x
    refine ⟨hbefore, hcap, ?_⟩
    intro y hy hc
    exact (hp v).2 ⟨y, rfl, hy, hc⟩
  · intro hp v
    refine ⟨⟨p v, rfl, (hp v).1, (hp v).2.1⟩, ?_⟩
    rintro i ⟨x, rfl, hx, hc⟩
    exact (hp v).2.2 x hx hc

theorem hPrecursor_unique {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p q : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (hq : IsHPrecursor g q) : p = q :=
  predecessor_unique g p q ((isHPrecursor_iff g p).mp hp)
    ((isHPrecursor_iff g q).mp hq)

theorem hPrecursor_exists_iff {m : ℕ} {P : TNEPath} (g : Grading m P) :
    (∃ p, IsHPrecursor g p) ↔ ∀ k ≤ P.steps.length,
      KroneckerPredecessor.verticalCount (occurrenceWord g) k ≤
        KroneckerPredecessor.horizontalGrade (occurrenceWord g) k := by
  simpa only [isHPrecursor_iff] using predecessor_exists_iff g

/-- Definition 2.6(2): the node has the same endpoints and subpath. -/
theorem hPrecursor_nodePath_edges {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (x : Horizontal P) (v : Vertical P) (h : IsNode g p x v) :
    (nodePath x v).steps = (P.steps.drop (edgeIndex x.val)).take
      (edgeIndex v.val + 1 - edgeIndex x.val) ∧
    (nodePath x v).origin = vertex P (edgeIndex x.val) :=
  nodePath_edges g p ((isHPrecursor_iff g p).mp hp) x v h

/-- Definition 2.6(3): natural-valued debt equals the manuscript's integer
subtraction under the h-precursor condition. -/
theorem hPrecursor_debt_formula {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (x : Horizontal P) (k : ℕ) (hk : k ≤ P.steps.length) :
    (Debt g p x k : ℤ) = (g x.val).val - (assignmentCount p k x : ℤ) := by
  have h := debt_and_assignments g p ((isHPrecursor_iff g p).mp hp) x k hk
  have hz : (Debt g p x k : ℤ) + (assignmentCount p k x : ℤ) =
      ((g x.val).val : ℤ) := by exact_mod_cast h
  omega

end KroneckerPaperPathGradings
