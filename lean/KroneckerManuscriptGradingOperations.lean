import KroneckerNaturalPathGradings

/-! Restriction and concatenation preserve both grades and one-based colors.
Edge copies are identified by traversal positions, including translated paths. -/
noncomputable section
set_option autoImplicit false
namespace KroneckerManuscriptGradingOperations
open KroneckerPaperPaths KroneckerNaturalPathGradings

def restrictColors {m : ℕ} {P : TNEPath} {g : Grading P}
    (c : ColorFiber m g) (i j : ℕ) (hj : j ≤ P.steps.length) :
    ColorFiber m (restrictGrading g i j hj) :=
  fun e => c (edgeEquiv P (subpathEdge P i j hj ((edgeEquiv _).symm e)))

def restrictColored {m : ℕ} {P : TNEPath} (c : ColoredGrading m P)
    (i j : ℕ) (hj : j ≤ P.steps.length) : ColoredGrading m (subpath P i j) :=
  ⟨restrictGrading c.1 i j hj, restrictColors c.2 i j hj⟩

theorem restriction_values {m : ℕ} {P : TNEPath} (c : ColoredGrading m P)
    (i j : ℕ) (hj : j ≤ P.steps.length) (e : GeomEdge (subpath P i j)) :
    (restrictColored c i j hj).1 e = c.1 (edgeEquiv P (subpathEdge P i j hj ((edgeEquiv _).symm e))) ∧
    ((restrictColored c i j hj).2 e).val = (c.2 (edgeEquiv P (subpathEdge P i j hj ((edgeEquiv _).symm e)))).val :=
  ⟨rfl,rfl⟩

def concatEdge (U V : TNEPath) : (GeomEdge U ⊕ GeomEdge V) ≃ GeomEdge (concat U V) :=
  (Equiv.sumCongr (edgeEquiv U).symm (edgeEquiv V).symm).trans
    (finSumFinEquiv.trans ((finCongr (by simp)).trans (edgeEquiv (concat U V))))

def leftCopy (U V : TNEPath) (e : GeomEdge U) : GeomEdge (concat U V) :=
  concatEdge U V (.inl e)
def rightCopy (U V : TNEPath) (e : GeomEdge V) : GeomEdge (concat U V) :=
  concatEdge U V (.inr e)

def concatGrading {U V : TNEPath} (g : Grading U) (h : Grading V) : Grading (concat U V) :=
  fun e => Sum.elim g h ((concatEdge U V).symm e)

def concatColors {m : ℕ} {U V : TNEPath} {g : Grading U} {h : Grading V}
    (c : ColorFiber m g) (d : ColorFiber m h) : ColorFiber m (concatGrading g h) :=
  fun e => ⟨Sum.elim (fun u => (c u).val) (fun v => (d v).val) ((concatEdge U V).symm e), by
    dsimp [concatGrading]
    cases he : (concatEdge U V).symm e with
    | inl u => exact (c u).property
    | inr v => exact (d v).property⟩

def concatColored {m : ℕ} {U V : TNEPath}
    (c : ColoredGrading m U) (d : ColoredGrading m V) : ColoredGrading m (concat U V) :=
  ⟨concatGrading c.1 d.1, concatColors c.2 d.2⟩

theorem concat_left_values {m : ℕ} {U V : TNEPath}
    (c : ColoredGrading m U) (d : ColoredGrading m V) (e : GeomEdge U) :
    (concatColored c d).1 (leftCopy U V e) = c.1 e ∧
    ((concatColored c d).2 (leftCopy U V e)).val = (c.2 e).val := by
  simp [concatColored,concatGrading,concatColors,leftCopy]

theorem concat_right_values {m : ℕ} {U V : TNEPath}
    (c : ColoredGrading m U) (d : ColoredGrading m V) (e : GeomEdge V) :
    (concatColored c d).1 (rightCopy U V e) = d.1 e ∧
    ((concatColored c d).2 (rightCopy U V e)).val = (d.2 e).val := by
  simp [concatColored,concatGrading,concatColors,rightCopy]

theorem leftCopy_position (U V : TNEPath) (e : GeomEdge U) :
    ((edgeEquiv (concat U V)).symm (leftCopy U V e)).val = ((edgeEquiv U).symm e).val := by
  simp [leftCopy,concatEdge,finSumFinEquiv]
  exact congrArg Fin.val ((edgeEquiv (concat U V)).symm_apply_apply _)

theorem rightCopy_position (U V : TNEPath) (e : GeomEdge V) :
    ((edgeEquiv (concat U V)).symm (rightCopy U V e)).val = U.steps.length + ((edgeEquiv V).symm e).val := by
  simp [rightCopy,concatEdge,finSumFinEquiv]
  exact congrArg Fin.val ((edgeEquiv (concat U V)).symm_apply_apply _)

def emptyColored (m : ℕ) : ColoredGrading m empty :=
  ⟨fun e => Fin.elim0 ((edgeEquiv empty).symm e), fun e => Fin.elim0 ((edgeEquiv empty).symm e)⟩

structure Factor (m : ℕ) where
  path : TNEPath
  colored : ColoredGrading m path

def concatenate {m : ℕ} : List (Factor m) → Factor m
  | [] => ⟨empty, emptyColored m⟩
  | f :: fs => let q := concatenate fs
               ⟨concat f.path q.path, concatColored f.colored q.colored⟩

theorem concatenate_steps {m : ℕ} (fs : List (Factor m)) :
    (concatenate fs).path.steps = fs.flatMap (fun f => f.path.steps) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [concatenate,ih]

end KroneckerManuscriptGradingOperations

#print axioms KroneckerManuscriptGradingOperations.restrictColors
#print axioms KroneckerManuscriptGradingOperations.restrictColored
#print axioms KroneckerManuscriptGradingOperations.restriction_values
#print axioms KroneckerManuscriptGradingOperations.concatEdge
#print axioms KroneckerManuscriptGradingOperations.concatGrading
#print axioms KroneckerManuscriptGradingOperations.concatColors
#print axioms KroneckerManuscriptGradingOperations.concatColored
#print axioms KroneckerManuscriptGradingOperations.concat_left_values
#print axioms KroneckerManuscriptGradingOperations.concat_right_values
#print axioms KroneckerManuscriptGradingOperations.leftCopy_position
#print axioms KroneckerManuscriptGradingOperations.rightCopy_position
#print axioms KroneckerManuscriptGradingOperations.emptyColored
#print axioms KroneckerManuscriptGradingOperations.concatenate
#print axioms KroneckerManuscriptGradingOperations.concatenate_steps
