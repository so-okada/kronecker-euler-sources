import KroneckerPaperPaths
import KroneckerPaperColors

set_option autoImplicit false

namespace KroneckerPaperPathGradings
noncomputable section

open KroneckerPaperPaths
open KroneckerWeights KroneckerSourceGradingDictionary
open scoped BigOperators

abbrev Grading (m : ℕ) (P : TNEPath) := GeomEdge P → Fin (m + 1)

abbrev ColorFiber {m : ℕ} {P : TNEPath} (g : Grading m P) :=
  (v : GeomEdge P) → {c : ℕ // 1 ≤ c ∧ c ≤ Nat.choose m (g v).val}

abbrev ColoredGrading (m : ℕ) (P : TNEPath) :=
  (g : Grading m P) × ColorFiber g

private theorem coloredFunction_ext {m : ℕ} {α : Type}
    {c d : (g : α → Fin (m + 1)) ×
      ((v : α) → {k : ℕ // 1 ≤ k ∧ k ≤ Nat.choose m (g v).val})}
    (hg : c.1 = d.1) (hc : ∀ v, (c.2 v).val = (d.2 v).val) : c = d := by
  rcases c with ⟨g,c⟩
  rcases d with ⟨h,d⟩
  dsimp at hg
  subst h
  have hcd : c = d := by
    funext v
    apply Subtype.ext
    exact hc v
  cases hcd
  rfl

def gradingEquiv (m : ℕ) (P : TNEPath) : Grading m P ≃ Grades m P.steps.length where
  toFun g k := g (edgeEquiv P k)
  invFun g v := g ((edgeEquiv P).symm v)
  left_inv g := by funext v; simp
  right_inv g := by funext k; simp

def coloredGradingEquiv (m : ℕ) (P : TNEPath) :
    ColoredGrading m P ≃ KroneckerPaperColors.PaperColoredGrading m P.steps.length where
  toFun c := ⟨gradingEquiv m P c.1, fun k => c.2 (edgeEquiv P k)⟩
  invFun c := ⟨(gradingEquiv m P).symm c.1,
    fun v => c.2 ((edgeEquiv P).symm v)⟩
  left_inv c := by
    apply coloredFunction_ext
    · exact (gradingEquiv m P).symm_apply_apply c.1
    · intro v
      exact congrArg (fun w => (c.2 w).val) ((edgeEquiv P).apply_symm_apply v)
  right_inv c := by
    apply coloredFunction_ext
    · exact (gradingEquiv m P).apply_symm_apply c.1
    · intro k
      exact congrArg (fun j => (c.2 j).val) ((edgeEquiv P).symm_apply_apply k)

@[simp] theorem coloredGradingEquiv_grades {m : ℕ} {P : TNEPath}
    (c : ColoredGrading m P) :
    (coloredGradingEquiv m P c).1 = gradingEquiv m P c.1 := rfl

@[simp] theorem coloredGradingEquiv_symm_grades {m : ℕ} {P : TNEPath}
    (c : KroneckerPaperColors.PaperColoredGrading m P.steps.length) :
    gradingEquiv m P ((coloredGradingEquiv m P).symm c).1 = c.1 := by
  exact (gradingEquiv m P).apply_symm_apply c.1

def translateEdge (P : TNEPath) (t : ℤ × ℤ) :
    GeomEdge P ≃ GeomEdge (translate P t) :=
  (edgeEquiv P).symm.trans (edgeEquiv (translate P t))

@[simp] theorem translateEdge_occurrence (P : TNEPath) (t : ℤ × ℤ)
    (k : Edge P) :
    translateEdge P t (edgeEquiv P k) = edgeEquiv (translate P t) k := by
  change edgeEquiv (translate P t) ((edgeEquiv P).symm (edgeEquiv P k)) = _
  exact congrArg (edgeEquiv (translate P t)) ((edgeEquiv P).symm_apply_apply k)

theorem translateEdge_geometry (P : TNEPath) (t : ℤ × ℤ) (v : GeomEdge P) :
    (translateEdge P t v).val = (v.val.1 + t, v.val.2 + t) := by
  obtain ⟨k, rfl⟩ := (edgeEquiv P).surjective v
  rw [translateEdge_occurrence]
  exact edge_translate P t k

def translateGrading {m : ℕ} {P : TNEPath} (g : Grading m P) (t : ℤ × ℤ) :
    Grading m (translate P t) := fun v => g ((translateEdge P t).symm v)

def translateColorFunction {m : ℕ} {P : TNEPath} {g : Grading m P}
    (c : ColorFiber g) (t : ℤ × ℤ) : ColorFiber (translateGrading g t) :=
  fun v => c ((translateEdge P t).symm v)

def translateColoredGrading {m : ℕ} {P : TNEPath}
    (c : ColoredGrading m P) (t : ℤ × ℤ) : ColoredGrading m (translate P t) :=
  ⟨translateGrading c.1 t, translateColorFunction c.2 t⟩

@[simp] theorem translateGrading_apply {m : ℕ} {P : TNEPath}
    (g : Grading m P) (t : ℤ × ℤ) (v : GeomEdge P) :
    translateGrading g t (translateEdge P t v) = g v := by
  simp [translateGrading]

@[simp] theorem translateColorFunction_apply {m : ℕ} {P : TNEPath}
    {g : Grading m P} (c : ColorFiber g) (t : ℤ × ℤ) (v : GeomEdge P) :
    (translateColorFunction c t (translateEdge P t v)).val = (c v).val := by
  exact congrArg (fun w => (c w).val) ((translateEdge P t).symm_apply_apply v)

@[simp] theorem translateGrading_occurrences {m : ℕ} {P : TNEPath}
    (g : Grading m P) (t : ℤ × ℤ) :
    gradingEquiv m (translate P t) (translateGrading g t) = gradingEquiv m P g := by
  funext k
  exact congrArg (fun j => g (edgeEquiv P j))
    ((edgeEquiv (translate P t)).symm_apply_apply k)

@[simp] theorem translateColoredGrading_occurrences {m : ℕ} {P : TNEPath}
    (c : ColoredGrading m P) (t : ℤ × ℤ) :
    coloredGradingEquiv m (translate P t) (translateColoredGrading c t) =
      coloredGradingEquiv m P c := by
  apply coloredFunction_ext
  · exact translateGrading_occurrences c.1 t
  · intro k
    exact congrArg (fun j => (c.2 (edgeEquiv P j)).val)
      ((edgeEquiv (translate P t)).symm_apply_apply k)

private theorem coloredGrading_heq {m : ℕ} {P Q : TNEPath} (h : P = Q)
    {c : ColoredGrading m P} {d : ColoredGrading m Q}
    (hc : HEq (coloredGradingEquiv m P c) (coloredGradingEquiv m Q d)) : HEq c d := by
  subst Q
  exact heq_of_eq ((coloredGradingEquiv m P).injective (eq_of_heq hc))

@[simp] theorem translateColoredGrading_zero {m : ℕ} {P : TNEPath}
    (c : ColoredGrading m P) : HEq (translateColoredGrading c 0) c := by
  apply coloredGrading_heq (translate_zero P)
  simp only [translateColoredGrading_occurrences]
  rfl

theorem translateColoredGrading_add {m : ℕ} {P : TNEPath}
    (c : ColoredGrading m P) (s t : ℤ × ℤ) :
    HEq (translateColoredGrading (translateColoredGrading c s) t)
      (translateColoredGrading c (s + t)) := by
  apply coloredGrading_heq (translate_add P s t)
  simp only [translateColoredGrading_occurrences]
  rfl

@[simp] theorem translateColoredGrading_neg {m : ℕ} {P : TNEPath}
    (c : ColoredGrading m P) (t : ℤ × ℤ) :
    HEq (translateColoredGrading (translateColoredGrading c t) (-t)) c := by
  apply coloredGrading_heq (translate_neg P t)
  simp only [translateColoredGrading_occurrences]
  rfl

def translationEquiv (m : ℕ) (P : TNEPath) (t : ℤ × ℤ) :
    ColoredGrading m P ≃ ColoredGrading m (translate P t) :=
  (coloredGradingEquiv m P).trans (coloredGradingEquiv m (translate P t)).symm

@[simp] theorem translationEquiv_apply {m : ℕ} {P : TNEPath}
    (t : ℤ × ℤ) (c : ColoredGrading m P) :
    translationEquiv m P t c = translateColoredGrading c t := by
  change (coloredGradingEquiv m (translate P t)).symm (coloredGradingEquiv m P c) = _
  calc
    _ = (coloredGradingEquiv m (translate P t)).symm
        (coloredGradingEquiv m (translate P t) (translateColoredGrading c t)) :=
      congrArg _ (translateColoredGrading_occurrences c t).symm
    _ = _ := (coloredGradingEquiv m (translate P t)).symm_apply_apply _

@[simp] theorem translationEquiv_left_inverse {m : ℕ} {P : TNEPath}
    (t : ℤ × ℤ) (c : ColoredGrading m P) :
    (translationEquiv m P t).symm (translateColoredGrading c t) = c := by
  rw [← translationEquiv_apply]
  exact (translationEquiv m P t).symm_apply_apply c

@[simp] theorem translationEquiv_right_inverse {m : ℕ} {P : TNEPath}
    (t : ℤ × ℤ) (c : ColoredGrading m (translate P t)) :
    translateColoredGrading ((translationEquiv m P t).symm c) t = c := by
  rw [← translationEquiv_apply]
  exact (translationEquiv m P t).apply_symm_apply c

theorem translationEquiv_symm_apply {m : ℕ} {P : TNEPath}
    (t : ℤ × ℤ) (c : ColoredGrading m (translate P t)) :
    HEq ((translationEquiv m P t).symm c) (translateColoredGrading c (-t)) := by
  have h := translateColoredGrading_neg ((translationEquiv m P t).symm c) t
  rw [translationEquiv_right_inverse] at h
  exact h.symm

def boundaryBalance {m : ℕ} {P : TNEPath} (g : Grading m P)
    (i : Fin (P.steps.length + 1)) : ℤ :=
  KroneckerCompatibility.balance
    (rawTrace (KroneckerWordCounts.pathShape P.steps) (gradingEquiv m P g)) i.val

def edgeBalance {m : ℕ} {P : TNEPath} (g : Grading m P) (v : GeomEdge P) : ℤ :=
  boundaryBalance g ⟨((edgeEquiv P).symm v).val + 1, by
    have h := ((edgeEquiv P).symm v).isLt
    omega⟩

def surplus {m : ℕ} {P : TNEPath} (g : Grading m P) : ℤ :=
  boundaryBalance g ⟨P.steps.length, Nat.lt_succ_self _⟩ - 1

def ConnectedGrade {m : ℕ} {P : TNEPath} (d : ℕ) (g : Grading m P) : Prop :=
  KroneckerPaperColors.ConnectedGrade
    (KroneckerWordCounts.pathShape P.steps) d (gradingEquiv m P g)

theorem connectedGrade_surplus {m : ℕ} {P : TNEPath} {d : ℕ}
    {g : Grading m P} (h : ConnectedGrade d g) : surplus g = (d : ℤ) := by
  obtain ⟨_, hd⟩ := h
  unfold surplus boundaryBalance
  rw [hd]
  omega

abbrev ConnectedColorings (m : ℕ) (P : TNEPath) (d : ℕ) :=
  {c : ColoredGrading m P // ConnectedGrade d c.1}

def connectedCount (m : ℕ) (P : TNEPath) (d : ℕ) : ℕ :=
  Nat.card (ConnectedColorings m P d)

theorem boundaryBalance_formula {m : ℕ} {P : TNEPath}
    (g : Grading m P) (i : Fin (P.steps.length + 1)) :
    boundaryBalance g i =
      KroneckerCompatibility.intervalSum KroneckerCompatibility.hCount
        (rawTrace (KroneckerWordCounts.pathShape P.steps) (gradingEquiv m P g)) 0 i.val -
      KroneckerCompatibility.intervalSum KroneckerCompatibility.vGrade
        (rawTrace (KroneckerWordCounts.pathShape P.steps) (gradingEquiv m P g)) 0 i.val := by
  simpa only [Nat.zero_add, KroneckerCompatibility.balance,
    KroneckerCompatibility.walk, sub_zero, boundaryBalance] using
    KroneckerCompatibility.balance_interval
      (rawTrace (KroneckerWordCounts.pathShape P.steps) (gradingEquiv m P g)) 0 i.val

theorem boundaryBalance_geometric_prefix_sum {m : ℕ} {P : TNEPath}
    (g : Grading m P) (i : Fin (P.steps.length + 1)) :
    boundaryBalance g i = ∑ k : Fin i.val,
      if KroneckerWordCounts.pathShape P.steps k.val then (1 : ℤ)
      else -((g (edgeEquiv P
        ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.le_of_lt_succ i.isLt)⟩)).val : ℤ) := by
  have h := KroneckerCompatibility.walk_interval KroneckerStack.Edge.credit
    (rawTrace (KroneckerWordCounts.pathShape P.steps) (gradingEquiv m P g)) 0 i.val
  simp only [Nat.zero_add, KroneckerCompatibility.walk, sub_zero,
    KroneckerCompatibility.intervalSum] at h
  unfold boundaryBalance KroneckerCompatibility.balance
  rw [h, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [raw_before _ _ k.val
    (Nat.lt_of_lt_of_le k.isLt (Nat.le_of_lt_succ i.isLt))]
  cases KroneckerWordCounts.pathShape P.steps k.val <;> rfl

theorem surplus_formula {m : ℕ} {P : TNEPath} (g : Grading m P) :
    surplus g = KroneckerColoring.HEdges (KroneckerWordCounts.pathShape P.steps) P.steps.length - 1 -
      KroneckerColoring.VTotal (KroneckerWordCounts.pathShape P.steps)
        (representative (gradingEquiv m P g)) := by
  exact KroneckerPaperColors.surplus_formula
    (KroneckerWordCounts.pathShape P.steps) (gradingEquiv m P g)

@[simp] theorem boundaryBalance_translate {m : ℕ} {P : TNEPath}
    (g : Grading m P) (t : ℤ × ℤ) (i : Fin (P.steps.length + 1)) :
    boundaryBalance (translateGrading g t) i = boundaryBalance g i := by
  change KroneckerCompatibility.balance
    (rawTrace (KroneckerWordCounts.pathShape P.steps)
      (gradingEquiv m (translate P t) (translateGrading g t))) i.val = _
  rw [translateGrading_occurrences]
  rfl

@[simp] theorem edgeBalance_translate {m : ℕ} {P : TNEPath}
    (g : Grading m P) (t : ℤ × ℤ) (v : GeomEdge P) :
    edgeBalance (translateGrading g t) (translateEdge P t v) = edgeBalance g v := by
  have hv : (edgeEquiv (translate P t)).symm (translateEdge P t v) =
      (edgeEquiv P).symm v :=
    (edgeEquiv (translate P t)).symm_apply_apply ((edgeEquiv P).symm v)
  unfold edgeBalance
  simp only [hv]
  exact boundaryBalance_translate g t _

@[simp] theorem surplus_translate {m : ℕ} {P : TNEPath}
    (g : Grading m P) (t : ℤ × ℤ) :
    surplus (translateGrading g t) = surplus g := by
  simp [surplus]

@[simp] theorem connectedGrade_translate {m : ℕ} {P : TNEPath}
    (g : Grading m P) (t : ℤ × ℤ) (d : ℕ) :
    ConnectedGrade d (translateGrading g t) ↔ ConnectedGrade d g := by
  change KroneckerPaperColors.ConnectedGrade (KroneckerWordCounts.pathShape P.steps) d
    (gradingEquiv m (translate P t) (translateGrading g t)) ↔ _
  rw [translateGrading_occurrences]
  rfl

def connectedColoringEquiv (m : ℕ) (P : TNEPath) (d : ℕ) :
    ConnectedColorings m P d ≃
      @KroneckerPaperColors.ConnectedColorings m P.steps.length
        (KroneckerWordCounts.pathShape P.steps) d where
  toFun c := ⟨coloredGradingEquiv m P c.val, c.property⟩
  invFun c := ⟨(coloredGradingEquiv m P).symm c.val, by
    simpa only [ConnectedGrade, coloredGradingEquiv_symm_grades] using c.property⟩
  left_inv c := by
    apply Subtype.ext
    exact (coloredGradingEquiv m P).left_inv c.val
  right_inv c := by
    apply Subtype.ext
    exact (coloredGradingEquiv m P).right_inv c.val

def connectedTranslationEquiv (m : ℕ) (P : TNEPath) (t : ℤ × ℤ) (d : ℕ) :
    ConnectedColorings m P d ≃ ConnectedColorings m (translate P t) d :=
  (connectedColoringEquiv m P d).trans (connectedColoringEquiv m (translate P t) d).symm

@[simp] theorem connectedTranslationEquiv_apply {m : ℕ} {P : TNEPath}
    (t : ℤ × ℤ) (d : ℕ) (c : ConnectedColorings m P d) :
    (connectedTranslationEquiv m P t d c).val = translateColoredGrading c.val t := by
  exact translationEquiv_apply t c.val

theorem connectedCount_translate (m : ℕ) (P : TNEPath) (t : ℤ × ℤ) (d : ℕ) :
    connectedCount m P d = connectedCount m (translate P t) d :=
  Nat.card_congr (connectedTranslationEquiv m P t d)

theorem connectedCount_eq_pathCount (m : ℕ) (P : TNEPath) (d : ℕ) :
    connectedCount m P d = KroneckerWordCounts.pathCount m P.steps d := by
  rw [connectedCount, Nat.card_congr (connectedColoringEquiv m P d)]
  exact KroneckerPaperColors.literal_count_eq_pathCount m d P.steps

@[simp] theorem connectedCount_empty (m d : ℕ) : connectedCount m empty d = 0 := by
  rw [connectedCount_eq_pathCount]
  exact KroneckerWordCounts.pathCount_nil m d

#print axioms connectedCount_translate
#print axioms connectedCount_eq_pathCount

end
end KroneckerPaperPathGradings
