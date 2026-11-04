import KroneckerGeometricOperations

set_option autoImplicit false

namespace KroneckerPaperPaths

def cyclicLength {P : TNEPath} (u v : Edge P) : ℕ :=
  if u.val ≤ v.val then v.val - u.val + 1 else P.steps.length - u.val + v.val + 1

theorem cyclicLength_pos {P : TNEPath} (u v : Edge P) : 0 < cyclicLength u v := by
  have hu := u.isLt
  have hv := v.isLt
  unfold cyclicLength
  split <;> omega

theorem cyclicLength_le {P : TNEPath} (u v : Edge P) :
    cyclicLength u v ≤ P.steps.length := by
  have hu := u.isLt
  have hv := v.isLt
  unfold cyclicLength
  split <;> omega

def cyclicIndex {P : TNEPath} (u v : Edge P) (k : Fin (cyclicLength u v)) : Edge P :=
  if h : u.val + k.val < P.steps.length then ⟨u.val + k.val, h⟩
  else ⟨u.val + k.val - P.steps.length, by
    have hu := u.isLt
    have hk := k.isLt
    have hl := cyclicLength_le u v
    omega⟩

theorem cyclicIndex_val {P : TNEPath} (u v : Edge P) (k : Fin (cyclicLength u v)) :
    (cyclicIndex u v k).val = if u.val + k.val < P.steps.length then
      u.val + k.val else u.val + k.val - P.steps.length := by
  unfold cyclicIndex
  split <;> rfl

theorem cyclicIndex_injective {P : TNEPath} (u v : Edge P) :
    Function.Injective (cyclicIndex u v) := by
  intro k l he
  have hu := u.isLt
  have hk := k.isLt
  have hl := l.isLt
  have hn := cyclicLength_le u v
  have he' := congrArg Fin.val he
  apply Fin.ext
  unfold cyclicIndex at he'
  split at he' <;> split at he' <;> dsimp at he' <;> omega

@[simp] theorem cyclicIndex_first {P : TNEPath} (u v : Edge P) :
    cyclicIndex u v ⟨0, cyclicLength_pos u v⟩ = u := by
  apply Fin.ext
  simp [cyclicIndex, u.isLt]

@[simp] theorem cyclicIndex_last {P : TNEPath} (u v : Edge P) :
    cyclicIndex u v ⟨cyclicLength u v - 1, by have := cyclicLength_pos u v; omega⟩ = v := by
  have hu := u.isLt
  have hv := v.isLt
  apply Fin.ext
  rw [cyclicIndex_val]
  dsimp only
  unfold cyclicLength
  split_ifs <;> omega

theorem cyclicIndex_first_encounter {P : TNEPath} (u v : Edge P)
    (k : Fin (cyclicLength u v)) (hk : cyclicIndex u v k = v) :
    k.val + 1 = cyclicLength u v := by
  have he := cyclicIndex_injective u v (hk.trans (cyclicIndex_last u v).symm)
  have := congrArg Fin.val he
  have := cyclicLength_pos u v
  dsimp at *
  omega

def cyclicRealization {P : TNEPath} (u v : Edge P) : TNEPath :=
  ofSteps (List.ofFn (fun k : Fin (cyclicLength u v) => P.steps.get (cyclicIndex u v k))) 0

@[simp] theorem cyclicRealization_length {P : TNEPath} (u v : Edge P) :
    (cyclicRealization u v).steps.length = cyclicLength u v := by
  simp [cyclicRealization]

@[simp] theorem cyclicRealization_origin {P : TNEPath} (u v : Edge P) :
    (cyclicRealization u v).origin = 0 := by simp [cyclicRealization, ofSteps]

theorem cyclicRealization_nonempty {P : TNEPath} (u v : Edge P) :
    cyclicRealization u v ≠ empty := by
  intro he
  have h := congrArg (fun P : TNEPath => P.steps.length) he
  have := cyclicLength_pos u v
  simp at h
  omega

def cyclicRealizationIndex {P : TNEPath} (u v : Edge P) :
    Edge (cyclicRealization u v) ≃ Fin (cyclicLength u v) :=
  finCongr (cyclicRealization_length u v)

noncomputable def cyclicAmbientEdge {P : TNEPath} (u v : Edge P)
    (w : GeomEdge (cyclicRealization u v)) : GeomEdge P :=
  edgeEquiv P (cyclicIndex u v (cyclicRealizationIndex u v
    ((edgeEquiv (cyclicRealization u v)).symm w)))

theorem cyclicAmbientEdge_injective {P : TNEPath} (u v : Edge P) :
    Function.Injective (cyclicAmbientEdge u v) :=
  (edgeEquiv P).injective.comp ((cyclicIndex_injective u v).comp
    ((cyclicRealizationIndex u v).injective.comp
      (edgeEquiv (cyclicRealization u v)).symm.injective))

set_option backward.isDefEq.respectTransparency false in
theorem cyclicRealization_direction {P : TNEPath} (u v : Edge P)
    (k : Edge (cyclicRealization u v)) :
    (edge (cyclicRealization u v) k).2 - (edge (cyclicRealization u v) k).1 =
      (edge P (cyclicIndex u v (cyclicRealizationIndex u v k))).2 -
        (edge P (cyclicIndex u v (cyclicRealizationIndex u v k))).1 := by
  rw [edge_direction, edge_direction]
  apply congrArg stepVector
  simp only [cyclicRealization, ofSteps_steps, List.get_eq_getElem, List.getElem_ofFn]
  congr 2

end KroneckerPaperPaths

namespace KroneckerPaperPathGradings
noncomputable section
open KroneckerPaperPaths

def cyclicGrading {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) :
    Grading m (cyclicRealization u v) := g ∘ cyclicAmbientEdge u v

def cyclicColoredGrading {m : ℕ} {P : TNEPath} (c : ColoredGrading m P)
    (u v : Edge P) : ColoredGrading m (cyclicRealization u v) :=
  ⟨cyclicGrading c.1 u v, fun w => c.2 (cyclicAmbientEdge u v w)⟩

theorem cyclicGrading_apply {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P)
    (w : GeomEdge (cyclicRealization u v)) :
    cyclicGrading g u v w = g (cyclicAmbientEdge u v w) := rfl

theorem cyclicColoredGrading_color {m : ℕ} {P : TNEPath} (c : ColoredGrading m P)
    (u v : Edge P) (w : GeomEdge (cyclicRealization u v)) :
    ((cyclicColoredGrading c u v).2 w).val = (c.2 (cyclicAmbientEdge u v w)).val := rfl

end
end KroneckerPaperPathGradings
