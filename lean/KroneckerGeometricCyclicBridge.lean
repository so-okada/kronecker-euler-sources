import KroneckerGeometricCyclic
import KroneckerPaperCompatibility

set_option autoImplicit false

namespace KroneckerPaperPaths

theorem cyclicIndex_mod {P : TNEPath} (u v : Edge P) (k : Fin (cyclicLength u v)) :
    (cyclicIndex u v k).val = (u.val + k.val) % P.steps.length := by
  rw [cyclicIndex_val]
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · have hu := u.isLt
    have hk := k.isLt
    have hl := cyclicLength_le u v
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem cyclicRealization_steps {P : TNEPath} (u v : Edge P) :
    (cyclicRealization u v).steps = (P.steps.rotate u.val).take (cyclicLength u v) := by
  apply List.ext_getElem
  · simp only [cyclicRealization_length, List.length_take, List.length_rotate,
      Nat.min_eq_left (cyclicLength_le u v)]
  · intro k hk hk'
    simp only [cyclicRealization, ofSteps_steps, List.getElem_ofFn,
      List.get_eq_getElem, List.getElem_take]
    rw [List.getElem_rotate]
    congr 1
    rw [cyclicIndex_mod, Nat.add_comm]

theorem cyclicLength_lift {P : TNEPath} (u v : Edge P) :
    u.val + cyclicLength u v =
      KroneckerSourceCompatibility.lift P.steps.length u.val v.val + 1 := by
  have hu := u.isLt
  unfold cyclicLength KroneckerSourceCompatibility.lift
  split_ifs <;> omega

theorem cyclicRealization_eq_singleton {P : TNEPath} (u : Edge P) :
    cyclicRealization u u = ofSteps [P.steps.get u] 0 := by
  apply TNEPath.ext
  · rw [cyclicRealization_steps]
    simp only [cyclicLength, le_refl, ↓reduceIte, Nat.sub_self, Nat.zero_add]
    rw [List.take_one]
    simp [List.head?_rotate u.isLt, List.get_eq_getElem]
  · simp [cyclicRealization_origin, ofSteps]

end KroneckerPaperPaths

namespace KroneckerPaperPathGradings
noncomputable section
open KroneckerPaperPaths KroneckerSourceGradingDictionary

def geometricTrace {m : ℕ} {P : TNEPath} (g : Grading m P) : ℕ → KroneckerStack.Edge :=
  rawTrace (KroneckerWordCounts.pathShape P.steps) (gradingEquiv m P g)

theorem geometricTrace_periodic {m : ℕ} {P : TNEPath}
    (g : Grading m P) (i : ℕ) :
    geometricTrace g (i + P.steps.length) = geometricTrace g i := by
  simp [geometricTrace, rawTrace, Nat.add_mod_right]

theorem geometricTrace_edge {m : ℕ} {P : TNEPath} (g : Grading m P) (k : Edge P) :
    geometricTrace g k.val =
      if P.steps.get k then KroneckerStack.Edge.H (g (edgeEquiv P k)).val
      else KroneckerStack.Edge.V (g (edgeEquiv P k)).val := by
  rw [geometricTrace, raw_before _ _ k.val k.isLt]
  simp [KroneckerWordCounts.pathShape, List.getD, k.isLt,
    gradingEquiv, List.get_eq_getElem]

theorem cyclicGrading_occurrence {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P)
    (k : Edge (cyclicRealization u v)) :
    gradingEquiv m (cyclicRealization u v) (cyclicGrading g u v) k =
      g (edgeEquiv P (cyclicIndex u v (cyclicRealizationIndex u v k))) := by
  simp [gradingEquiv, cyclicGrading, cyclicAmbientEdge]

theorem geometricTrace_mod {m : ℕ} {P : TNEPath} (g : Grading m P) (i : ℕ) :
    geometricTrace g (i % P.steps.length) = geometricTrace g i := by
  simp [geometricTrace, rawTrace]

set_option backward.isDefEq.respectTransparency false in
theorem cyclicTrace_correspondence {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P)
    (k : Edge (cyclicRealization u v)) :
    geometricTrace (cyclicGrading g u v) k.val = geometricTrace g (u.val + k.val) := by
  rw [geometricTrace_edge]
  have hg := cyclicGrading_occurrence g u v k
  change (if (cyclicRealization u v).steps.get k then
    KroneckerStack.Edge.H ((gradingEquiv m (cyclicRealization u v) (cyclicGrading g u v)) k).val
    else KroneckerStack.Edge.V ((gradingEquiv m (cyclicRealization u v) (cyclicGrading g u v)) k).val) = _
  rw [hg]
  have hs : (cyclicRealization u v).steps.get k =
      P.steps.get (cyclicIndex u v (cyclicRealizationIndex u v k)) := by
    simp only [cyclicRealization, ofSteps_steps, List.get_eq_getElem, List.getElem_ofFn]
    congr 2
  rw [hs, ← geometricTrace_edge]
  have hk : (cyclicIndex u v (cyclicRealizationIndex u v k)).val =
      (u.val + k.val) % P.steps.length := cyclicIndex_mod u v _
  rw [hk, geometricTrace_mod]

end
end KroneckerPaperPathGradings
