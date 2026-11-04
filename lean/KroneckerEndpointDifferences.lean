import KroneckerCurrentShadowDefinitions
import InsertionConventionCheck

/-! Endpoint and grading-difference formulas for the manuscript of 22 October
2026. Geometric edges are kept distinct from their occurrence indices.
NE-path words in exchange and rotation are based at the origin. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace KroneckerPaperPaths

theorem simpleRun_Start_pt (j : ℕ) (hj : 0 < j) (h : simpleRun j hj ≠ empty) :
    Start_pt (simpleRun j hj) h = (0, 0) := by
  simp [Start_pt, simpleRun, ofSteps]
  rfl

/-- Definition 2.3(4), with each simple run based at the origin. -/
theorem CRot_normalized (rs : List ℕ) (o : LatticePoint) (j : ℕ)
    (hj : j ≤ rs.length) :
    CRot (runPath rs o) j =
      translate (concat (runPath (rs.drop j) 0) (runPath (rs.take j) 0)) o := by
  rw [← runPath_append, runPath_translate, zero_add]
  exact (rotateRuns_runPath rs o j).trans
    (congrArg (fun ss => runPath ss o) (List.rotate_eq_drop_append_take hj))

theorem subpath_nonempty (P : TNEPath) (i j : ℕ) (hij : i < j)
    (hj : j ≤ P.steps.length) : subpath P i j ≠ empty := by
  intro h
  have hl := congrArg (fun Q : TNEPath => Q.steps.length) h
  simp only [subpath_steps, List.length_take, List.length_drop, empty_steps,
    List.length_nil] at hl
  omega

theorem subpath_Start_NE (P : TNEPath) (i j : ℕ) (hij : i < j)
    (hj : j ≤ P.steps.length) :
    (Start_NE (subpath P i j) (subpath_nonempty P i j hij hj)).val =
      edge P ⟨i, lt_of_lt_of_le hij hj⟩ := by
  unfold Start_NE
  rw [edgeEquiv_apply, subpath_edge P i j hj]
  congr 1

theorem subpath_End_NE (P : TNEPath) (i j : ℕ) (hij : i < j)
    (hj : j ≤ P.steps.length) :
    (End_NE (subpath P i j) (subpath_nonempty P i j hij hj)).val =
      edge P ⟨j-1, by omega⟩ := by
  unfold End_NE
  rw [edgeEquiv_apply, subpath_edge P i j hj]
  congr 1
  apply Fin.ext
  simp only [subpathEdge, subpath_steps, List.length_take, List.length_drop]
  omega

theorem NEReal_Start_NE (P : TNEPath) (u v : Edge P) :
    cyclicAmbientEdge u v (Start_NE (NEReal P u v) (cyclicRealization_nonempty u v)) =
      edgeEquiv P u := by
  unfold cyclicAmbientEdge Start_NE
  simp only [Equiv.symm_apply_apply]
  exact congrArg (edgeEquiv P) (cyclicIndex_first u v)

theorem NEReal_End_NE (P : TNEPath) (u v : Edge P) :
    cyclicAmbientEdge u v (End_NE (NEReal P u v) (cyclicRealization_nonempty u v)) =
      edgeEquiv P v := by
  unfold cyclicAmbientEdge End_NE
  simp only [Equiv.symm_apply_apply]
  have hk : cyclicRealizationIndex u v
      ⟨(NEReal P u v).steps.length-1, by
        rw [cyclicRealization_length]
        have := cyclicLength_pos u v
        omega⟩ = ⟨cyclicLength u v-1, by have := cyclicLength_pos u v; omega⟩ := by
    apply Fin.ext
    simp [cyclicRealizationIndex, Nat.min_eq_left (cyclicLength_le u v)]
  rw [hk, cyclicIndex_last]

end KroneckerPaperPaths

namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths KroneckerCompatibility

private theorem cyclic_sum_shift {P : TNEPath} (g : Grading P) (u v : Edge P)
    (f : KroneckerStack.Edge → ℤ) :
    intervalSum f (geometricTrace (NERealGrading g u v)) 0 (cyclicLength u v) =
      intervalSum f (geometricTrace g) u.val (cyclicLength u v) := by
  unfold intervalSum
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.zero_add]
  exact congrArg f (KroneckerPaperPathGradings.cyclicTrace_at (bounded g) u v i
    (Finset.mem_range.mp hi))

theorem NGrDiff_debt {P : TNEPath} (g : Grading P) (u v : Edge P) :
    NGrDiff g (edgeEquiv P u) (edgeEquiv P v) =
      debt (geometricTrace g) u.val -
        debt (geometricTrace g) (u.val + cyclicLength u v) := by
  have hi := debt_interval (geometricTrace g) u.val (cyclicLength u v)
  have hh := KroneckerPaperPathGradings.cyclic_east_grade (bounded g) u v
  have hn := KroneckerPaperPathGradings.cyclic_north_count (bounded g) u v
  change intervalSum hGrade (geometricTrace (NERealGrading g u v)) 0 _ = _ at hh
  change intervalSum vCount (geometricTrace (NERealGrading g u v)) 0 _ = _ at hn
  rw [cyclic_sum_shift] at hh hn
  simp only [NGrDiff, Equiv.symm_apply_apply]
  change intervalSum hGrade (geometricTrace g) u.val _ =
    ∑ e ∈ cyclicE P u v, (g e : ℤ) at hh
  omega

theorem EGrDiff_bBal {P : TNEPath} (g : Grading P) (u v : Edge P)
    (huv : u.val ≤ v.val) :
    EGrDiff g (edgeEquiv P u) (edgeEquiv P v) =
      bBal g ⟨v.val+1, by have := v.isLt; omega⟩ -
        bBal g ⟨u.val, Nat.lt_succ_of_lt u.isLt⟩ := by
  have hi := balance_interval (geometricTrace g) u.val (cyclicLength u v)
  have hh := KroneckerPaperPathGradings.cyclic_east_count (bounded g) u v
  have hn := KroneckerPaperPathGradings.cyclic_north_grade (bounded g) u v
  change intervalSum hCount (geometricTrace (NERealGrading g u v)) 0 _ = _ at hh
  change intervalSum vGrade (geometricTrace (NERealGrading g u v)) 0 _ = _ at hn
  rw [cyclic_sum_shift] at hh hn
  have he : u.val + cyclicLength u v = v.val+1 := by
    simp only [cyclicLength, ite_eq_left huv]
    omega
  rw [he, hh, hn] at hi
  simpa only [EGrDiff, Equiv.symm_apply_apply, bBal, bounded] using hi.symm

theorem EGrDiff_eBal {P : TNEPath} (g : Grading P) (u v : Edge P)
    (huv : u.val ≤ v.val) (hu : P.steps.get u = true) :
    EGrDiff g (edgeEquiv P u) (edgeEquiv P v) =
      eBal g (edgeEquiv P v) - eBal g (edgeEquiv P u) + 1 := by
  rw [EGrDiff_bBal g u v huv]
  simp only [eBal, Equiv.symm_apply_apply, bBal]
  have ht := KroneckerPaperPathGradings.geometricTrace_edge (bounded g) u
  change geometricTrace g u.val = _ at ht
  simp only [hu, ite_true] at ht
  simp only [balance, walk]
  rw [ht]
  simp only [KroneckerStack.Edge.credit]
  omega

theorem whole_path_EGrDiff {P : TNEPath} (g : Grading P) (hP : P ≠ empty) :
    EGrDiff g (Start_NE P hP) (End_NE P hP) =
      bBal g ⟨P.steps.length, Nat.lt_succ_self _⟩ := by
  have hn : 0 < P.steps.length := by
    apply List.length_pos_iff.mpr
    intro hs
    exact hP ((eq_empty_iff P).mpr hs)
  have h := EGrDiff_bBal g
    ((edgeEquiv P).symm (Start_NE P hP))
    ((edgeEquiv P).symm (End_NE P hP)) (by simp)
  have he : P.steps.length-1+1 = P.steps.length := by omega
  simp only [Equiv.apply_symm_apply, Start_NE_index, End_NE_index, bBal] at h
  rw [he] at h
  simpa only [bBal, balance, walk, sub_zero] using h

theorem surp_EGrDiff {P : TNEPath} (g : Grading P) (hP : P ≠ empty) :
    Surp P g = EGrDiff g (Start_NE P hP) (End_NE P hP) - 1 := by
  rw [whole_path_EGrDiff]
  rfl

end KroneckerNaturalPathGradings
