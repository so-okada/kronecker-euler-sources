import KroneckerNaturalShadowNodes

/-! Definition 2.19 and Claim 3(a) of Lemma 2.24. The NGrDiff-zero and EGrDiff-zero
conditions are expressed using integer-valued differences. Zero extension is an actual grading. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths

/-- Definition 2.19: vertical-edge count minus total horizontal grade. -/
def NGrDiff {P : TNEPath} (g : Grading P) (u v : GeomEdge P) : ℤ :=
  ((cyclicN P ((edgeEquiv P).symm u) ((edgeEquiv P).symm v)).card : ℤ) -
    ∑ e ∈ cyclicE P ((edgeEquiv P).symm u) ((edgeEquiv P).symm v), (g e : ℤ)

/-- Definition 2.19: horizontal-edge count minus total vertical grade. -/
def EGrDiff {P : TNEPath} (g : Grading P) (u v : GeomEdge P) : ℤ :=
  ((cyclicE P ((edgeEquiv P).symm u) ((edgeEquiv P).symm v)).card : ℤ) -
    ∑ e ∈ cyclicN P ((edgeEquiv P).symm u) ((edgeEquiv P).symm v), (g e : ℤ)

theorem NGrDiff_eq_zero_iff {P : TNEPath} (g : Grading P) (u v : Edge P) :
    NGrDiff g (edgeEquiv P u) (edgeEquiv P v) = 0 ↔
      ((cyclicN P u v).card : ℤ) = ∑ e ∈ cyclicE P u v, (g e : ℤ) := by
  simp only [NGrDiff, Equiv.symm_apply_apply, sub_eq_zero]

theorem EGrDiff_eq_zero_iff {P : TNEPath} (g : Grading P) (u v : Edge P) :
    EGrDiff g (edgeEquiv P u) (edgeEquiv P v) = 0 ↔
      ((cyclicE P u v).card : ℤ) = ∑ e ∈ cyclicN P u v, (g e : ℤ) := by
  simp only [EGrDiff, Equiv.symm_apply_apply, sub_eq_zero]

theorem hCloses_iff_NGrDiff_zero {P : TNEPath} (g : Grading P) (u v : Edge P) :
    HCloses g u v ↔ P.steps.get v = false ∧
      NGrDiff g (edgeEquiv P u) (edgeEquiv P v) = 0 := by
  rw [NGrDiff_eq_zero_iff]; rfl

theorem vCloses_iff_EGrDiff_zero {P : TNEPath} (g : Grading P) (u v : Edge P) :
    VCloses g u v ↔ P.steps.get u = true ∧
      EGrDiff g (edgeEquiv P u) (edgeEquiv P v) = 0 := by
  rw [EGrDiff_eq_zero_iff]; rfl

theorem firstHShadow_NGrDiff_zero {P : TNEPath} {g : Grading P} {u v : Edge P}
    (h : FirstHShadow g u v) : NGrDiff g (edgeEquiv P u) (edgeEquiv P v) = 0 :=
  (NGrDiff_eq_zero_iff g u v).mpr h.2.1.2

theorem firstVShadow_EGrDiff_zero {P : TNEPath} {g : Grading P} {u v : Edge P}
    (h : FirstVShadow g u v) : EGrDiff g (edgeEquiv P u) (edgeEquiv P v) = 0 :=
  (EGrDiff_eq_zero_iff g u v).mpr h.2.1.2

theorem hWitness_iff_NGrDiff_zero {P : TNEPath} (g : Grading P) (u v t : Edge P) :
    HWitness g u v t ↔ edgeEquiv P t ∈ cyclicNE P u v ∧
      P.steps.get t = false ∧ t ≠ v ∧
      NGrDiff g (edgeEquiv P u) (edgeEquiv P t) = 0 := by
  rw [NGrDiff_eq_zero_iff]; rfl

theorem vWitness_iff_EGrDiff_zero {P : TNEPath} (g : Grading P) (u v t : Edge P) :
    VWitness g u v t ↔ edgeEquiv P t ∈ cyclicNE P u v ∧
      P.steps.get t = true ∧ t ≠ u ∧
      EGrDiff g (edgeEquiv P t) (edgeEquiv P v) = 0 := by
  rw [EGrDiff_eq_zero_iff]; rfl

theorem compatible_iff_grading_differences {P : TNEPath} (g : Grading P) :
    Compatible g ↔ ∀ u v : Edge P, P.steps.get u = true → P.steps.get v = false →
      0 < g (edgeEquiv P u) → 0 < g (edgeEquiv P v) → ∃ t,
        (edgeEquiv P t ∈ cyclicNE P u v ∧ P.steps.get t = false ∧ t ≠ v ∧
          NGrDiff g (edgeEquiv P u) (edgeEquiv P t) = 0) ∨
        (edgeEquiv P t ∈ cyclicNE P u v ∧ P.steps.get t = true ∧ t ≠ u ∧
          EGrDiff g (edgeEquiv P t) (edgeEquiv P v) = 0) := by
  simp only [Compatible, hWitness_iff_NGrDiff_zero, vWitness_iff_EGrDiff_zero]

theorem NEReal_surp_EGrDiff {P : TNEPath} (g : Grading P) (u v : Edge P) :
    Surp (NEReal P u v) (NERealGrading g u v) =
      EGrDiff g (edgeEquiv P u) (edgeEquiv P v) - 1 := by
  rw [NEReal_surp_formula]
  simp only [EGrDiff, Equiv.symm_apply_apply]
  omega

/-- The grading g0 in Claim 3(a) of Lemma 2.24. -/
def zeroExtension {P : TNEPath} (g : Grading P) (u v : Edge P) : Grading P :=
  fun e => if e ∈ cyclicNE P u v then g e else 0

theorem zeroExtension_on {P : TNEPath} (g : Grading P) (u v : Edge P)
    (e : GeomEdge P) (he : e ∈ cyclicNE P u v) : zeroExtension g u v e = g e :=
  ite_eq_left he

theorem zeroExtension_off {P : TNEPath} (g : Grading P) (u v : Edge P)
    (e : GeomEdge P) (he : e ∉ cyclicNE P u v) : zeroExtension g u v e = 0 :=
  ite_eq_right he

theorem NEReal_zeroExtension {P : TNEPath} (g : Grading P) (u v : Edge P) :
    NERealGrading (zeroExtension g u v) u v = NERealGrading g u v := by
  funext e
  apply zeroExtension_on
  have h : cyclicAmbientEdge u v e ∈ Set.range (cyclicAmbientEdge u v) := ⟨e,rfl⟩
  rwa [NEReal_ambient_range] at h

private theorem cyclicNE_prefix_subset {P : TNEPath} (u v w : Edge P)
    (h : cyclicLength u w ≤ cyclicLength u v) : cyclicNE P u w ⊆ cyclicNE P u v := by
  intro e he
  obtain ⟨k,rfl⟩ := (mem_cyclicNE u w e).mp he
  apply (mem_cyclicNE u v _).mpr
  refine ⟨⟨k.val, lt_of_lt_of_le k.isLt h⟩, ?_⟩
  congr 1

private theorem hCloses_zeroExtension {P : TNEPath} (g : Grading P) (u v w : Edge P)
    (h : cyclicLength u w ≤ cyclicLength u v) :
    HCloses (zeroExtension g u v) u w ↔ HCloses g u w := by
  have he : (∑ e ∈ cyclicE P u w, (zeroExtension g u v e : ℤ)) =
      ∑ e ∈ cyclicE P u w, (g e : ℤ) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [zeroExtension_on g u v e
      (cyclicNE_prefix_subset u v w h (Finset.mem_filter.mp he).1)]
  simp only [HCloses, he]

theorem firstHShadow_zeroExtension {P : TNEPath} (g : Grading P) (u v : Edge P)
    (hs : FirstHShadow g u v) : FirstHShadow (zeroExtension g u v) u v := by
  refine ⟨hs.1, (hCloses_zeroExtension g u v v le_rfl).mpr hs.2.1, ?_⟩
  intro w hw
  by_cases h : cyclicLength u w ≤ cyclicLength u v
  · exact hs.2.2 w ((hCloses_zeroExtension g u v w h).mp hw)
  · omega

private theorem trace_grade {P : TNEPath} (g : Grading P) (i : Edge P) :
    (geometricTrace g i.val).grade = g (edgeEquiv P i) := by
  have h := KroneckerPaperPathGradings.geometricTrace_edge (bounded g) i
  rw [trace_bounded] at h
  rw [h]
  cases P.steps.get i <;> rfl

theorem zeroExtension_compatible_iff_connected {P : TNEPath} (g : Grading P)
    (u v : Edge P) (hg : 0 < g (edgeEquiv P u)) (hs : FirstHShadow g u v) :
    Compatible (zeroExtension g u v) ↔ ConnectedGrading (NERealGrading g u v) := by
  have hu : edgeEquiv P u ∈ cyclicNE P u v :=
    (mem_cyclicNE u v _).mpr ⟨⟨0,cyclicLength_pos u v⟩, by simp⟩
  have hp : 0 < zeroExtension g u v (edgeEquiv P u) := by
    rwa [zeroExtension_on g u v _ hu]
  have hz : ∀ k, cyclicLength u v ≤ k → k < P.steps.length →
      (geometricTrace (zeroExtension g u v) (u.val+k)).grade = 0 := by
    intro k hk hkN
    have hN : 0 < P.steps.length := lt_of_le_of_lt (Nat.zero_le _) u.isLt
    let i : Edge P := ⟨(u.val+k) % P.steps.length, Nat.mod_lt _ hN⟩
    have hi : edgeEquiv P i ∉ cyclicNE P u v := by
      intro hi
      obtain ⟨j,hj⟩ := (mem_cyclicNE u v _).mp hi
      have hj' := congrArg Fin.val ((edgeEquiv P).injective hj)
      rw [cyclicIndex_mod] at hj'
      have hjN := lt_of_lt_of_le j.isLt (cyclicLength_le u v)
      have he : j.val = k := by
        have := Nat.ModEq.add_left_cancel' u.val hj'
        simpa only [Nat.ModEq, Nat.mod_eq_of_lt hjN, Nat.mod_eq_of_lt hkN] using this
      omega
    have hm := KroneckerPaperPathGradings.geometricTrace_mod (bounded (zeroExtension g u v))
      (u.val+k)
    change geometricTrace (zeroExtension g u v) ((u.val+k)%P.steps.length) =
      geometricTrace (zeroExtension g u v) (u.val+k) at hm
    rw [← hm, trace_grade (zeroExtension g u v) i]
    exact zeroExtension_off g u v (edgeEquiv P i) hi
  have h := NEReal_shadow_zero_extension (zeroExtension g u v) u v hp
    (firstHShadow_zeroExtension g u v hs) hz
  rwa [NEReal_zeroExtension] at h

end KroneckerNaturalPathGradings
