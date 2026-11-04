import KroneckerManuscriptPathDefinitions
import KroneckerPathContainment

/-! Definition 2.18. Cyclic edge sets contain ambient edges. NEReal has its own
geometric edges, mapped injectively to their names in the ambient path. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace KroneckerPaperPaths

/-- Ambient edges of a cyclic subpath (Definition 2.18(2)). -/
def CyclicSubpath.NE {P : TNEPath} (C : CyclicSubpath P) : Finset (GeomEdge P) :=
  C.edges.toFinset

def CyclicSubpath.E {P : TNEPath} (C : CyclicSubpath P) : Finset (GeomEdge P) :=
  C.NE.filter (fun w => P.steps.get ((edgeEquiv P).symm w) = true)

def CyclicSubpath.N {P : TNEPath} (C : CyclicSubpath P) : Finset (GeomEdge P) :=
  C.NE.filter (fun w => P.steps.get ((edgeEquiv P).symm w) = false)

abbrev cyclicNE (P : TNEPath) (u v : Edge P) := (CyclicSubpath.mk u v).NE
abbrev cyclicE (P : TNEPath) (u v : Edge P) := (CyclicSubpath.mk u v).E
abbrev cyclicN (P : TNEPath) (u v : Edge P) := (CyclicSubpath.mk u v).N

/-- The origin-based NE-path realization (Definition 2.18(3)). -/
abbrev NEReal (P : TNEPath) (u v : Edge P) : TNEPath := cyclicRealization u v

theorem mem_cyclicNE {P : TNEPath} (u v : Edge P) (w : GeomEdge P) :
    w ∈ cyclicNE P u v ↔ ∃ k, edgeEquiv P (cyclicIndex u v k) = w := by
  classical
  simp [cyclicNE, CyclicSubpath.NE, CyclicSubpath.edges, List.mem_ofFn]

theorem cyclicNE_eq_image {P : TNEPath} (u v : Edge P) :
    cyclicNE P u v = Finset.univ.image (fun k => edgeEquiv P (cyclicIndex u v k)) := by
  classical
  ext w
  simp [mem_cyclicNE]

theorem cyclicNE_card {P : TNEPath} (u v : Edge P) :
    (cyclicNE P u v).card = cyclicLength u v := by
  classical
  rw [cyclicNE_eq_image, Finset.card_image_of_injective _
    (show Function.Injective (fun k => edgeEquiv P (cyclicIndex u v k)) from
      (edgeEquiv P).injective.comp (cyclicIndex_injective u v))]
  simp

theorem cyclicNE_singleton {P : TNEPath} (u : Edge P) :
    cyclicNE P u u = {edgeEquiv P u} := by
  classical
  ext w
  rw [mem_cyclicNE]
  constructor
  · rintro ⟨k,rfl⟩
    have hk : k = ⟨0,cyclicLength_pos u u⟩ := by
      apply Fin.ext
      change k.val = 0
      have := k.isLt
      simp only [cyclicLength, le_refl, ite_true, Nat.sub_self, Nat.zero_add] at this
      omega
    simp [hk]
  · intro h
    exact ⟨⟨0,cyclicLength_pos u u⟩, by simpa using (Finset.mem_singleton.mp h).symm⟩

/-- The ambient names of all realized edges are exactly NE(U,u,v). -/
theorem NEReal_ambient_range {P : TNEPath} (u v : Edge P) :
    Set.range (cyclicAmbientEdge u v) = (cyclicNE P u v : Set (GeomEdge P)) := by
  ext w
  rw [Set.mem_range, Finset.mem_coe, mem_cyclicNE]
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨cyclicRealizationIndex u v ((edgeEquiv _).symm z), rfl⟩
  · rintro ⟨k,rfl⟩
    refine ⟨edgeEquiv _ ((cyclicRealizationIndex u v).symm k), ?_⟩
    simp [cyclicAmbientEdge]

@[simp] theorem NEReal_origin (P : TNEPath) (u v : Edge P) :
    (NEReal P u v).origin = 0 := cyclicRealization_origin u v

@[simp] theorem NEReal_steps (P : TNEPath) (u v : Edge P) :
    (NEReal P u v).steps = (P.steps.rotate u.val).take (cyclicLength u v) :=
  cyclicRealization_steps u v

/-- Containment keeps the ordered ambient edge names, even for a full cycle. -/
theorem CyclicSubpath.included_edge_subset {P : TNEPath} {A B : CyclicSubpath P}
    (h : A.Included B) : A.NE ⊆ B.NE := by
  classical
  obtain ⟨i,j,_,_,he⟩ := h
  intro w hw
  have hw' : w ∈ A.edges := List.mem_toFinset.mp hw
  rw [he] at hw'
  exact List.mem_toFinset.mpr (List.mem_of_mem_drop (List.mem_of_mem_take hw'))

theorem CyclicSubpath.disjoint_iff {P : TNEPath} (A B : CyclicSubpath P) :
    A.Disjoint B ↔ A.NE ∩ B.NE = ∅ := by
  classical
  exact Finset.disjoint_iff_inter_eq_empty

/-- Finite sums over ambient edge names agree with sums in cyclic order. -/
theorem sum_cyclicNE {P : TNEPath} (u v : Edge P) (f : GeomEdge P → ℤ) :
    ∑ w ∈ cyclicNE P u v, f w =
      ∑ k : Fin (cyclicLength u v), f (edgeEquiv P (cyclicIndex u v k)) := by
  classical
  rw [cyclicNE_eq_image]
  exact Finset.sum_image (fun a _ b _ h =>
    cyclicIndex_injective u v ((edgeEquiv P).injective h))

end KroneckerPaperPaths

namespace KroneckerPaperPathGradings
open KroneckerPaperPaths KroneckerCompatibility

abbrev NERealGrading {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) :
    Grading m (NEReal P u v) := cyclicGrading g u v

abbrev NERealColoredGrading {m : ℕ} {P : TNEPath}
    (c : ColoredGrading m P) (u v : Edge P) : ColoredGrading m (NEReal P u v) :=
  cyclicColoredGrading c u v

theorem NEReal_grade {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P)
    (w : GeomEdge (NEReal P u v)) :
    NERealGrading g u v w = g (cyclicAmbientEdge u v w) := rfl

theorem NEReal_color {m : ℕ} {P : TNEPath} (c : ColoredGrading m P) (u v : Edge P)
    (w : GeomEdge (NEReal P u v)) :
    ((NERealColoredGrading c u v).2 w).val = (c.2 (cyclicAmbientEdge u v w)).val := rfl

/-- A cyclic interval sum is the finite sum over its ambient edge names. -/
theorem cyclic_intervalSum {m : ℕ} {P : TNEPath} (g : Grading m P)
    (u v : Edge P) (f : KroneckerStack.Edge → ℤ) :
    intervalSum f (geometricTrace (NERealGrading g u v)) 0 (cyclicLength u v) =
      ∑ w ∈ cyclicNE P u v,
        f (if P.steps.get ((edgeEquiv P).symm w) then
          KroneckerStack.Edge.H (g w).val else KroneckerStack.Edge.V (g w).val) := by
  classical
  rw [sum_cyclicNE, intervalSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Nat.zero_add, Equiv.symm_apply_apply]
  have ht := cyclicTrace_correspondence g u v
    (⟨k.val, by rw [cyclicRealization_length]; exact k.isLt⟩ : Edge (cyclicRealization u v))
  change geometricTrace (NERealGrading g u v) k.val = _ at ht
  rw [ht, ← geometricTrace_mod g (u.val+k.val), ← cyclicIndex_mod u v k,
    geometricTrace_edge]

theorem cyclic_north_count {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) :
    intervalSum vCount (geometricTrace (NERealGrading g u v)) 0 (cyclicLength u v) =
      ((cyclicN P u v).card : ℤ) := by
  classical
  rw [cyclic_intervalSum]
  simp only [cyclicN, CyclicSubpath.N, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro w _
  cases P.steps.get ((edgeEquiv P).symm w) <;> simp [vCount]

theorem cyclic_east_count {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) :
    intervalSum hCount (geometricTrace (NERealGrading g u v)) 0 (cyclicLength u v) =
      ((cyclicE P u v).card : ℤ) := by
  classical
  rw [cyclic_intervalSum]
  simp only [cyclicE, CyclicSubpath.E, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro w _
  cases P.steps.get ((edgeEquiv P).symm w) <;> simp [hCount]

theorem cyclic_east_grade {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) :
    intervalSum hGrade (geometricTrace (NERealGrading g u v)) 0 (cyclicLength u v) =
      ∑ w ∈ cyclicE P u v, ((g w).val : ℤ) := by
  classical
  rw [cyclic_intervalSum]
  simp only [cyclicE, CyclicSubpath.E, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  cases P.steps.get ((edgeEquiv P).symm w) <;> simp [hGrade]

theorem cyclic_north_grade {m : ℕ} {P : TNEPath} (g : Grading m P) (u v : Edge P) :
    intervalSum vGrade (geometricTrace (NERealGrading g u v)) 0 (cyclicLength u v) =
      ∑ w ∈ cyclicN P u v, ((g w).val : ℤ) := by
  classical
  rw [cyclic_intervalSum]
  simp only [cyclicN, CyclicSubpath.N, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  cases P.steps.get ((edgeEquiv P).symm w) <;> simp [vGrade]

end KroneckerPaperPathGradings
