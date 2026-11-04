import KroneckerGeometricShadows

set_option autoImplicit false
noncomputable section

namespace KroneckerPaperPathGradings
open KroneckerPaperPaths

def edgeIndex {P : TNEPath} (v : GeomEdge P) : ℕ :=
  ((edgeEquiv P).symm v).val

abbrev Horizontal (P : TNEPath) :=
  {v : GeomEdge P // P.steps.get ((edgeEquiv P).symm v) = true}

abbrev Vertical (P : TNEPath) :=
  {v : GeomEdge P // P.steps.get ((edgeEquiv P).symm v) = false}

theorem horizontal_geometry {P : TNEPath} (v : Horizontal P) :
    v.val.val.2 - v.val.val.1 = (1, 0) := by
  have h := edge_direction P ((edgeEquiv P).symm v.val)
  have he : edge P ((edgeEquiv P).symm v.val) = v.val.val :=
    congrArg Subtype.val ((edgeEquiv P).apply_symm_apply v.val)
  rw [he, v.property] at h
  exact h

theorem vertical_geometry {P : TNEPath} (v : Vertical P) :
    v.val.val.2 - v.val.val.1 = (0, 1) := by
  have h := edge_direction P ((edgeEquiv P).symm v.val)
  have he : edge P ((edgeEquiv P).symm v.val) = v.val.val :=
    congrArg Subtype.val ((edgeEquiv P).apply_symm_apply v.val)
  rw [he, v.property] at h
  exact h

def occurrenceWord {m : ℕ} {P : TNEPath} (g : Grading m P) :
    KroneckerPredecessor.Word P.steps.length := fun i =>
  if P.steps.get i then .H (g (edgeEquiv P i)).val
  else .V (g (edgeEquiv P i)).val

@[simp] theorem occurrenceWord_horizontal {m : ℕ} {P : TNEPath}
    (g : Grading m P) (i : Edge P) :
    KroneckerPredecessor.IsHorizontal (occurrenceWord g) i ↔
      P.steps.get i = true := by
  cases h : P.steps.get i <;>
    simp only [List.get_eq_getElem] at h <;>
    simp [occurrenceWord, KroneckerPredecessor.IsHorizontal, List.get_eq_getElem, h]

@[simp] theorem occurrenceWord_grade {m : ℕ} {P : TNEPath}
    (g : Grading m P) (i : Edge P) :
    ((occurrenceWord g) i).grade = (g (edgeEquiv P i)).val := by
  cases h : P.steps.get i <;>
    simp only [List.get_eq_getElem] at h <;>
    simp [occurrenceWord, KroneckerStack.Edge.grade, h]

theorem occurrenceWord_raw {m : ℕ} {P : TNEPath} (g : Grading m P) :
    occurrenceWord g = KroneckerPaperTraceBridge.sample
      (KroneckerSourceGradingDictionary.rawTrace
        (KroneckerWordCounts.pathShape P.steps) (gradingEquiv m P g)) P.steps.length := by
  funext i
  exact (geometricTrace_edge g i).symm

def horizontalEquiv {m : ℕ} {P : TNEPath} (g : Grading m P) :
    Horizontal P ≃ KroneckerPredecessor.Horizontal (occurrenceWord g) :=
  (edgeEquiv P).symm.subtypeEquiv (fun _ => (occurrenceWord_horizontal g _).symm)

def verticalEquiv {m : ℕ} {P : TNEPath} (g : Grading m P) :
    Vertical P ≃ KroneckerPredecessor.Vertical (occurrenceWord g) :=
  (edgeEquiv P).symm.subtypeEquiv (fun v => by
    rw [occurrenceWord_horizontal]
    cases P.steps.get ((edgeEquiv P).symm v) <;> simp)

def predecessorOccurrences {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) :
    KroneckerPredecessor.Vertical (occurrenceWord g) →
      KroneckerPredecessor.Horizontal (occurrenceWord g) :=
  fun v => horizontalEquiv g (p ((verticalEquiv g).symm v))

def assignmentCount {P : TNEPath} (p : Vertical P → Horizontal P)
    (k : ℕ) (x : Horizontal P) : ℕ :=
  Nat.card {v : Vertical P // edgeIndex v.val < k ∧ p v = x}

def predecessorGeometry {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : KroneckerPredecessor.Vertical (occurrenceWord g) →
      KroneckerPredecessor.Horizontal (occurrenceWord g)) : Vertical P → Horizontal P :=
  fun v => (horizontalEquiv g).symm (p (verticalEquiv g v))

@[simp] theorem predecessorOccurrences_geometry {m : ℕ} {P : TNEPath}
    (g : Grading m P)
    (p : KroneckerPredecessor.Vertical (occurrenceWord g) →
      KroneckerPredecessor.Horizontal (occurrenceWord g)) :
    predecessorOccurrences g (predecessorGeometry g p) = p := by
  funext v
  simp [predecessorOccurrences, predecessorGeometry]

theorem assignmentCount_occurrences {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (k : ℕ) (x : Horizontal P) :
    assignmentCount p k x = KroneckerPredecessor.assignedBefore
      (occurrenceWord g) (predecessorOccurrences g p) k (horizontalEquiv g x) := by
  classical
  rw [KroneckerPredecessor.assignedBefore_eq_card]
  let e := (verticalEquiv g).subtypeEquiv
    (p := fun v => edgeIndex v.val < k ∧ p v = x)
    (q := fun v => v.val.val < k ∧
      predecessorOccurrences g p v = horizontalEquiv g x)
    (fun v => by
      change (edgeIndex v.val < k ∧ p v = x) ↔
        (edgeIndex v.val < k ∧ horizontalEquiv g
          (p ((verticalEquiv g).symm (verticalEquiv g v))) = horizontalEquiv g x)
      simp)
  have h := Nat.card_congr e
  simpa [assignmentCount, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

def IsPredecessor {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) : Prop :=
  ∀ v : Vertical P,
    edgeIndex (p v).val < edgeIndex v.val ∧
    assignmentCount p (edgeIndex v.val) (p v) < (g (p v).val).val ∧
    ∀ x : Horizontal P, edgeIndex x.val < edgeIndex v.val →
      assignmentCount p (edgeIndex v.val) x < (g x.val).val →
      edgeIndex x.val ≤ edgeIndex (p v).val

theorem isPredecessor_iff {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) :
    IsPredecessor g p ↔ KroneckerPredecessor.IsHorizontalPredecessor
      (occurrenceWord g) (predecessorOccurrences g p) := by
  rw [KroneckerPredecessor.isHorizontalPredecessor_iff]
  constructor
  · intro hp v
    obtain ⟨w, rfl⟩ := (verticalEquiv g).surjective v
    have h := hp w
    simp only [predecessorOccurrences, Equiv.symm_apply_apply]
    refine ⟨h.1, ?_, ?_⟩
    · rw [← assignmentCount_occurrences]
      simpa [horizontalEquiv, verticalEquiv, edgeIndex, Equiv.subtypeEquiv] using h.2.1
    · intro x hx hg
      obtain ⟨y, rfl⟩ := (horizontalEquiv g).surjective x
      apply h.2.2 y hx
      rw [← assignmentCount_occurrences] at hg
      simpa [horizontalEquiv, verticalEquiv, edgeIndex, Equiv.subtypeEquiv] using hg
  · intro hp v
    have h := hp (verticalEquiv g v)
    simp only [predecessorOccurrences, Equiv.symm_apply_apply] at h
    refine ⟨h.1, ?_, ?_⟩
    · have hh := h.2.1
      rw [← assignmentCount_occurrences] at hh
      simpa [horizontalEquiv, verticalEquiv, edgeIndex, Equiv.subtypeEquiv] using hh
    · intro x hx hg
      apply h.2.2 (horizontalEquiv g x) hx
      rw [← assignmentCount_occurrences]
      simpa [horizontalEquiv, verticalEquiv, edgeIndex, Equiv.subtypeEquiv] using hg

theorem predecessor_unique {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p q : Vertical P → Horizontal P) (hp : IsPredecessor g p)
    (hq : IsPredecessor g q) : p = q := by
  have h := KroneckerPredecessor.horizontalPredecessor_unique (occurrenceWord g)
    (predecessorOccurrences g p) (predecessorOccurrences g q)
    ((isPredecessor_iff g p).mp hp) ((isPredecessor_iff g q).mp hq)
  funext v
  apply (horizontalEquiv g).injective
  have hv := congrFun h (verticalEquiv g v)
  simpa [predecessorOccurrences] using hv

theorem predecessor_exists_iff {m : ℕ} {P : TNEPath} (g : Grading m P) :
    (∃ p, IsPredecessor g p) ↔ ∀ k ≤ P.steps.length,
      KroneckerPredecessor.verticalCount (occurrenceWord g) k ≤
        KroneckerPredecessor.horizontalGrade (occurrenceWord g) k := by
  rw [← KroneckerPredecessor.exists_horizontalPredecessor_iff]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨predecessorOccurrences g p, (isPredecessor_iff g p).mp hp⟩
  · rintro ⟨p, hp⟩
    refine ⟨predecessorGeometry g p, (isPredecessor_iff g _).mpr ?_⟩
    simpa using hp

def Debt {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (x : Horizontal P) (k : ℕ) : ℕ :=
  (g x.val).val - assignmentCount p k x

theorem debt_and_assignments {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (hp : IsPredecessor g p)
    (x : Horizontal P) (k : ℕ) (hk : k ≤ P.steps.length) :
    Debt g p x k + assignmentCount p k x = (g x.val).val := by
  have h := KroneckerPredecessor.Debt_add_assignedBefore (occurrenceWord g)
    (predecessorOccurrences g p) ((isPredecessor_iff g p).mp hp) hk (horizontalEquiv g x)
  unfold KroneckerPredecessor.Debt at h
  rw [← assignmentCount_occurrences] at h
  simpa [Debt, horizontalEquiv, Equiv.subtypeEquiv] using h

def IsNode {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (x : Horizontal P) (v : Vertical P) : Prop :=
  p v = x ∧ assignmentCount p P.steps.length x = (g x.val).val ∧
    ∀ w : Vertical P, p w = x → edgeIndex w.val ≤ edgeIndex v.val

theorem isNode_iff {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (x : Horizontal P) (v : Vertical P) :
    IsNode g p x v ↔ KroneckerPredecessor.IsNode (occurrenceWord g)
      (KroneckerPredecessor.extend (occurrenceWord g) (predecessorOccurrences g p))
      (horizontalEquiv g x).val (verticalEquiv g v).val := by
  constructor
  · rintro ⟨he, hs, hl⟩
    refine ⟨(horizontalEquiv g x).property, (verticalEquiv g v).property, ?_, ?_, ?_⟩
    · rw [KroneckerPredecessor.extend_vertical]
      simp [predecessorOccurrences, he]
    · change KroneckerPredecessor.assignedBefore (occurrenceWord g)
        (predecessorOccurrences g p) P.steps.length (horizontalEquiv g x) = _
      rw [← assignmentCount_occurrences]
      simpa [horizontalEquiv, verticalEquiv, edgeIndex, Equiv.subtypeEquiv] using hs
    · intro w hw hwx
      let w' : KroneckerPredecessor.Vertical (occurrenceWord g) := ⟨w, hw⟩
      obtain ⟨z, hz⟩ := (verticalEquiv g).surjective w'
      have hpz : predecessorOccurrences g p w' = horizontalEquiv g x :=
        Subtype.ext (by simpa [w', KroneckerPredecessor.extend, hw] using hwx)
      rw [← hz] at hpz
      have hpx : p z = x := (horizontalEquiv g).injective (by
        simpa [predecessorOccurrences] using hpz)
      have hle := hl z hpx
      have hi : edgeIndex z.val = w.val := congrArg (fun a => a.val.val) hz
      change w.val ≤ edgeIndex v.val
      rw [hi] at hle
      exact hle
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · apply (horizontalEquiv g).injective
      have he : predecessorOccurrences g p (verticalEquiv g v) = horizontalEquiv g x :=
        Subtype.ext (by simpa only [KroneckerPredecessor.extend_vertical] using h.end_assigned)
      simpa [predecessorOccurrences] using he
    · have hs := h.saturated
      change KroneckerPredecessor.assignedBefore (occurrenceWord g)
        (predecessorOccurrences g p) P.steps.length (horizontalEquiv g x) = _ at hs
      rw [← assignmentCount_occurrences] at hs
      simpa [horizontalEquiv, verticalEquiv, edgeIndex, Equiv.subtypeEquiv] using hs
    · intro w hw
      apply h.last_assigned (verticalEquiv g w).val (verticalEquiv g w).property
      rw [KroneckerPredecessor.extend_vertical]
      simp [predecessorOccurrences, hw]

def nodePath {P : TNEPath} (x : Horizontal P) (v : Vertical P) : TNEPath :=
  subpath P (edgeIndex x.val) (edgeIndex v.val + 1)

theorem nodePath_edges {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (hp : IsPredecessor g p)
    (x : Horizontal P) (v : Vertical P) (h : IsNode g p x v) :
    (nodePath x v).steps = (P.steps.drop (edgeIndex x.val)).take
      (edgeIndex v.val + 1 - edgeIndex x.val) ∧
    (nodePath x v).origin = vertex P (edgeIndex x.val) := by
  refine ⟨rfl, ?_⟩
  apply subpath_origin
  · have hh := (hp v).1
    rw [h.1] at hh
    omega
  · exact ((edgeEquiv P).symm v.val).isLt

set_option backward.isDefEq.respectTransparency false in
theorem nodePath_mem_edge_iff {P : TNEPath} (x : Horizontal P)
    (v : Vertical P) (k : Edge P) :
    edge P k ∈ Set.range (edge (nodePath x v)) ↔
      edgeIndex x.val ≤ k.val ∧ k.val ≤ edgeIndex v.val := by
  have hv : edgeIndex v.val + 1 ≤ P.steps.length := ((edgeEquiv P).symm v.val).isLt
  constructor
  · rintro ⟨j, hj⟩
    change edge (subpath P (edgeIndex x.val) (edgeIndex v.val + 1)) j = edge P k at hj
    rw [subpath_edge P _ _ hv] at hj
    have hidx := congrArg Fin.val (edge_injective P hj)
    change edgeIndex x.val + j.val = k.val at hidx
    have hl := j.isLt
    simp only [nodePath, subpath_steps, List.length_take, List.length_drop] at hl
    omega
  · rintro ⟨hx, hk⟩
    let j : Edge (nodePath x v) := ⟨k.val - edgeIndex x.val, by
      simp only [nodePath, subpath_steps, List.length_take, List.length_drop]
      omega⟩
    refine ⟨j, ?_⟩
    change edge (subpath P (edgeIndex x.val) (edgeIndex v.val + 1)) j = edge P k
    rw [subpath_edge P _ _ hv]
    apply congrArg (edge P)
    apply Fin.ext
    change edgeIndex x.val + (k.val - edgeIndex x.val) = k.val
    omega

structure Node {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) where
  first : Horizontal P
  last : Vertical P
  isNode : IsNode g p first last

def nodeEdges {m : ℕ} {P : TNEPath} {g : Grading m P}
    {p : Vertical P → Horizontal P} (X : Node g p) :
    Set (LatticePoint × LatticePoint) := Set.range (edge (nodePath X.first X.last))

def Ancestor {m : ℕ} {P : TNEPath} {g : Grading m P}
    {p : Vertical P → Horizontal P} (X Y : Node g p) : Prop :=
  nodeEdges Y ⊂ nodeEdges X

def Parent {m : ℕ} {P : TNEPath} {g : Grading m P}
    {p : Vertical P → Horizontal P} (X Y : Node g p) : Prop :=
  Ancestor X Y ∧ ¬ ∃ Z : Node g p, Ancestor X Z ∧ Ancestor Z Y

end KroneckerPaperPathGradings
