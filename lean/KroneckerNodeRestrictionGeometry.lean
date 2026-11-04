import KroneckerNodeParent
import KroneckerSurplus
import KroneckerPaperNodeRestriction

/-! Lemma 2.15(4): literal grading restriction and Surp on geometric node paths. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerPaperPathGradings
open KroneckerPaperPaths KroneckerCompatibility

/-- Pull back a grading along the actual geometric inclusion of a subpath. -/
def restrictGrading {m : ℕ} {P : TNEPath} (g : Grading m P)
    (i j : ℕ) (hj : j ≤ P.steps.length) : Grading m (subpath P i j) :=
  fun w => g (edgeEquiv P (subpathEdge P i j hj ((edgeEquiv _).symm w)))

theorem restrictGrading_geometry {m : ℕ} {P : TNEPath} (g : Grading m P)
    (i j : ℕ) (hj : j ≤ P.steps.length) (w : GeomEdge (subpath P i j)) :
    ∃ v : GeomEdge P, v.val = w.val ∧ restrictGrading g i j hj w = g v := by
  refine ⟨edgeEquiv P (subpathEdge P i j hj ((edgeEquiv _).symm w)), ?_,rfl⟩
  change edge P (subpathEdge P i j hj ((edgeEquiv _).symm w)) = w.val
  rw [← subpath_edge P i j hj, edge_equiv_inverse]

set_option backward.isDefEq.respectTransparency false in
theorem subpath_get (P : TNEPath) (i j : ℕ) (hj : j ≤ P.steps.length)
    (k : Edge (subpath P i j)) :
    (subpath P i j).steps.get k = P.steps.get (subpathEdge P i j hj k) := by
  simp only [subpath_steps, List.get_eq_getElem, List.getElem_take, List.getElem_drop, subpathEdge]

theorem restrictGrading_occurrence {m : ℕ} {P : TNEPath} (g : Grading m P)
    (i j : ℕ) (hj : j ≤ P.steps.length) (k : Edge (subpath P i j)) :
    occurrenceWord (restrictGrading g i j hj) k = occurrenceWord g (subpathEdge P i j hj k) := by
  simp only [occurrenceWord, restrictGrading, Equiv.symm_apply_apply]
  rw [subpath_get P i j hj k]

theorem restrictGrading_trace {m : ℕ} {P : TNEPath} (g : Grading m P)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ P.steps.length)
    (k : ℕ) (hk : k < j-i) :
    geometricTrace (restrictGrading g i j hj) k = geometricTrace g (i+k) := by
  let K : Edge (subpath P i j) := ⟨k,by rw [subpath_length P hij hj]; exact hk⟩
  have h := restrictGrading_occurrence g i j hj K
  rw [occurrenceWord_raw, occurrenceWord_raw] at h
  exact h

/-- Restriction subtracts the same boundary balance from every balance. -/
theorem restrictGrading_boundaryBalance {m : ℕ} {P : TNEPath} (g : Grading m P)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ P.steps.length)
    (k : ℕ) (hk : k ≤ j-i) :
    boundaryBalance (restrictGrading g i j hj)
      ⟨k,by rw [subpath_length P hij hj]; omega⟩ =
    boundaryBalance g ⟨i+k,by omega⟩ - boundaryBalance g ⟨i,by omega⟩ :=
  walk_subpath (restrictGrading_trace g i j hij hj) KroneckerStack.Edge.credit k hk

/-- Manuscript g restricted to NE(X), with no translation of the node. -/
abbrev nodeGrading {m : ℕ} {P : TNEPath} (g : Grading m P)
    (x : Horizontal P) (v : Vertical P) : Grading m (nodePath x v) :=
  restrictGrading g (edgeIndex x.val) (edgeIndex v.val+1)
    ((edgeEquiv P).symm v.val).isLt

/-- The exact Surp identity in Lemma 2.15(4)(c). -/
theorem node_surp_balance {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p) (X : Node g p) :
    edgeBalance g X.last.val -
      boundaryBalance g ⟨edgeIndex X.first.val,by exact Nat.lt_succ_of_lt ((edgeEquiv P).symm X.first.val).isLt⟩ =
    Surp (nodePath X.first X.last) (nodeGrading g X.first X.last)+1 := by
  have hle := X.start_lt_end hp
  have hj : edgeIndex X.last.val+1 ≤ P.steps.length := ((edgeEquiv P).symm X.last.val).isLt
  have h := restrictGrading_boundaryBalance g (edgeIndex X.first.val) (edgeIndex X.last.val+1)
    (by omega) hj (edgeIndex X.last.val+1-edgeIndex X.first.val) le_rfl
  have hlen := subpath_length P (by omega : edgeIndex X.first.val ≤ edgeIndex X.last.val+1) hj
  have he : edgeIndex X.first.val+(edgeIndex X.last.val+1-edgeIndex X.first.val) =
      edgeIndex X.last.val+1 := by omega
  simp only [he] at h
  unfold Surp surplus boundaryBalance
  unfold boundaryBalance at h
  change edgeBalance g X.last.val - boundaryBalance g _ =
    KroneckerCompatibility.balance (geometricTrace (nodeGrading g X.first X.last))
      (subpath P (edgeIndex X.first.val) (edgeIndex X.last.val+1)).steps.length-1+1
  rw [hlen]
  change _ = KroneckerCompatibility.balance
    (geometricTrace (restrictGrading g _ _ hj)) _-1+1
  simpa only [edgeBalance, boundaryBalance, geometricTrace, edgeIndex, sub_add_cancel] using h.symm

/-- Intrinsic connectedness, without choosing a surplus parameter. -/
def ConnectedGrading {m : ℕ} {P : TNEPath} (g : Grading m P) : Prop :=
  KroneckerPaperConnected.Connected (geometricTrace g) P.steps.length

/-- The node balance condition, on the occurrences of this geometric grading. -/
def NodeBalance {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) : Prop :=
  KroneckerPredecessor.OwnedBalance (occurrenceWord g)
    (KroneckerPredecessor.extend (occurrenceWord g) (predecessorOccurrences g p))

theorem connectedGrading_surp_nonnegative {m : ℕ} {P : TNEPath}
    {g : Grading m P} (hc : ConnectedGrading g) : 0 ≤ Surp P g := by
  obtain ⟨p,hp,hb,hr⟩ := hc
  have h := KroneckerPaperConnected.literal_final_balance hp hb hr
  change 0 ≤ KroneckerCompatibility.balance (geometricTrace g) P.steps.length-1
  omega

theorem connectedGrade_iff_connected_surp {m : ℕ} {P : TNEPath}
    (g : Grading m P) (d : ℕ) :
    ConnectedGrade d g ↔ ConnectedGrading g ∧ Surp P g = (d : ℤ) := by
  change (_ ∧ KroneckerCompatibility.balance (geometricTrace g) P.steps.length = (d:ℤ)+1) ↔
    (_ ∧ KroneckerCompatibility.balance (geometricTrace g) P.steps.length-1 = (d:ℤ))
  constructor <;> rintro ⟨hc,hd⟩ <;> exact ⟨hc,by omega⟩

/-- Lemma 2.15(4)(a): the geometric restriction itself is connected. -/
theorem nodeGrading_connected {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (hb : NodeBalance g p) (X : Node g p) :
    ConnectedGrading (nodeGrading g X.first X.last) := by
  let x := (horizontalEquiv g X.first).val
  let v := (verticalEquiv g X.last).val
  have hp' := (isPredecessor_iff g p).mp ((isHPrecursor_iff g p).mp hp)
  have hn := (isNode_iff g p X.first X.last).mp X.isNode
  have hc := hn.restriction_connected hp' hb
  have hxy := X.start_lt_end hp
  have hj : edgeIndex X.last.val+1 ≤ P.steps.length := ((edgeEquiv P).symm X.last.val).isLt
  have hlen : (nodePath X.first X.last).steps.length =
      KroneckerPredecessor.restrictionLength x v :=
    subpath_length P (by omega) hj
  have hw : KroneckerPredecessor.restrictionWord (occurrenceWord g) x v =
      KroneckerPaperTraceBridge.sample (geometricTrace (nodeGrading g X.first X.last))
        (KroneckerPredecessor.restrictionLength x v) := by
    funext k
    change occurrenceWord g (KroneckerPredecessor.restrictionEmbed x v k) =
      geometricTrace (nodeGrading g X.first X.last) k.val
    rw [occurrenceWord_raw]
    symm
    exact restrictGrading_trace g _ _ (by omega) hj k.val k.isLt
  change KroneckerPaperConnected.FiniteConnected
    (KroneckerPredecessor.restrictionWord (occurrenceWord g) x v) at hc
  rw [hw] at hc
  unfold ConnectedGrading KroneckerPaperConnected.Connected
  rw [hlen]
  exact hc

/-- Lemma 2.15(4)(b), with Surp and the restricted grading. -/
theorem nodeGrading_surp_nonnegative {m : ℕ} {P : TNEPath} (g : Grading m P)
    (p : Vertical P → Horizontal P) (hp : IsHPrecursor g p)
    (hb : NodeBalance g p) (X : Node g p) :
    0 ≤ Surp (nodePath X.first X.last) (nodeGrading g X.first X.last) :=
  connectedGrading_surp_nonnegative (nodeGrading_connected g p hp hb X)

end KroneckerPaperPathGradings
