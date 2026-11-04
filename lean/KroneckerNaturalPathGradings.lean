import KroneckerAmbientShadows
import KroneckerManuscriptShadowNodes
import KroneckerSourceNaturalGradings

/-! Definitions 2.4--2.14 with unrestricted nonnegative grades on geometric
edges. The finite grade bound below is computed from each input, independently
of m. Colors imply the bound m; the counting equivalence proves that the
finite counting core represents exactly the manuscript's colored objects. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths

abbrev Grading (P : TNEPath) := GeomEdge P → ℕ

def ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) : Grading P := fun e => (g e).val

def gradeBound {P : TNEPath} (g : Grading P) : ℕ :=
  KroneckerSourceNaturalGradings.capacity (fun i => g (edgeEquiv P i))

theorem grade_le_bound {P : TNEPath} (g : Grading P) (e : GeomEdge P) :
    g e ≤ gradeBound g := by
  simpa only [gradeBound, Equiv.apply_symm_apply] using
    KroneckerSourceNaturalGradings.grade_le_capacity
      (fun i => g (edgeEquiv P i)) ((edgeEquiv P).symm e)

def bounded {P : TNEPath} (g : Grading P) :
    KroneckerPaperPathGradings.Grading (gradeBound g) P :=
  fun e => ⟨g e, Nat.lt_succ_of_le (grade_le_bound g e)⟩

@[simp] theorem ofBounded_bounded {P : TNEPath} (g : Grading P) :
    ofBounded (bounded g) = g := rfl

def geometricTrace {P : TNEPath} (g : Grading P) : ℕ → KroneckerStack.Edge :=
  KroneckerSourceNaturalGradings.naturalTrace
    (KroneckerWordCounts.pathShape P.steps) (fun i => g (edgeEquiv P i))

@[simp] theorem trace_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) :
    geometricTrace (ofBounded g) = KroneckerPaperPathGradings.geometricTrace g := rfl

@[simp] theorem trace_bounded {P : TNEPath} (g : Grading P) :
    KroneckerPaperPathGradings.geometricTrace (bounded g) = geometricTrace g := rfl

def bBal {P : TNEPath} (g : Grading P) (i : Fin (P.steps.length+1)) : ℤ :=
  KroneckerCompatibility.balance (geometricTrace g) i.val

def eBal {P : TNEPath} (g : Grading P) (e : GeomEdge P) : ℤ :=
  bBal g ⟨((edgeEquiv P).symm e).val+1, by have := ((edgeEquiv P).symm e).isLt; omega⟩

def Surp (P : TNEPath) (g : Grading P) : ℤ :=
  bBal g ⟨P.steps.length, Nat.lt_succ_self _⟩-1

def ConnectedGrading {P : TNEPath} (g : Grading P) : Prop :=
  KroneckerPaperConnected.Connected (geometricTrace g) P.steps.length

@[simp] theorem bBal_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) (i : Fin (P.steps.length+1)) :
    bBal (ofBounded g) i = KroneckerPaperPathGradings.boundaryBalance g i := rfl

@[simp] theorem eBal_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) (e : GeomEdge P) :
    eBal (ofBounded g) e = KroneckerPaperPathGradings.edgeBalance g e := rfl

@[simp] theorem surp_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) :
    Surp P (ofBounded g) = KroneckerPaperPathGradings.Surp P g := rfl

@[simp] theorem connected_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) :
    ConnectedGrading (ofBounded g) ↔ KroneckerPaperPathGradings.ConnectedGrading g := Iff.rfl

theorem connected_surp_nonnegative {P : TNEPath} {g : Grading P}
    (hg : ConnectedGrading g) : 0 ≤ Surp P g :=
  KroneckerPaperPathGradings.connectedGrading_surp_nonnegative (g := bounded g) hg

def translateGrading {P : TNEPath} (g : Grading P) (t : LatticePoint) :
    Grading (translate P t) :=
  fun e => g ((KroneckerPaperPathGradings.translateEdge P t).symm e)

@[simp] theorem translate_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) (t : LatticePoint) :
    translateGrading (ofBounded g) t =
      ofBounded (KroneckerPaperPathGradings.translateGrading g t) := rfl

theorem translateGrading_apply {P : TNEPath} (g : Grading P) (t : LatticePoint)
    (e : GeomEdge P) :
    translateGrading g t (KroneckerPaperPathGradings.translateEdge P t e) = g e := by
  simp [translateGrading]

theorem trace_translate {P : TNEPath} (g : Grading P) (t : LatticePoint) :
    geometricTrace (translateGrading g t) = geometricTrace g :=
  KroneckerPaperPathGradings.geometricTrace_translate (bounded g) t

theorem connected_translate {P : TNEPath} (g : Grading P) (t : LatticePoint) :
    ConnectedGrading (translateGrading g t) ↔ ConnectedGrading g := by
  unfold ConnectedGrading
  rw [trace_translate]
  rfl

theorem surp_translate {P : TNEPath} (g : Grading P) (t : LatticePoint) :
    Surp (translate P t) (translateGrading g t) = Surp P g := by
  unfold Surp bBal
  rw [trace_translate]
  rfl

def restrictGrading {P : TNEPath} (g : Grading P)
    (i j : ℕ) (hj : j ≤ P.steps.length) : Grading (subpath P i j) :=
  fun e => g (edgeEquiv P (subpathEdge P i j hj ((edgeEquiv _).symm e)))

@[simp] theorem restrict_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) (i j : ℕ) (hj : j ≤ P.steps.length) :
    restrictGrading (ofBounded g) i j hj =
      ofBounded (KroneckerPaperPathGradings.restrictGrading g i j hj) := rfl

theorem restrictGrading_bBal {P : TNEPath} (g : Grading P)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ P.steps.length) (k : ℕ) (hk : k ≤ j-i) :
    bBal (restrictGrading g i j hj) ⟨k, by rw [subpath_length P hij hj]; omega⟩ =
      bBal g ⟨i+k, by omega⟩ - bBal g ⟨i, by omega⟩ :=
  KroneckerPaperPathGradings.restrictGrading_boundaryBalance (bounded g) i j hij hj k hk

def NERealGrading {P : TNEPath} (g : Grading P) (u v : Edge P) :
    Grading (NEReal P u v) := g ∘ cyclicAmbientEdge u v

@[simp] theorem NEReal_ofBounded {m : ℕ} {P : TNEPath}
    (g : KroneckerPaperPathGradings.Grading m P) (u v : Edge P) :
    NERealGrading (ofBounded g) u v =
      ofBounded (KroneckerPaperPathGradings.NERealGrading g u v) := rfl

theorem NEReal_grade {P : TNEPath} (g : Grading P) (u v : Edge P)
    (e : GeomEdge (NEReal P u v)) :
    NERealGrading g u v e = g (cyclicAmbientEdge u v e) := rfl

abbrev ColorFiber (m : ℕ) {P : TNEPath} (g : Grading P) :=
  (e : GeomEdge P) → {c : ℕ // 1 ≤ c ∧ c ≤ Nat.choose m (g e)}

abbrev ColoredGrading (m : ℕ) (P : TNEPath) := (g : Grading P) × ColorFiber m g

theorem color_grade_le {m : ℕ} {P : TNEPath} {g : Grading P}
    (c : ColorFiber m g) (e : GeomEdge P) : g e ≤ m := by
  by_contra hn
  have hz := Nat.choose_eq_zero_of_lt (show m < g e by omega)
  have h1 := (c e).property.1
  have h2 := (c e).property.2
  omega

theorem colorFiber_nonempty_iff {m : ℕ} {P : TNEPath} (g : Grading P) :
    Nonempty (ColorFiber m g) ↔ ∀ e, g e ≤ m := by
  constructor
  · rintro ⟨c⟩
    exact color_grade_le c
  · intro h
    exact ⟨fun e => ⟨1, le_rfl, Nat.choose_pos (h e)⟩⟩

def coloredGradingEquiv (m : ℕ) (P : TNEPath) :
    ColoredGrading m P ≃ KroneckerPaperPathGradings.ColoredGrading m P where
  toFun c := ⟨fun e => ⟨c.1 e, Nat.lt_succ_of_le (color_grade_le c.2 e)⟩, c.2⟩
  invFun c := ⟨ofBounded c.1, c.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

abbrev ConnectedColorings (m : ℕ) (P : TNEPath) (d : ℕ) :=
  {c : ColoredGrading m P // ConnectedGrading c.1 ∧ Surp P c.1 = (d : ℤ)}

def connectedCount (m : ℕ) (P : TNEPath) (d : ℕ) : ℕ :=
  Nat.card (ConnectedColorings m P d)

def connectedColoringEquiv (m : ℕ) (P : TNEPath) (d : ℕ) :
    ConnectedColorings m P d ≃ KroneckerPaperPathGradings.ConnectedColorings m P d :=
  (coloredGradingEquiv m P).subtypeEquiv (fun c =>
    (KroneckerPaperPathGradings.connectedGrade_iff_connected_surp
      ((coloredGradingEquiv m P) c).1 d).symm)

theorem connectedCount_eq_bounded (m : ℕ) (P : TNEPath) (d : ℕ) :
    connectedCount m P d = KroneckerPaperPathGradings.connectedCount m P d :=
  Nat.card_congr (connectedColoringEquiv m P d)

theorem connectedCount_translate (m : ℕ) (P : TNEPath) (d : ℕ) (t : LatticePoint) :
    connectedCount m (translate P t) d = connectedCount m P d := by
  rw [connectedCount_eq_bounded, connectedCount_eq_bounded]
  exact (KroneckerPaperPathGradings.connectedCount_translate m P t d).symm

def NERealColoredGrading {m : ℕ} {P : TNEPath} (c : ColoredGrading m P)
    (u v : Edge P) : ColoredGrading m (NEReal P u v) :=
  ⟨NERealGrading c.1 u v, fun e => c.2 (cyclicAmbientEdge u v e)⟩

theorem NEReal_color {m : ℕ} {P : TNEPath} (c : ColoredGrading m P)
    (u v : Edge P) (e : GeomEdge (NEReal P u v)) :
    ((NERealColoredGrading c u v).2 e).val = (c.2 (cyclicAmbientEdge u v e)).val := rfl

end KroneckerNaturalPathGradings
