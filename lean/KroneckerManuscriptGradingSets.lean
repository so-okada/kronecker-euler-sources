import KroneckerNaturalPathGradings

/-! The grading and color sets in Definitions 2.4 and 2.9.
The set bounds use arbitrary nonnegative integer gradings. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths

abbrev G (U : TNEPath) := Grading U

def G_h (U : TNEPath) (h : ℕ) : Set (G U) := {g | ∀ e, g e ≤ h}

/-- Signed grade difference; subtraction takes place in the integers. -/
def Diff (U : TNEPath) (g h : G U) (e : GeomEdge U) : ℤ :=
  (g e : ℤ) - (h e : ℤ)

@[simp] theorem Diff_self (U : TNEPath) (g : G U) (e : GeomEdge U) :
    Diff U g g e = 0 := sub_self _

theorem Diff_nonneg_iff (U : TNEPath) (g h : G U) (e : GeomEdge U) :
    0 ≤ Diff U g h e ↔ h e ≤ g e := by
  unfold Diff
  omega

theorem Diff_zero_iff (U : TNEPath) (g h : G U) (e : GeomEdge U) :
    Diff U g h e = 0 ↔ g e = h e := by
  unfold Diff
  omega

theorem Diff_recovery (U : TNEPath) (g h : G U) (e : GeomEdge U) :
    (g e : ℤ) = (h e : ℤ) + Diff U g h e := by
  unfold Diff
  omega

theorem Diff_add (U : TNEPath) (g h k : G U) (e : GeomEdge U) :
    Diff U g k e = Diff U g h e + Diff U h k e := by
  unfold Diff
  omega

abbrev Col (U : TNEPath) (g : G U) (m : ℕ) := ColorFiber m g

def CtdG (U : TNEPath) : Set (G U) := {g | ConnectedGrading g}

def CtdG_h (U : TNEPath) (h : ℕ) : Set (G U) := CtdG U ∩ G_h U h

@[simp] theorem mem_G_h {U : TNEPath} {g : G U} {h : ℕ} :
    g ∈ G_h U h ↔ ∀ e, g e ≤ h := Iff.rfl

@[simp] theorem mem_CtdG {U : TNEPath} {g : G U} :
    g ∈ CtdG U ↔ ConnectedGrading g := Iff.rfl

@[simp] theorem mem_CtdG_h {U : TNEPath} {g : G U} {h : ℕ} :
    g ∈ CtdG_h U h ↔ ConnectedGrading g ∧ ∀ e, g e ≤ h := Iff.rfl

theorem Col_nonempty_iff {U : TNEPath} (g : G U) (m : ℕ) :
    Nonempty (Col U g m) ↔ g ∈ G_h U m :=
  colorFiber_nonempty_iff g

theorem mem_CtdG_h_of_color {U : TNEPath} {g : G U} {m : ℕ}
    (hg : g ∈ CtdG U) (c : Col U g m) : g ∈ CtdG_h U m :=
  ⟨hg, color_grade_le c⟩

theorem connectedColorings_spec {m d : ℕ} {U : TNEPath}
    (c : ColoredGrading m U) :
    (ConnectedGrading c.1 ∧ Surp U c.1 = (d : ℤ)) ↔
      c.1 ∈ CtdG_h U m ∧ Surp U c.1 = (d : ℤ) := by
  constructor
  · rintro ⟨hc, hd⟩
    exact ⟨mem_CtdG_h_of_color hc c.2, hd⟩
  · rintro ⟨⟨hc, _⟩, hd⟩
    exact ⟨hc, hd⟩

end KroneckerNaturalPathGradings

