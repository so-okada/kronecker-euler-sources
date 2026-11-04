import KroneckerManuscriptGradingSets

/-! Definition 3.2: recoloring along a partial injection of geometric edges.
The color set is one-based, as in the manuscript. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerNaturalPathGradings
open KroneckerPaperPaths
attribute [local instance] Classical.propDecidable

variable {m : ℕ} {U V : TNEPath} {S : Set (GeomEdge U)}

def Recol (U V : TNEPath) {S : Set (GeomEdge U)} (ι : S ↪ GeomEdge V)
    (h : G V) (hh : h ∈ G_h V m) (g : G U) (γ : Col U g m) : Col V h m := fun e =>
  if he : ∃ x : S, ι x = e ∧ h e = g x.val then
    ⟨(γ (Classical.choose he).val).val, by
      have hc := (γ (Classical.choose he).val).property
      exact ⟨hc.1, hc.2.trans_eq
        (congrArg (Nat.choose m) (Classical.choose_spec he).2.symm)⟩⟩
  else ⟨1, le_rfl, Nat.choose_pos (hh e)⟩

theorem Recol_preserved (ι : S ↪ GeomEdge V) (h : G V)
    (hh : h ∈ G_h V m) (g : G U) (γ : Col U g m)
    (x : S) (hx : h (ι x) = g x.val) :
    ((Recol U V ι h hh g γ) (ι x)).val = (γ x.val).val := by
  have he : ∃ y : S, ι y = ι x ∧ h (ι x) = g y.val := ⟨x, rfl, hx⟩
  have hy : Classical.choose he = x := ι.injective (Classical.choose_spec he).1
  simp only [Recol, dite_eq_left he]
  exact congrArg (fun y : S => (γ y.val).val) hy

theorem Recol_default (ι : S ↪ GeomEdge V) (h : G V)
    (hh : h ∈ G_h V m) (g : G U) (γ : Col U g m)
    (e : GeomEdge V) (he : ¬ ∃ x : S, ι x = e ∧ h e = g x.val) :
    ((Recol U V ι h hh g γ) e).val = 1 := by
  simp only [Recol, dite_eq_right he]

theorem Recol_changed (ι : S ↪ GeomEdge V) (h : G V)
    (hh : h ∈ G_h V m) (g : G U) (γ : Col U g m)
    (x : S) (hx : h (ι x) ≠ g x.val) :
    ((Recol U V ι h hh g γ) (ι x)).val = 1 := by
  apply Recol_default
  rintro ⟨y, hy, hg⟩
  have : y = x := ι.injective hy
  subst y
  exact hx hg

theorem Recol_new (ι : S ↪ GeomEdge V) (h : G V)
    (hh : h ∈ G_h V m) (g : G U) (γ : Col U g m)
    (e : GeomEdge V) (he : e ∉ Set.range ι) :
    ((Recol U V ι h hh g γ) e).val = 1 :=
  Recol_default ι h hh g γ e (fun ⟨x, hx, _⟩ => he ⟨x, hx⟩)

theorem Recol_unique (ι : S ↪ GeomEdge V) (h : G V)
    (hh : h ∈ G_h V m) (g : G U) (γ : Col U g m) (δ : Col V h m)
    (hcopy : ∀ x : S, h (ι x) = g x.val → (δ (ι x)).val = (γ x.val).val)
    (hdefault : ∀ e, (¬ ∃ x : S, ι x = e ∧ h e = g x.val) → (δ e).val = 1) :
    Recol U V ι h hh g γ = δ := by
  funext e
  apply Subtype.ext
  by_cases he : ∃ x : S, ι x = e ∧ h e = g x.val
  · obtain ⟨x, rfl, hx⟩ := he
    exact (Recol_preserved ι h hh g γ x hx).trans (hcopy x hx).symm
  · exact (Recol_default ι h hh g γ e he).trans (hdefault e he).symm

end KroneckerNaturalPathGradings
