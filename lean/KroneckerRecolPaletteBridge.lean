import KroneckerRecolorConstructions

/-! Pointwise palette criteria for the manuscript's Recol operator. -/
set_option autoImplicit false
noncomputable section
namespace KroneckerRecolPaletteBridge
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerManuscriptRecolorMaps
open KroneckerColoring

theorem fromPalette_recol {m : ℕ} {U V : TNEPath} {S : Set (Edge U)}
    (f : S ↪ Edge V) (c : Coloring m U.steps.length) (d : Coloring m V.steps.length)
    (hc : ∀ k : S, RespectsRecol (c k.val) (d (f k)))
    (hn : ∀ k : Edge V, k ∉ Set.range f → (d k).2.val = 0) :
    (⟨(fromPalette V d).1,
      Recol U V (partialEdgeCopy f) (fromPalette V d).1
        (color_grade_le (fromPalette V d).2) (fromPalette U c).1 (fromPalette U c).2⟩ :
        ColoredGrading m V) = fromPalette V d := by
  apply congrArg (fun δ => (⟨(fromPalette V d).1, δ⟩ : ColoredGrading m V))
  apply Recol_unique
  · intro x hx
    let k : S := ⟨(edgeEquiv U).symm x.val, x.property⟩
    have hx' : grade (d (f k)) = grade (c k.val) := by
      change grade (d ((edgeEquiv V).symm (edgeEquiv V (f k)))) = grade (c k.val) at hx
      simpa only [Equiv.symm_apply_apply] using hx
    change (d ((edgeEquiv V).symm (edgeEquiv V (f k)))).2.val + 1 = (c k.val).2.val + 1
    exact (congrArg (fun p : Palette m => p.2.val + 1)
      (congrArg d ((edgeEquiv V).symm_apply_apply (f k)))).trans
        (congrArg (fun p : Palette m => p.2.val + 1) ((hc k).1 hx'))
  · intro e he
    let k := (edgeEquiv V).symm e
    have hk : edgeEquiv V k = e := (edgeEquiv V).apply_symm_apply e
    change ((fromPalette V d).2 e).val = 1
    rw [← hk, fromPalette_color]
    by_cases hr : k ∈ Set.range f
    · obtain ⟨x, hx⟩ := hr
      have hg : grade (d (f x)) ≠ grade (c x.val) := by
        intro hg
        apply he
        refine ⟨⟨edgeEquiv U x.val, by
          change (edgeEquiv U).symm (edgeEquiv U x.val) ∈ S
          rw [Equiv.symm_apply_apply]
          exact x.property⟩, ?_, ?_⟩
        · change edgeEquiv V (f ⟨(edgeEquiv U).symm (edgeEquiv U x.val), _⟩) = e
          simpa only [Equiv.symm_apply_apply,hx] using hk
        · simpa only [← hk, ← hx, fromPalette_grade] using hg
      rw [← hx, (hc x).2 hg]
    · rw [hn k hr]

theorem fromPalette_recol_total {m : ℕ} {U V : TNEPath}
    (f : Edge U ↪ Edge V) (c : Coloring m U.steps.length) (d : Coloring m V.steps.length)
    (hc : ∀ k, RespectsRecol (c k) (d (f k)))
    (hn : ∀ k, k ∉ Set.range f → (d k).2.val = 0) :
    (⟨(fromPalette V d).1,
      Recol U V (edgeCopy f) (fromPalette V d).1
        (color_grade_le (fromPalette V d).2) (fromPalette U c).1 (fromPalette U c).2⟩ :
        ColoredGrading m V) = fromPalette V d := by
  let f' : (Set.univ : Set (Edge U)) ↪ Edge V :=
    ⟨fun k => f k.val, fun a b h => Subtype.ext (f.injective h)⟩
  have h := fromPalette_recol f' c d (fun k => hc k.val) (by
    intro k hk
    apply hn k
    rintro ⟨x, hx⟩
    exact hk ⟨⟨x, Set.mem_univ _⟩, hx⟩)
  have he : partialEdgeCopy f' = edgeCopy f := by
    apply Function.Embedding.ext
    intro x
    rfl
  rw [he] at h
  exact h

end KroneckerRecolPaletteBridge
