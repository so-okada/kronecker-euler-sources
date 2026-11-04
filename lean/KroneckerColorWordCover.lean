import KroneckerGraphColorWords
import KroneckerWordParity

/- Original module: KroneckerWordTranslations -/
section
set_option autoImplicit false
namespace KroneckerWordTranslations
open KroneckerReducedColorWords KroneckerColorWordAction

def translate (g w : Word) : Word := act w.val g
def inverseWord (g : Word) : Word := normal g.val.reverse

theorem translate_root (g : Word) : translate g root = g := rfl

theorem root_translate (w : Word) : translate root w = w := normal_reduced w

theorem translate_toggle (g : Word) (c : Color) (w : Word) :
    translate g (toggle c w) = toggle c (translate g w) := act_toggle c w g

theorem translate_comp (h g w : Word) :
    translate h (translate g w) = translate (translate h g) w :=
  act_normalized w.val g h

theorem inverse_translate (g : Word) : translate (inverseWord g) g = root :=
  act_cancel_reverse g.val root

theorem translate_inverse (g : Word) : translate g (inverseWord g) = root := by
  change act (normal g.val.reverse).val g = root
  rw [act_normal]
  simpa only [show act g.val root = g from normal_reduced g] using act_reverse_cancel g.val root

def translation (g : Word) : Word ≃ Word where
  toFun := translate g
  invFun := translate (inverseWord g)
  left_inv w := by rw [translate_comp, inverse_translate, root_translate]
  right_inv w := by rw [translate_comp, translate_inverse, root_translate]

theorem translation_reaches (u v : Word) :
    ∃ g : Word, translate g u = v := by
  refine ⟨translate v (inverseWord u), ?_⟩
  rw [←translate_comp, inverse_translate, translate_root]

end KroneckerWordTranslations
end

/- Original module: KroneckerColorWordCover -/
section
set_option autoImplicit false
namespace KroneckerColorWordCover
open SimpleGraph KroneckerReducedColorWords KroneckerColorWordAction
open KroneckerWordTranslations KroneckerWordParity KroneckerGraphColorWords

def cover : SimpleGraph Word where
  Adj u v := ∃ c, toggle c u = v
  symm := by
    constructor
    rintro u v ⟨c,h⟩
    exact ⟨c, by rw [←h, toggle_involution]⟩
  loopless := by
    constructor
    rintro u ⟨c,h⟩
    exact toggle_ne c u h

noncomputable def coverColoring : EdgeColoring cover where
  color h := h.choose
  symm := by
    intro u v h
    apply toggle_color_injective v
    exact h.symm.choose_spec.trans ((toggle_involution h.choose u).symm.trans
      (congrArg (toggle h.choose) h.choose_spec))
  proper := by
    intro u v w h k hc
    exact h.choose_spec.symm.trans (hc ▸ k.choose_spec)

theorem cover_color_step {u v : Word} (h : cover.Adj u v) :
    toggle (coverColoring.color h) u = v := h.choose_spec

theorem cover_walk_action {u v : Word} (p : cover.Walk u v) :
    act (colors coverColoring p) v = u := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change toggle (coverColoring.color h) (act (colors coverColoring p) _) = _
    rw [ih]
    exact (congrArg (toggle (coverColoring.color h)) (cover_color_step h)).symm.trans
      (toggle_involution _ _)

theorem act_reachable (l : List Color) (w : Word) : cover.Reachable (act l w) w := by
  induction l with
  | nil => exact Reachable.refl _
  | cons c l ih =>
    exact (show cover.Adj (toggle c (act l w)) (act l w) from
      ⟨c, toggle_involution c (act l w)⟩).reachable.trans ih

theorem cover_connected : cover.Connected := by
  have : Nonempty Word := ⟨root⟩
  apply Connected.mk
  intro u v
  have hu : cover.Reachable u root := by
    simpa only [show act u.val root = u from normal_reduced u] using act_reachable u.val root
  have hv : cover.Reachable v root := by
    simpa only [show act v.val root = v from normal_reduced v] using act_reachable v.val root
  exact hu.trans hv.symm

theorem cover_tree : cover.IsTree := by
  refine ⟨cover_connected, isAcyclic_iff_subsingleton_path.mpr ?_⟩
  intro u v
  refine ⟨fun p q => ?_⟩
  apply Subtype.ext
  apply walk_eq_of_colors coverColoring
  let wp : Word := ⟨colors coverColoring p.val, path_colors_reduced coverColoring p.val p.property⟩
  let wq : Word := ⟨colors coverColoring q.val, path_colors_reduced coverColoring q.val q.property⟩
  have hp : translate v wp = u := cover_walk_action p.val
  have hq : translate v wq = u := cover_walk_action q.val
  exact congrArg Subtype.val ((translation v).injective (hp.trans hq.symm))

theorem cover_opposite_parity {u v : Word} (h : cover.Adj u v) : parity u ≠ parity v := by
  obtain ⟨c,rfl⟩ := h
  exact (toggle_opposite_parity c u).symm

end KroneckerColorWordCover
end
