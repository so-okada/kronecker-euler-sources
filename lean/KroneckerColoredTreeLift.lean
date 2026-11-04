import KroneckerColorWordCover

/- Original module: KroneckerTreeRootPaths -/
section
set_option autoImplicit false
namespace KroneckerTreeRootPaths
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

noncomputable def rootPath (hT : G.IsTree) (r v : V) : G.Walk v r :=
  (hT.existsUnique_path v r).choose

theorem rootPath_isPath (hT : G.IsTree) (r v : V) : (rootPath hT r v).IsPath :=
  (hT.existsUnique_path v r).choose_spec.1

theorem rootPath_unique (hT : G.IsTree) (r v : V) (p : G.Walk v r) (hp : p.IsPath) :
    p = rootPath hT r v := (hT.existsUnique_path v r).choose_spec.2 p hp


theorem adjacent_rootPaths (hT : G.IsTree) (r : V) {u v : V} (h : G.Adj u v) :
    rootPath hT r u = .cons h (rootPath hT r v) ∨
    rootPath hT r v = .cons h.symm (rootPath hT r u) := by
  classical
  by_cases hu : u ∈ (rootPath hT r v).support
  · right
    have ht : (rootPath hT r v).takeUntil u hu = .cons h.symm .nil :=
      (hT.existsUnique_path v u).unique ((rootPath_isPath hT r v).takeUntil hu)
        (Walk.IsPath.nil.cons (by simpa using h.ne.symm))
    have hd : (rootPath hT r v).dropUntil u hu = rootPath hT r u :=
      rootPath_unique hT r u _ ((rootPath_isPath hT r v).dropUntil hu)
    rw [←Walk.take_spec (rootPath hT r v) hu, ht, hd]
    rfl
  · left
    exact (rootPath_unique hT r u _ ((rootPath_isPath hT r v).cons hu)).symm

end KroneckerTreeRootPaths
end

/- Original module: KroneckerColoredTreeLift -/
section
set_option autoImplicit false
namespace KroneckerColoredTreeLift
open SimpleGraph KroneckerReducedColorWords KroneckerColorWordAction
open KroneckerGraphColorWords KroneckerTreeRootPaths KroneckerColorWordCover

variable {V : Type*} {G : SimpleGraph V} (C : EdgeColoring G) (hT : G.IsTree)

noncomputable def rootLift (r v : V) : Word :=
  ⟨colors C (rootPath hT r v), path_colors_reduced C _ (rootPath_isPath hT r v)⟩


theorem rootLift_step (r : V) {u v : V} (h : G.Adj u v) :
    rootLift C hT r u = toggle (C.color h) (rootLift C hT r v) := by
  have hn (x : V) : rootLift C hT r x = normal (colors C (rootPath hT r x)) :=
    (normal_reduced (rootLift C hT r x)).symm
  rcases adjacent_rootPaths hT r h with hp | hp
  · rw [hn u, hp]
    change toggle (C.color h) (normal (colors C (rootPath hT r v))) = _
    rw [←hn v]
  · have hv : rootLift C hT r v = toggle (C.color h) (rootLift C hT r u) := by
      rw [hn v, hp]
      change toggle (C.color h.symm) (normal (colors C (rootPath hT r u))) = _
      rw [C.symm h, ←hn u]
    exact ((congrArg (toggle (C.color h)) hv).trans (toggle_involution _ _)).symm

theorem rootLift_injective (r : V) : Function.Injective (rootLift C hT r) := by
  intro u v huv
  have hw : colors C (rootPath hT r u) = colors C (rootPath hT r v) :=
    congrArg Subtype.val huv
  apply endpoint_of_colors C (rootPath hT r u).reverse (rootPath hT r v).reverse
  rw [colors_reverse, colors_reverse, hw]

noncomputable def rootLiftHom (r : V) : G →g cover where
  toFun := rootLift C hT r
  map_rel' := by
    intro u v h
    exact ⟨C.color h, (congrArg (toggle (C.color h)) (rootLift_step C hT r h)).trans
      (toggle_involution _ _)⟩

theorem rootLift_color (r : V) {u v : V} (h : G.Adj u v) :
    coverColoring.color ((rootLiftHom C hT r).map_adj h) = C.color h := by
  apply toggle_color_injective (rootLift C hT r u)
  exact (cover_color_step ((rootLiftHom C hT r).map_adj h)).trans
    ((congrArg (toggle (C.color h)) (rootLift_step C hT r h)).trans
      (toggle_involution _ _)).symm

end KroneckerColoredTreeLift
end
