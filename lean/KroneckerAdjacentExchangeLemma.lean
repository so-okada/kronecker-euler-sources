import KroneckerGeometricExchange
import KroneckerNaturalPathGradings
import KroneckerRecolShell
import KroneckerRecolConcatenation
import KroneckerExchangeRecolor

/-! Lemmas 9.8 and 9.10: adjacent exchange on natural-valued geometric colored gradings.
The statement concerns connectedness, surplus, ordered grade--color pairs,
and recovery. No complete h-precursor identity is asserted. -/
set_option autoImplicit false
noncomputable section

namespace KroneckerAdjacentExchangeLemma
open KroneckerPaperPaths KroneckerNaturalPathGradings KroneckerColoring
open KroneckerWrappedExchangeWitness KroneckerWrappedExchangeMap
open KroneckerExchangeColorOrder KroneckerEdgeShell KroneckerColoredEdgeDictionary

abbrev ColoredSet (P : TNEPath) := (d : ℕ) × ConnectedColorings 3 P d

def operational (P : TNEPath) :
    ColoredSet P ≃ KroneckerProgramExecution.SurplusColorings 3 P.steps :=
  (Equiv.sigmaCongrRight (fun d => connectedColoringEquiv 3 P d)).trans
    (KroneckerPaperPathGradings.operationalSurplusEquiv 3 P)

def spec (right : Bool) (P Q : List Bool) (u v : ℕ)
    (hu : 1 ≤ u ∧ u ≤ 2) (hv : 1 ≤ v ∧ v ≤ 2) : ExchangeSpec 3 :=
  ⟨right, P, Q, u, v, by omega, by omega, by decide, hv.1⟩

def source (s : ExchangeSpec 3) (o : LatticePoint) : TNEPath := ofSteps s.source o
def target (s : ExchangeSpec 3) : TNEPath := ofSteps s.target 0

def exchange (s : ExchangeSpec 3) (o : LatticePoint)
    (a : ColoredSet (source s o)) : ColoredSet (target s) :=
  (operational (target s)).symm (exchangeMap s (operational (source s o) a))

abbrev GradeColor := (h : ℕ) × {c : ℕ // 1 ≤ c ∧ c ≤ Nat.choose 3 h}

def gradeColor (p : Palette 3) : GradeColor :=
  ⟨p.1.val, ⟨p.2.val + 1, by omega, by have := p.2.isLt; omega⟩⟩

theorem gradeColor_injective : Function.Injective gradeColor := by
  intro p q he
  have hg := congrArg (fun z : GradeColor => z.1) he
  have hc := congrArg (fun z : GradeColor => z.2.val) he
  rcases p with ⟨p, c⟩
  rcases q with ⟨q, d⟩
  have hp : p = q := Fin.ext hg
  subst q
  have hd : c = d := Fin.ext (by simpa [gradeColor] using hc)
  subst d
  rfl

theorem gradeColor_bound (p : Palette 3) : (gradeColor p).1 ≤ 3 := by
  have := p.1.isLt
  exact Nat.le_of_lt_succ this

def code (s : ExchangeSpec 3) (o : LatticePoint) (a : ColoredSet (source s o)) :
    GradeColor := gradeColor (exchangeCode s (operational (source s o) a))

def edges {P : TNEPath} (a : ColoredGrading 3 P) :
    List (KroneckerColoredEdges.CEdge 3) :=
  KroneckerPaperPathGradings.coloredEdges (coloredGradingEquiv 3 P a)

def horizontalData (es : List (KroneckerColoredEdges.CEdge 3)) : List GradeColor :=
  (horizontalColors es).map gradeColor
def verticalData (es : List (KroneckerColoredEdges.CEdge 3)) : List GradeColor :=
  (verticalColors es).map gradeColor

theorem geometric_pair {P : TNEPath} (a : ColoredGrading 3 P) (k : Edge P) :
    gradeColor (KroneckerPaperPathGradings.paletteEncoding
      (coloredGradingEquiv 3 P a) k) = ⟨a.1 (edgeEquiv P k), a.2 (edgeEquiv P k)⟩ := by
  obtain ⟨c, rfl⟩ := KroneckerRecolConcatenation.fromPalette_surjective 3 P a
  have hp : KroneckerPaperPathGradings.paletteEncoding
      (coloredGradingEquiv 3 P (KroneckerManuscriptRecolorMaps.fromPalette P c)) = c := by
    simp only [KroneckerPaperPathGradings.paletteEncoding,
      KroneckerManuscriptRecolorMaps.fromPalette, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply]
  rw [hp]
  change gradeColor (c k) = gradeColor (c ((edgeEquiv P).symm (edgeEquiv P k)))
  rw [Equiv.symm_apply_apply]

theorem edges_fromPalette (P : TNEPath) (c : Coloring 3 P.steps.length) :
    edges (KroneckerManuscriptRecolorMaps.fromPalette P c) = ofColoring P.steps c := by
  simp only [edges, KroneckerPaperPathGradings.coloredEdges,
    KroneckerPaperPathGradings.paletteEncoding, KroneckerManuscriptRecolorMaps.fromPalette,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]

def shell {P : TNEPath} (s : ExchangeSpec 3) (a : ColoredGrading 3 P) :
    ColoredGrading 3 (KroneckerManuscriptShell.path P s.u s.v) :=
  KroneckerManuscriptShell.coloring P a.1 a.2 s.u s.v 1 0 s.hu s.hv s.hm

theorem shell_edges {P : TNEPath} (s : ExchangeSpec 3) (a : ColoredGrading 3 P) :
    edges (shell s a) = edgeShell s.u s.v s.hu s.hv s.hm (edges a) := by
  obtain ⟨c, rfl⟩ := KroneckerRecolConcatenation.fromPalette_surjective 3 P a
  unfold shell
  rw [KroneckerRecolShell.explicit_shell_eq P s.u s.v 1 0 s.hu s.hv s.hm s.hpos c,
    edges_fromPalette, edges_fromPalette]
  have hs := edgeShell_shape s.u s.v s.hu s.hv s.hm s.hpos (ofColoring P.steps c)
  rw [ofColoring_shape] at hs
  have hc : (edgeShell s.u s.v s.hu s.hv s.hm (ofColoring P.steps c)).map Prod.snd =
      KroneckerColoredShell.prefixColors 3 s.u s.hu ++
      (List.ofFn c ++ KroneckerRecolShell.tailColors 3 s.v 2 s.hv s.hm) := by
    simp [edgeShell, edgePrefix, edgeSuffix, ofColoring_colors,
      KroneckerColoredShell.prefixColors, KroneckerRecolShell.tailColors]
  conv_rhs => rw [← List.zip_unzip (edgeShell s.u s.v s.hu s.hv s.hm (ofColoring P.steps c))]
  simp only [List.unzip_fst, List.unzip_snd]
  rw [show (edgeShell s.u s.v s.hu s.hv s.hm (ofColoring P.steps c)).map Prod.fst =
    KroneckerColoredShell.shellPath s.u s.v P.steps from hs, hc]
  unfold ofColoring KroneckerRecolShell.shellPalette
  rw [KroneckerColoredShell.fromList_colors]
  rfl

@[simp] theorem exchange_core (s : ExchangeSpec 3) (o : LatticePoint)
    (a : ColoredSet (source s o)) :
    operational (target s) (exchange s o a) = exchangeMap s (operational (source s o) a) :=
  (operational (target s)).apply_symm_apply _

theorem exchange_surplus (s : ExchangeSpec 3) (o : LatticePoint)
    (a : ColoredSet (source s o)) :
    a.1 ≤ (exchange s o a).1 ∧ (exchange s o a).1 ≤ a.1 + 3 :=
  exchangeMap_surplus s (operational (source s o) a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem exchange_recovery (s : ExchangeSpec 3) (o : LatticePoint) :
    Function.Injective (fun a : ColoredSet (source s o) => (exchange s o a, code s o a)) := by
  intro a b he
  apply (operational (source s o)).injective
  apply KroneckerWrappedExchangeRecovery.exchange_target_code_injective s
  refine Prod.ext ?_ ?_
  · simpa only [exchange_core] using congrArg (operational (target s)) (Prod.mk.inj he).1
  · exact gradeColor_injective (Prod.mk.inj he).2

theorem oneChange_map {α β : Type} (f : α → β) {xs ys : List α}
    (h : OneChange xs ys) : OneChange (xs.map f) (ys.map f) := by
  induction h with
  | here p q xs => exact .here (f p) (f q) (xs.map f)
  | there p h ih => exact .there (f p) ih

theorem oneChange_count {α : Type} [DecidableEq α] {xs ys : List α}
    (h : OneChange xs ys) :
    ((xs.zip ys).filter (fun p => p.1 != p.2)).length ≤ 1 := by
  induction h with
  | here p q xs =>
    have hz : ((xs.zip xs).filter (fun z => z.1 != z.2)).length = 0 := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simpa using ih
    simp only [List.zip_cons_cons, List.filter_cons]
    split <;> simp only [List.length_cons, hz] <;> omega
  | there p h ih => simpa using ih

theorem exchange_colors (s : ExchangeSpec 3) (o : LatticePoint)
    (a : ColoredSet (source s o)) :
    horizontalData (edges (exchange s o a).2.val) =
      horizontalData (edgeShell s.u s.v s.hu s.hv s.hm (edges a.2.val)) ∧
    ((verticalData (edgeShell s.u s.v s.hu s.hv s.hm (edges a.2.val))).zip
      (verticalData (edges (exchange s o a).2.val)) |>.filter
        (fun p => p.1 != p.2)).length ≤ 1 := by
  classical
  have hh := KroneckerWrappedExchangeColors.exchangeMap_horizontal_colors s
    (operational (source s o) a)
  have hv := KroneckerWrappedExchangeColors.exchangeMap_vertical_colors s
    (operational (source s o) a)
  rw [← exchange_core] at hh hv
  exact ⟨congrArg (List.map gradeColor) hh, oneChange_count (oneChange_map gradeColor hv)⟩

theorem exchange_recol (s : ExchangeSpec 3) (o : LatticePoint)
    (a : ColoredSet (source s o)) :
    List.Forall₂ RespectsRecol
      (verticalColors (edgeShell s.u s.v s.hu s.hv s.hm (edges a.2.val)))
      (verticalColors (edges (exchange s o a).2.val)) := by
  have h := KroneckerExchangeRecolor.exchangeMap_vertical s (operational (source s o) a)
  rw [← exchange_core] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem exchange_fiber (s : ExchangeSpec 3) (o : LatticePoint) (b : ColoredSet (target s)) :
    Nat.card {a // exchange s o a = b} ≤ 8 := by
  let e : {a // exchange s o a = b} ≃
      {a // exchangeMap s a = operational (target s) b} :=
    { toFun := fun a => ⟨operational (source s o) a.val, by
        rw [← exchange_core, a.property]⟩
      invFun := fun a => ⟨(operational (source s o)).symm a.val, by
        apply (operational (target s)).injective
        rw [exchange_core, Equiv.apply_symm_apply, a.property]⟩
      left_inv := fun a => Subtype.ext ((operational (source s o)).symm_apply_apply a.val)
      right_inv := fun a => Subtype.ext ((operational (source s o)).apply_symm_apply a.val) }
  rw [Nat.card_congr e]
  exact KroneckerWrappedExchangeFiber.three_arrow_fiber s _

/-- The colored adjacent-exchange construction used in Lemmas 9.8 and 9.10. -/
theorem adjacent_exchange (s : ExchangeSpec 3) (o : LatticePoint) :
    ∃ Ψ : ColoredSet (source s o) → ColoredSet (target s),
    ∃ κ : ColoredSet (source s o) → GradeColor,
      Function.Injective (fun a => (Ψ a, κ a)) ∧
      ∀ a, (κ a).1 ≤ 3 ∧ (a.1 ≤ (Ψ a).1 ∧ (Ψ a).1 ≤ a.1 + 3) ∧
        horizontalData (edges (Ψ a).2.val) =
          horizontalData (edges (shell s a.2.val)) ∧
        ((verticalData (edges (shell s a.2.val))).zip
          (verticalData (edges (Ψ a).2.val)) |>.filter
            (fun p => p.1 != p.2)).length ≤ 1 := by
  classical
  exact ⟨exchange s o, code s o, exchange_recovery s o,
    fun a => ⟨gradeColor_bound _, exchange_surplus s o a,
      by simpa only [shell_edges] using exchange_colors s o a⟩⟩

end KroneckerAdjacentExchangeLemma
