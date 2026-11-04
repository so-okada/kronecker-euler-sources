import KroneckerGeometricRunEdits
import KroneckerWrappedExchangeAssembly

set_option autoImplicit false

namespace KroneckerPaperPathGradings
noncomputable section
open KroneckerPaperPaths KroneckerBinaryExchangeShapes KroneckerBinaryExchangeMap
open KroneckerExchangeColorOrder KroneckerColoredEdgeDictionary KroneckerEdgeShell

abbrev SurplusGradings (m : ℕ) (P : TNEPath) := (d : ℕ) × ConnectedColorings m P d

def operationalConnectedEquiv (m : ℕ) (P : TNEPath) (d : ℕ) :
    ConnectedColorings m P d ≃ KroneckerWordCounts.ConnectedColorings m P.steps d :=
  (connectedColoringEquiv m P d).trans
    (KroneckerPaperColors.operationalColoringEquiv (KroneckerWordCounts.pathShape P.steps) d)

def operationalSurplusEquiv (m : ℕ) (P : TNEPath) :
    SurplusGradings m P ≃ KroneckerProgramExecution.SurplusColorings m P.steps :=
  Equiv.sigmaCongrRight (fun d => operationalConnectedEquiv m P d)

def paletteEncoding {m : ℕ} {P : TNEPath} (c : ColoredGrading m P) :
    KroneckerColoring.Coloring m P.steps.length :=
  (KroneckerPaperColors.coloringEquiv m P.steps.length).symm (coloredGradingEquiv m P c)

theorem paletteEncoding_grade {m : ℕ} {P : TNEPath} (c : ColoredGrading m P)
    (k : Edge P) : (paletteEncoding c k).1 = c.1 (edgeEquiv P k) := rfl

theorem paletteEncoding_color {m : ℕ} {P : TNEPath} (c : ColoredGrading m P)
    (k : Edge P) : (paletteEncoding c k).2.val + 1 = (c.2 (edgeEquiv P k)).val := by
  change (c.2 (edgeEquiv P k)).val - 1 + 1 = _
  exact Nat.sub_add_cancel (c.2 (edgeEquiv P k)).property.1

def coloredEdges {m : ℕ} {P : TNEPath} (c : ColoredGrading m P) :
    List (KroneckerColoredEdges.CEdge m) := ofColoring P.steps (paletteEncoding c)

@[simp] theorem operationalConnectedEquiv_colors {m : ℕ} {P : TNEPath} {d : ℕ}
    (c : ConnectedColorings m P d) :
    (operationalConnectedEquiv m P d c).val = paletteEncoding c.val := rfl

@[simp] theorem operationalSurplusEquiv_surplus {m : ℕ} {P : TNEPath}
    (c : SurplusGradings m P) : (operationalSurplusEquiv m P c).1 = c.1 := rfl

@[simp] theorem operationalSurplusEquiv_symm_surplus {m : ℕ} {P : TNEPath}
    (c : KroneckerProgramExecution.SurplusColorings m P.steps) :
    ((operationalSurplusEquiv m P).symm c).1 = c.1 := rfl

@[simp] theorem operationalSurplusEquiv_colors {m : ℕ} {P : TNEPath}
    (c : SurplusGradings m P) :
    (operationalSurplusEquiv m P c).2.val = paletteEncoding c.2.val := rfl

def wrappedExchange (right : Bool) (A B : List ℕ) (u v : ℕ)
    (hu : 1 ≤ u ∧ u ≤ 2) (hv : 1 ≤ v ∧ v ≤ 2) (o : LatticePoint)
    (c : SurplusGradings 3 (runPath (A ++ pairRuns right ++ B) o)) :
    SurplusGradings 3 (runPath (u :: (A ++ pairRuns (!right) ++ B) ++ [v]) 0) :=
  (operationalSurplusEquiv 3 _).symm
    (binaryExchange right A B u v hu hv (operationalSurplusEquiv 3 _ c))

theorem wrappedExchange_target (right : Bool) (A B : List ℕ) (u v : ℕ)
    (hu : 0 < u) (hv : 0 < v) :
    runPath (u :: (A ++ pairRuns (!right) ++ B) ++ [v]) 0 =
      concat (simpleRun u hu) (concat
        (exchangeRuns (runPath (A ++ pairRuns right ++ B) 0) A.length)
        (simpleRun v hv)) := by
  cases right <;> simp only [pairRuns, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, exchangeRuns_adjacent]
  all_goals simp only [← runPath_singleton u hu, ← runPath_singleton v hv,
    ← runPath_append, List.cons_append, List.nil_append]

@[simp] theorem wrappedExchange_core (right : Bool) (A B : List ℕ) (u v : ℕ)
    (hu : 1 ≤ u ∧ u ≤ 2) (hv : 1 ≤ v ∧ v ≤ 2) (o : LatticePoint)
    (c : SurplusGradings 3 (runPath (A ++ pairRuns right ++ B) o)) :
    operationalSurplusEquiv 3 _ (wrappedExchange right A B u v hu hv o c) =
      binaryExchange right A B u v hu hv (operationalSurplusEquiv 3 _ c) :=
  (operationalSurplusEquiv 3 _).apply_symm_apply _

theorem wrappedExchange_surplus (right : Bool) (A B : List ℕ) (u v : ℕ)
    (hu : 1 ≤ u ∧ u ≤ 2) (hv : 1 ≤ v ∧ v ≤ 2) (o : LatticePoint)
    (c : SurplusGradings 3 (runPath (A ++ pairRuns right ++ B) o)) :
    c.1 ≤ (wrappedExchange right A B u v hu hv o c).1 ∧
      (wrappedExchange right A B u v hu hv o c).1 ≤ c.1 + 3 :=
  binary_exchange_surplus right A B u v hu hv (operationalSurplusEquiv 3 _ c)

set_option backward.isDefEq.respectTransparency false in
def wrappedExchangeFiberEquiv (right : Bool) (A B : List ℕ) (u v : ℕ)
    (hu : 1 ≤ u ∧ u ≤ 2) (hv : 1 ≤ v ∧ v ≤ 2) (o : LatticePoint)
    (b : SurplusGradings 3 (runPath (u :: (A ++ pairRuns (!right) ++ B) ++ [v]) 0)) :
    {c // wrappedExchange right A B u v hu hv o c = b} ≃
      {c // binaryExchange right A B u v hu hv c = operationalSurplusEquiv 3 _ b} where
  toFun c := ⟨operationalSurplusEquiv 3 _ c.val, by
    rw [← wrappedExchange_core, c.property]⟩
  invFun c := ⟨(operationalSurplusEquiv 3 _).symm c.val, by
    apply (operationalSurplusEquiv 3 _).injective
    rw [wrappedExchange_core, Equiv.apply_symm_apply, c.property]⟩
  left_inv c := by apply Subtype.ext; exact (operationalSurplusEquiv 3 _).symm_apply_apply _
  right_inv c := by apply Subtype.ext; exact (operationalSurplusEquiv 3 _).apply_symm_apply _

theorem wrappedExchange_fiber (right : Bool) (A B : List ℕ) (u v : ℕ)
    (hu : 1 ≤ u ∧ u ≤ 2) (hv : 1 ≤ v ∧ v ≤ 2) (o : LatticePoint)
    (b : SurplusGradings 3 (runPath (u :: (A ++ pairRuns (!right) ++ B) ++ [v]) 0)) :
    Nat.card {c // wrappedExchange right A B u v hu hv o c = b} ≤ 8 := by
  rw [Nat.card_congr (wrappedExchangeFiberEquiv right A B u v hu hv o b)]
  exact KroneckerBinaryExchangeBound.binary_exchange_fiber right A B u v hu hv _

theorem wrappedExchange_colors (right : Bool) (A B : List ℕ) (u v : ℕ)
    (hu : 1 ≤ u ∧ u ≤ 2) (hv : 1 ≤ v ∧ v ≤ 2) (o : LatticePoint)
    (c : SurplusGradings 3 (runPath (A ++ pairRuns right ++ B) o)) :
    horizontalColors (coloredEdges (wrappedExchange right A B u v hu hv o c).2.val) =
      horizontalColors (edgeShell u v (by omega) (by omega) (by decide) (coloredEdges c.2.val)) ∧
    OneChange (verticalColors (edgeShell u v (by omega) (by omega) (by decide) (coloredEdges c.2.val)))
      (verticalColors (coloredEdges (wrappedExchange right A B u v hu hv o c).2.val)) := by
  have hh := KroneckerBinaryExchangeColors.binary_horizontal_colors right A B u v hu hv
    (operationalSurplusEquiv 3 _ c)
  have hvv := KroneckerBinaryExchangeColors.binary_vertical_colors right A B u v hu hv
    (operationalSurplusEquiv 3 _ c)
  rw [← wrappedExchange_core] at hh hvv
  exact ⟨hh, hvv⟩

end
end KroneckerPaperPathGradings
